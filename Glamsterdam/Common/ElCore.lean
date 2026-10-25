/-
Copyright (c) 2026 Verity Labs / LFG Labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Marchand, Verity Audit Team
-/
import Glamsterdam.Common.MetaSpec

/-!
# Glamsterdam Common Execution Layer Core (`ElCore`)

Formal specification and validated state-tracker / gas-meter model pinned against
`ethereum/execution-specs` @ `16898000911c1e3caa57be08509536c10ae92d3e`:
- `src/ethereum/forks/amsterdam/state_tracker.py` (`Account`, `BlockState`, `TransactionState`,
  `get_pre_state_account_optional`, `get_pre_state_account`, `get_account_optional`,
  `get_account`, `get_code`, `get_storage`, `get_storage_original`, `get_transient_storage`,
  `account_exists`, `account_deployable`, `account_exists_and_is_empty`, `is_account_alive`,
  `set_account`, `set_storage`, `destroy_account`, `clear_account_preserving_balance`,
  `destroy_storage`, `mark_account_created`, `set_transient_storage`, `modify_state`,
  `move_ether`, `create_ether`, `set_account_balance`, `increment_nonce`, `set_code`,
  `copy_tx_state`, `restore_tx_state`, `incorporate_tx_into_block`).
- `src/ethereum/forks/amsterdam/vm/gas.py` (`GasMeter`, `check_gas`, `charge_gas_from_meter`,
  `charge_state_gas_from_meter`, `commit_state_gas`, `restore_state_gas`,
  `restore_state_gas_to_entry`, `tx_state_gas_used`, `credit_state_gas_refund`,
  `repay_state_gas_spill`, `forfeit_remaining_gas`, `withhold_create_gas`,
  `drain_state_gas_reservoir`, `restore_child_gas`, `max_message_call_gas`,
  `calculate_message_call_gas`, `init_code_cost`, `allocate_evm_gas`,
  `settle_transaction_gas`, `check_block_gas_capacity`).
- `src/ethereum/forks/amsterdam/vm/__init__.py` (`incorporate_child`).

Abstraction conventions (documented in `audit/source-map.yaml` via `mapping_kind: exact | projection`):
- Addresses, storage keys, storage values, and 32-byte code hashes are modeled in `Nat`, with
  `EMPTY_CODE_HASH = 0` as the abstract sentinel for `keccak256(b"")`.
- Pure value-lookup projections (`get_pre_state_account_optional`, `get_account_optional`,
  `get_storage`, `account_exists`, `is_account_alive`) are paired with explicit stateful
  read-tracking transitions (`read_account_tx`, `read_storage_tx`).
-/

namespace Glamsterdam.Common.ElCore

open Glamsterdam.Common.Prelude
open Glamsterdam.Common.MetaSpec

/-! ## 1. Core Execution Layer Identifiers and Account Model (`ethereum/state.py`) -/

/-- 20-byte Ethereum account address modeled as `Nat`. -/
abbrev Address := Nat

/-- 32-byte storage slot key modeled as `Nat`. -/
abbrev StorageKey := Nat

/-- 32-byte storage value (`U256`) modeled as `Nat`. -/
abbrev StorageVal := Nat

/-- 32-byte Keccak-256 hash (`Hash32`) modeled as `Nat`. -/
abbrev Hash32 := Nat

/-- Sentinel hash representing `keccak256(b"")` (`EMPTY_CODE_HASH = 0`). -/
def EMPTY_CODE_HASH : Hash32 := 0

/-- Account state in the execution trie (`ethereum/state.py`).
We retain `codeEmpty` and `storageNonEmpty` helpers alongside `codeHash` for backwards
compatibility with algebraic projections while matching `execution-specs` `Account(nonce, balance, code_hash)`. -/
structure Account where
  nonce : Nat := 0
  balance : Nat := 0
  codeHash : Hash32 := EMPTY_CODE_HASH
  codeEmpty : Bool := true
  storageNonEmpty : Bool := false
  deriving Repr, DecidableEq, BEq

/-- The canonical `EMPTY_ACCOUNT = Account(nonce=0, balance=0, code_hash=EMPTY_CODE_HASH)`. -/
def EMPTY_ACCOUNT : Account :=
  { nonce := 0, balance := 0, codeHash := EMPTY_CODE_HASH, codeEmpty := true, storageNonEmpty := false }

/-- Whether an `Account` equals `EMPTY_ACCOUNT` (`nonce == 0 && balance == 0 && codeHash == EMPTY_CODE_HASH`,
matching `state_tracker.py:397-400` `account.nonce == Uint(0) and account.code_hash == EMPTY_CODE_HASH and account.balance == 0`). -/
@[inline, simp]
def Account.isEmpty (acc : Account) : Bool :=
  acc.nonce == 0 && acc.balance == 0 && acc.codeHash == EMPTY_CODE_HASH

/-! ## 2. BlockState and TransactionState (`state_tracker.py:44-101`) -/

/-- Read-only pre-block state (`PreState` in `ethereum/state.py`). -/
structure PreState where
  accounts : List (Address × Account) := []
  storage : List ((Address × StorageKey) × StorageVal) := []
  codes : List (Hash32 × Nat) := []
  deriving Repr, DecidableEq, BEq

/-- Look up an optional account in `PreState`. -/
@[simp]
def PreState.getAccountOptional (pre : PreState) (addr : Address) : Option Account :=
  match pre.accounts.find? (fun p => p.1 == addr) with
  | some (_, acc) => some acc
  | none => none

/-- Look up a storage value in `PreState` (default `0`). -/
@[simp]
def PreState.getStorage (pre : PreState) (addr : Address) (key : StorageKey) : StorageVal :=
  match pre.storage.find? (fun p => p.1 == (addr, key)) with
  | some (_, v) => v
  | none => 0

/-- Block-scoped state tracker (`state_tracker.py:44-71`). -/
structure BlockState where
  preState : PreState := {}
  accountReads : List Address := []
  accountWrites : List (Address × Option Account) := []
  storageReads : List (Address × StorageKey) := []
  storageWrites : List ((Address × StorageKey) × StorageVal) := []
  codeWrites : List (Hash32 × Nat) := []
  storageClears : List Address := []
  deriving Repr, DecidableEq, BEq

/-- Transaction-scoped state tracker (`state_tracker.py:74-101`).
Read chain: `txWrites -> blockWrites -> preState`. -/
structure TransactionState where
  parent : BlockState := {}
  accountReads : List Address := []
  accountWrites : List (Address × Option Account) := []
  storageReads : List (Address × StorageKey) := []
  storageWrites : List ((Address × StorageKey) × StorageVal) := []
  codeWrites : List (Hash32 × Nat) := []
  createdAccounts : List Address := []
  storageClears : List Address := []
  transientStorage : List ((Address × StorageKey) × StorageVal) := []
  deriving Repr, DecidableEq, BEq

/-! ## 3. Exact `state_tracker.py` Read/Write/Lifecycle Functions (`lines 103-789`) -/

/-- Pure value-lookup projection of `get_pre_state_account_optional` (`state_tracker.py:103-133`):
Look up the account at `addr` before the current transaction (`parent.accountWrites` then `preState`).
See `read_account_tx` below for the stateful transition that also appends `addr` to `accountReads`. -/
def get_pre_state_account_optional (txState : TransactionState) (addr : Address) : Option Account :=
  match txState.parent.accountWrites.find? (fun p => p.1 == addr) with
  | some (_, accOpt) => accOpt
  | none => txState.parent.preState.getAccountOptional addr

/-- Pure value-lookup projection of `get_pre_state_account` (`state_tracker.py:136-167`):
Return `get_pre_state_account_optional` or `EMPTY_ACCOUNT` if `none`. -/
def get_pre_state_account (txState : TransactionState) (addr : Address) : Account :=
  match get_pre_state_account_optional txState addr with
  | some acc => acc
  | none => EMPTY_ACCOUNT

/-- Pure value-lookup projection of `get_account_optional` (`state_tracker.py:170-193`):
Read chain `txState.accountWrites -> parent.accountWrites -> preState`.
See `read_account_tx` below for the stateful transition that also records `accountReads`. -/
def get_account_optional (txState : TransactionState) (addr : Address) : Option Account :=
  match txState.accountWrites.find? (fun p => p.1 == addr) with
  | some (_, accOpt) => accOpt
  | none => get_pre_state_account_optional txState addr

/-- Pure value-lookup projection of `get_account` (`state_tracker.py:196-221`):
Return `get_account_optional` or `EMPTY_ACCOUNT` if `none`. -/
def get_account (txState : TransactionState) (addr : Address) : Account :=
  match get_account_optional txState addr with
  | some acc => acc
  | none => EMPTY_ACCOUNT

/-- Pure value-lookup projection of `get_storage` (`state_tracker.py:252-285`):
Read chain: `txState.storageWrites` -> `txState.storageClears` (`0`) ->
`parent.storageWrites` -> `parent.storageClears` (`0`) -> `preState.getStorage`.
See `read_storage_tx` below for the stateful transition that also records `storageReads`. -/
def get_storage (txState : TransactionState) (addr : Address) (key : StorageKey) : StorageVal :=
  match txState.storageWrites.find? (fun p => p.1 == (addr, key)) with
  | some (_, v) => v
  | none =>
    if txState.storageClears.contains addr then 0
    else
      match txState.parent.storageWrites.find? (fun p => p.1 == (addr, key)) with
      | some (_, v) => v
      | none =>
        if txState.parent.storageClears.contains addr then 0
        else txState.parent.preState.getStorage addr key

/-- Stateful account read transition (`state_tracker.py:103-221`):
Returns `get_account txState addr` and records `addr` in `txState.accountReads`
(`tx_state.account_reads.add(address)` at `state_tracker.py:130, 190`). -/
def read_account_tx (txState : TransactionState) (addr : Address) : Account × TransactionState :=
  let newReads := if txState.accountReads.contains addr then txState.accountReads else addr :: txState.accountReads
  (get_account txState addr, { txState with accountReads := newReads })

/-- Stateful storage read transition (`state_tracker.py:252-285`):
Returns `get_storage txState addr key` and records `(addr, key)` in `txState.storageReads`
(`tx_state.storage_reads.add((address, key))` at `state_tracker.py:274`). -/
def read_storage_tx (txState : TransactionState) (addr : Address) (key : StorageKey) :
    StorageVal × TransactionState :=
  let newReads :=
    if txState.storageReads.contains (addr, key) then txState.storageReads
    else (addr, key) :: txState.storageReads
  (get_storage txState addr key, { txState with storageReads := newReads })

@[simp]
theorem read_account_tx_records_read (txState : TransactionState) (addr : Address) :
    (read_account_tx txState addr).1 = get_account txState addr ∧
    (read_account_tx txState addr).2.accountReads.contains addr = true := by
  dsimp only [read_account_tx]
  refine ⟨rfl, ?_⟩
  cases h : txState.accountReads.contains addr
  · simp
  · exact h

@[simp]
theorem read_storage_tx_records_read (txState : TransactionState) (addr : Address) (key : StorageKey) :
    (read_storage_tx txState addr key).1 = get_storage txState addr key ∧
    (read_storage_tx txState addr key).2.storageReads.contains (addr, key) = true := by
  dsimp only [read_storage_tx]
  refine ⟨rfl, ?_⟩
  cases h : txState.storageReads.contains (addr, key)
  · simp
  · exact h

/-- `get_storage_original` (`state_tracker.py:288-314`):
Return `0` if `addr ∈ txState.createdAccounts`, otherwise read from `parent.storageWrites` ->
`parent.storageClears` (`0`) -> `preState.getStorage`. -/
def get_storage_original (txState : TransactionState) (addr : Address) (key : StorageKey) : StorageVal :=
  if txState.createdAccounts.contains addr then 0
  else
    match txState.parent.storageWrites.find? (fun p => p.1 == (addr, key)) with
    | some (_, v) => v
    | none =>
      if txState.parent.storageClears.contains addr then 0
      else txState.parent.preState.getStorage addr key

/-- `get_transient_storage` (`state_tracker.py:317-339`). -/
def get_transient_storage (txState : TransactionState) (addr : Address) (key : StorageKey) : StorageVal :=
  match txState.transientStorage.find? (fun p => p.1 == (addr, key)) with
  | some (_, v) => v
  | none => 0

/-- `account_exists` (`state_tracker.py:342-359`):
`get_account_optional(tx_state, address) is not None`. -/
def account_exists (txState : TransactionState) (addr : Address) : Bool :=
  (get_account_optional txState addr).isSome

/-- `account_deployable` (`state_tracker.py:362-370`):
True iff `account.nonce == 0` and `account.codeHash == EMPTY_CODE_HASH`. -/
def account_deployable (txState : TransactionState) (addr : Address) : Bool :=
  let acc := get_account txState addr
  acc.nonce == 0 && acc.codeHash == EMPTY_CODE_HASH

/-- `account_exists_and_is_empty` (`state_tracker.py:373-400`):
True iff `get_account_optional` is `some acc` with `nonce == 0`, `codeHash == EMPTY_CODE_HASH`, and `balance == 0`. -/
def account_exists_and_is_empty (txState : TransactionState) (addr : Address) : Bool :=
  match get_account_optional txState addr with
  | some acc => acc.isEmpty
  | none => false

/-- `is_account_alive` (`state_tracker.py:403-421`):
True iff `get_account_optional` is `some acc` and `acc != EMPTY_ACCOUNT`. -/
def is_account_alive (txState : TransactionState) (addr : Address) : Bool :=
  match get_account_optional txState addr with
  | some acc => !acc.isEmpty
  | none => false

/-- `set_account` (`state_tracker.py:424-444`):
Set `tx_state.account_writes[address] = account`. -/
def set_account (txState : TransactionState) (addr : Address) (acc : Option Account) : TransactionState :=
  { txState with
    accountWrites := (addr, acc) :: txState.accountWrites.filter (fun p => p.1 != addr) }

/-- `set_storage` (`state_tracker.py:447-471`):
Set `tx_state.storage_writes[address][key] = value`. -/
def set_storage (txState : TransactionState) (addr : Address) (key : StorageKey) (val : StorageVal) :
    TransactionState :=
  { txState with
    storageWrites := ((addr, key), val) :: txState.storageWrites.filter (fun p => p.1 != (addr, key)) }

/-- `destroy_storage` (`state_tracker.py:518-540`):
Move all `tx_state.storage_writes[address]` keys into `tx_state.storage_reads`, delete
`tx_state.storage_writes[address]`, and add `address` to `tx_state.storage_clears`. -/
def destroy_storage_tx (txState : TransactionState) (addr : Address) : TransactionState :=
  let writtenKeys := (txState.storageWrites.filter (fun p => p.1.1 == addr)).map Prod.fst
  let remainingWrites := txState.storageWrites.filter (fun p => p.1.1 != addr)
  let newClears := if txState.storageClears.contains addr then txState.storageClears else addr :: txState.storageClears
  { txState with
    storageReads := writtenKeys ++ txState.storageReads
    storageWrites := remainingWrites
    storageClears := newClears }

/-- `destroy_account` (`state_tracker.py:474-491`):
`destroy_storage(tx_state, address)` followed by `set_account(tx_state, address, None)`. -/
def destroy_account (txState : TransactionState) (addr : Address) : TransactionState :=
  set_account (destroy_storage_tx txState addr) addr none

/-- `modify_state` (`state_tracker.py:591-603`):
Modify `get_account(tx_state, address)` with `f`; if the resulting account is empty
(`account_exists_and_is_empty`), call `destroy_account(tx_state, address)`. -/
def modify_state (txState : TransactionState) (addr : Address) (f : Account → Account) : TransactionState :=
  let updated := f (get_account txState addr)
  let s1 := set_account txState addr (some updated)
  if updated.isEmpty then
    destroy_account s1 addr
  else
    s1

/-- `clear_account_preserving_balance` on `TransactionState` (`state_tracker.py:494-516`):
Calls `destroy_storage(tx_state, address)` and `modify_state(tx_state, address, clear_account)`
where `clear_account` zeroes `nonce` and sets `code_hash = EMPTY_CODE_HASH`. -/
def clear_account_preserving_balance_tx (txState : TransactionState) (addr : Address) : TransactionState :=
  let s1 := destroy_storage_tx txState addr
  modify_state s1 addr (fun acc =>
    { acc with nonce := 0, codeHash := EMPTY_CODE_HASH, codeEmpty := true, storageNonEmpty := false })

/-- `mark_account_created` (`state_tracker.py:542-562`):
Add `address` to `tx_state.created_accounts`. -/
@[simp]
def mark_account_created (txState : TransactionState) (addr : Address) : TransactionState :=
  if txState.createdAccounts.contains addr then txState
  else { txState with createdAccounts := addr :: txState.createdAccounts }

/-- `copy_tx_state` (`state_tracker.py:734-766`):
Snapshot `TransactionState` for copy-on-write rollback. Note that `parent`, `createdAccounts`,
`storageReads`, and `accountReads` are shared across snapshots in Python. -/
@[simp]
def copy_tx_state (txState : TransactionState) : TransactionState :=
  txState

/-- `restore_tx_state` (`state_tracker.py:769-788`):
Restore `accountWrites`, `storageWrites`, `codeWrites`, `storageClears`, and `transientStorage`
from `snapshot`, while keeping accumulated `accountReads`, `storageReads`, and `createdAccounts`. -/
@[simp]
def restore_tx_state (current snapshot : TransactionState) : TransactionState :=
  { current with
    accountWrites := snapshot.accountWrites
    storageWrites := snapshot.storageWrites
    codeWrites := snapshot.codeWrites
    storageClears := snapshot.storageClears
    transientStorage := snapshot.transientStorage }

/-- Theorem: `restore_tx_state` after arbitrary writes restores all 5 mutable write maps to
`snapshot` while preserving `accountReads` and `storageReads`. -/
theorem restore_tx_state_writes_exact (current snapshot : TransactionState) :
    let r := restore_tx_state current snapshot
    r.accountWrites = snapshot.accountWrites ∧
    r.storageWrites = snapshot.storageWrites ∧
    r.codeWrites = snapshot.codeWrites ∧
    r.storageClears = snapshot.storageClears ∧
    r.transientStorage = snapshot.transientStorage ∧
    r.accountReads = current.accountReads ∧
    r.storageReads = current.storageReads := by
  simp [restore_tx_state]

/-- `get_code` (`state_tracker.py:224-249`):
Look up bytecode length / content by `codeHash` (`txState.codeWrites -> parent.codeWrites -> preState.codes`). -/
def get_code (txState : TransactionState) (codeHash : Hash32) : Nat :=
  if codeHash == EMPTY_CODE_HASH then 0
  else
    match txState.codeWrites.find? (fun p => p.1 == codeHash) with
    | some (_, len) => len
    | none =>
      match txState.parent.codeWrites.find? (fun p => p.1 == codeHash) with
      | some (_, len) => len
      | none =>
        match txState.parent.preState.codes.find? (fun p => p.1 == codeHash) with
        | some (_, len) => len
        | none => 0

/-- `set_transient_storage` (`state_tracker.py:565-588`). -/
def set_transient_storage (txState : TransactionState) (addr : Address) (key : StorageKey) (val : StorageVal) :
    TransactionState :=
  { txState with
    transientStorage := ((addr, key), val) :: txState.transientStorage.filter (fun p => p.1 != (addr, key)) }

/-- `move_ether_tx` (`state_tracker.py:606-638`):
Transfer `amount` from `sender` to `recipient` via `modify_state` (`lines 636-638`), or return
`none` (`InsufficientBalanceError`) if `senderAcc.balance < amount`. -/
def move_ether_tx (txState : TransactionState) (sender recipient : Address) (amount : Nat) :
    Option TransactionState :=
  let senderAcc := get_account txState sender
  if senderAcc.balance < amount then
    none
  else
    let s1 := modify_state txState sender (fun acc => { acc with balance := acc.balance - amount })
    some (modify_state s1 recipient (fun acc => { acc with balance := acc.balance + amount }))

/-- `create_ether` (`state_tracker.py:640-660`):
Add `amount` to `recipient`'s balance via `modify_state(tx_state, recipient, add_balance)`. -/
def create_ether (txState : TransactionState) (recipient : Address) (amount : Nat) : TransactionState :=
  modify_state txState recipient (fun acc => { acc with balance := acc.balance + amount })

/-- `set_account_balance_tx` (`state_tracker.py:663-684`):
In `execution-specs` (`state_tracker.py:683`), `set_account_balance` calls
`modify_state(tx_state, address, set_balance)`, which destroys the account (`set_account(..., None)`)
if setting `balance := newBalance` produces `EMPTY_ACCOUNT`. -/
def set_account_balance_tx (txState : TransactionState) (addr : Address) (newBalance : Nat) :
    TransactionState :=
  modify_state txState addr (fun acc => { acc with balance := newBalance })

/-- `increment_nonce` (`state_tracker.py:686-703`):
Increment `addr`'s nonce by 1 via `modify_state(tx_state, address, increase_nonce)`. -/
def increment_nonce (txState : TransactionState) (addr : Address) : TransactionState :=
  modify_state txState addr (fun acc => { acc with nonce := acc.nonce + 1 })

/-- `set_code` (`state_tracker.py:705-729`):
If `codeHash != EMPTY_CODE_HASH` (`state_tracker.py:722-723`), record `(codeHash, codeLen)` in
`codeWrites`, and update `addr`'s `codeHash` via `modify_state(tx_state, address, write_code)` (`line 728`). -/
def set_code (txState : TransactionState) (addr : Address) (codeHash : Hash32) (codeLen : Nat) :
    TransactionState :=
  let s0 :=
    if codeHash != EMPTY_CODE_HASH then
      { txState with codeWrites := (codeHash, codeLen) :: txState.codeWrites.filter (fun p => p.1 != codeHash) }
    else
      txState
  modify_state s0 addr (fun acc => { acc with codeHash := codeHash, codeEmpty := (codeHash == EMPTY_CODE_HASH) })

/-- `incorporate_tx_into_block` (`state_tracker.py:793-846`):
Merge `txState` into `txState.parent` (`BlockState`). Crucially (`lines 827-829`), for each
`addr ∈ txState.storageClears`, any prior `parent.storageWrites` for `addr` are removed and
`addr` is added to `parent.storageClears` before applying `txState.storageWrites`. -/
def incorporate_tx_into_block (txState : TransactionState) : BlockState :=
  let p := txState.parent
  let mergedAccountWrites :=
    txState.accountWrites ++
      p.accountWrites.filter (fun pair => !txState.accountWrites.any (fun w => w.1 == pair.1))
  let clearedParentStorageWrites :=
    p.storageWrites.filter (fun pair => !txState.storageClears.contains pair.1.1)
  let mergedStorageClears :=
    txState.storageClears ++
      p.storageClears.filter (fun a => !txState.storageClears.contains a)
  let mergedStorageWrites :=
    txState.storageWrites ++
      clearedParentStorageWrites.filter (fun pair => !txState.storageWrites.any (fun w => w.1 == pair.1))
  let mergedCodeWrites :=
    txState.codeWrites ++
      p.codeWrites.filter (fun pair => !txState.codeWrites.any (fun w => w.1 == pair.1))
  { preState := p.preState
    accountReads := txState.accountReads ++ p.accountReads
    accountWrites := mergedAccountWrites
    storageReads := txState.storageReads ++ p.storageReads
    storageWrites := mergedStorageWrites
    codeWrites := mergedCodeWrites
    storageClears := mergedStorageClears }

/-- Look up the effective storage value of `(addr, key)` in `BlockState` (`state_tracker.py:276-285`). -/
def get_block_storage (blockState : BlockState) (addr : Address) (key : StorageKey) : StorageVal :=
  match blockState.storageWrites.find? (fun p => p.1 == (addr, key)) with
  | some (_, v) => v
  | none =>
    if blockState.storageClears.contains addr then 0
    else blockState.preState.getStorage addr key

/-- Well-formedness predicate on `TransactionState`: no entry in `accountWrites`, `parent.accountWrites`,
or `parent.preState.accounts` stores `some acc` with `acc.isEmpty = true` (canonical post-EIP-161 /
EIP-7523 invariant). -/
def NoEmptyAccountLeaves (txState : TransactionState) (addr : Address) : Prop :=
  ∀ acc, get_account_optional txState addr = some acc → acc.isEmpty = false

/-- Theorem: Under `NoEmptyAccountLeaves`, `account_exists` and `is_account_alive` are identical;
they can only diverge if `get_account_optional txState addr = some acc` with `acc.isEmpty = true`
(e.g. an unpruned `EMPTY_ACCOUNT` leaf injected into `PreState` in a synthetic test fixture). -/
theorem account_exists_iff_alive_of_no_empty_leaves (txState : TransactionState) (addr : Address)
    (h_wf : NoEmptyAccountLeaves txState addr) :
    account_exists txState addr = is_account_alive txState addr := by
  dsimp only [account_exists, is_account_alive]
  cases h_opt : get_account_optional txState addr with
  | none => rfl
  | some acc =>
    have h_ne := h_wf acc h_opt
    simp only [Option.isSome_some, h_ne, Bool.not_false]

/-! ### Layer-0b Equation Lemmas for `TransactionState` Read/Write Operations -/

@[simp]
theorem get_account_optional_set_account_same (txState : TransactionState) (addr : Address)
    (acc : Option Account) :
    get_account_optional (set_account txState addr acc) addr = acc := by
  simp [get_account_optional, set_account]

@[simp]
theorem get_account_set_account_some_same (txState : TransactionState) (addr : Address)
    (acc : Account) :
    get_account (set_account txState addr (some acc)) addr = acc := by
  simp [get_account]

@[simp]
theorem get_account_set_account_none_same (txState : TransactionState) (addr : Address) :
    get_account (set_account txState addr none) addr = EMPTY_ACCOUNT := by
  simp [get_account]

@[simp]
theorem get_account_optional_destroy_storage_tx (txState : TransactionState) (addr target : Address) :
    get_account_optional (destroy_storage_tx txState addr) target =
      get_account_optional txState target := rfl

@[simp]
theorem get_account_destroy_storage_tx (txState : TransactionState) (addr target : Address) :
    get_account (destroy_storage_tx txState addr) target = get_account txState target := by
  simp [get_account]

theorem find?_filter_addr_ne_eq_none (xs : List ((Address × StorageKey) × StorageVal))
    (addr : Address) (slot : StorageKey) :
    (xs.filter (fun p => p.1.1 != addr)).find? (fun p => p.1 == (addr, slot)) = none := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨⟨a, k⟩, v⟩
    dsimp [List.filter]
    by_cases ha : (a != addr) = true
    · simp only [ha, List.find?]
      have h_neq : ((a, k) == (addr, slot)) = false := by
        rw [beq_eq_false_iff_ne]
        intro h_eq
        injection h_eq with h1 _
        rw [bne_iff_ne] at ha
        exact ha h1
      simp [h_neq, ih]
    · simp [ha, ih]

@[simp]
theorem storageClears_destroy_storage_tx_contains (txState : TransactionState) (addr : Address) :
    (destroy_storage_tx txState addr).storageClears.contains addr = true := by
  dsimp only [destroy_storage_tx]
  cases h : txState.storageClears.contains addr
  · simp
  · exact h

@[simp]
theorem get_storage_destroy_storage_tx_same (txState : TransactionState) (addr : Address)
    (slot : StorageKey) :
    get_storage (destroy_storage_tx txState addr) addr slot = 0 := by
  dsimp only [get_storage]
  have h_find :
      (destroy_storage_tx txState addr).storageWrites.find? (fun p => p.1 == (addr, slot)) = none := by
    dsimp only [destroy_storage_tx]
    exact find?_filter_addr_ne_eq_none txState.storageWrites addr slot
  have h_clear := storageClears_destroy_storage_tx_contains txState addr
  rw [h_find, h_clear]
  rfl

@[simp]
theorem get_storage_set_account (txState : TransactionState) (addr target : Address)
    (acc : Option Account) (slot : StorageKey) :
    get_storage (set_account txState addr acc) target slot = get_storage txState target slot := by
  rfl

@[simp]
theorem get_account_destroy_account_same (txState : TransactionState) (addr : Address) :
    get_account (destroy_account txState addr) addr = EMPTY_ACCOUNT := by
  simp [destroy_account]

@[simp]
theorem get_account_optional_destroy_account_same (txState : TransactionState) (addr : Address) :
    get_account_optional (destroy_account txState addr) addr = none := by
  simp [destroy_account]

@[simp]
theorem get_storage_destroy_account_same (txState : TransactionState) (addr : Address)
    (slot : StorageKey) :
    get_storage (destroy_account txState addr) addr slot = 0 := by
  dsimp only [destroy_account]
  rw [get_storage_set_account, get_storage_destroy_storage_tx_same]

/-- Theorem (`no_empty_account_leaves_preserved`, `state_tracker.py:591-729`):
Because `modify_state` destroys the account (`set_account(..., None)`) whenever `f(acc).isEmpty = true`,
every `state_tracker.py` account mutator (`modify_state`, `set_account_balance_tx`, `increment_nonce`,
`create_ether`, `set_code`, `clear_account_preserving_balance_tx`) establishes `NoEmptyAccountLeaves`
at the target address `addr` — it NEVER creates an `EMPTY_ACCOUNT` leaf in `accountWrites`! -/
theorem modify_state_no_empty_account_leaf (txState : TransactionState) (addr : Address)
    (f : Account → Account) :
    NoEmptyAccountLeaves (modify_state txState addr f) addr := by
  intro acc h_opt
  dsimp only [modify_state] at h_opt
  cases h_emp : (f (get_account txState addr)).isEmpty
  · rw [h_emp] at h_opt
    simp only [Bool.false_eq_true, ↓reduceIte, get_account_optional_set_account_same, Option.some.injEq] at h_opt
    subst h_opt
    exact h_emp
  · rw [h_emp] at h_opt
    simp only [↓reduceIte, get_account_optional_destroy_account_same, reduceCtorEq] at h_opt

theorem no_empty_account_leaves_preserved (txState : TransactionState) (addr : Address)
    (newBal amount : Nat) (codeHash : Hash32) (codeLen : Nat) :
    NoEmptyAccountLeaves (set_account_balance_tx txState addr newBal) addr ∧
    NoEmptyAccountLeaves (increment_nonce txState addr) addr ∧
    NoEmptyAccountLeaves (create_ether txState addr amount) addr ∧
    NoEmptyAccountLeaves (set_code txState addr codeHash codeLen) addr ∧
    NoEmptyAccountLeaves (clear_account_preserving_balance_tx txState addr) addr := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact modify_state_no_empty_account_leaf txState addr _
  · exact modify_state_no_empty_account_leaf txState addr _
  · exact modify_state_no_empty_account_leaf txState addr _
  · exact modify_state_no_empty_account_leaf _ addr _
  · exact modify_state_no_empty_account_leaf _ addr _

/-! ## 4. Algebraic Single-Target Snapshot Projection (Backwards-Compatible with Layer-II Proofs) -/

structure WorldSnapshot where
  targetAccount : Account := {}
  recipientBalance : Nat := 0
  createdInTx : Bool := false
  markedToDelete : Bool := false
  deriving Repr, DecidableEq, BEq

structure State where
  current : WorldSnapshot := {}
  snapshots : List WorldSnapshot := []
  deriving Repr, DecidableEq, BEq

def begin_transaction (s : State) : State :=
  { s with snapshots := s.current :: s.snapshots }

def commit_transaction (s : State) : State :=
  match s.snapshots with
  | _ :: rest => { s with snapshots := rest }
  | [] => s

def rollback_transaction (s : State) : State :=
  match s.snapshots with
  | snap :: rest => { current := snap, snapshots := rest }
  | [] => s

/-- T-COMMON-CHECKPOINT-ROLLBACK: Rolling back after `begin_transaction` and arbitrary
in-frame mutations restores the exact pre-checkpoint `State`. -/
theorem t_common_checkpoint_rollback (s : State) (mutated : WorldSnapshot) :
    rollback_transaction { (begin_transaction s) with current := mutated } = s := by
  cases s; rfl

def set_account_balance (acc : Account) (newBalance : Nat) : Account :=
  { acc with balance := newBalance }

def move_ether_self (acc : Account) (amount : Nat) : Option Account :=
  if acc.balance ≥ amount then some acc else none

def move_ether_distinct (senderBalance recipientBalance amount : Nat) : Option (Nat × Nat) :=
  if senderBalance ≥ amount then
    some (senderBalance - amount, recipientBalance + amount)
  else
    none

theorem move_ether_distinct_conserves_sum (s r amount s' r' : Nat)
    (h : move_ether_distinct s r amount = some (s', r')) :
    s' + r' = s + r := by
  unfold move_ether_distinct at h
  split at h <;> simp_all
  omega

def destroy_storage (acc : Account) : Account :=
  { acc with storageNonEmpty := false }

def clear_account_preserving_balance (snap : WorldSnapshot) : WorldSnapshot :=
  if snap.markedToDelete && snap.createdInTx then
    let cleared := destroy_storage { snap.targetAccount with nonce := 0, codeHash := EMPTY_CODE_HASH, codeEmpty := true }
    { snap with targetAccount := cleared }
  else
    snap

/-! ## 5. Exact Two-Dimensional `GasMeter` (`src/ethereum/forks/amsterdam/vm/gas.py:258-735`) -/

/-- Exact 6-field `GasMeter` from `src/ethereum/forks/amsterdam/vm/gas.py:260-325`:
- `gasLeft`: execution gas remaining in the frame (`gas_left`).
- `stateGasLeft`: state gas remaining in the reservoir (`state_gas_left`).
- `stateGasBaseline`: reservoir level a rollback refills to (`state_gas_baseline`).
- `refundCounter`: execution gas eligible for refund at tx end (`refund_counter : Int`).
- `stateGasSpilled`: execution gas spent covering state charges after reservoir emptied (`state_gas_spilled`).
- `stateGasCommittedSpill`: spill marked non-refillable by `commit_state_gas` (`state_gas_committed_spill`). -/
@[ext]
structure GasMeter where
  gasLeft : Nat
  stateGasLeft : Nat
  stateGasBaseline : Nat
  refundCounter : Int := 0
  stateGasSpilled : Nat := 0
  stateGasCommittedSpill : Nat := 0
  deriving Repr, DecidableEq, BEq

/-- `charge_gas_from_meter` (`vm/gas.py:379-394`):
Subtract `amount` from `gas_left` or return `none` (`OutOfGasError`). -/
@[simp]
def charge_gas_from_meter (m : GasMeter) (amount : Nat) : Option GasMeter :=
  if m.gasLeft < amount then
    none
  else
    some { m with gasLeft := m.gasLeft - amount }

/-- `charge_state_gas_from_meter` (`vm/gas.py:413-436`):
Subtract `amount` from `state_gas_left` first, then spill into `gas_left` and increment
`state_gas_spilled` when the reservoir is exhausted, or return `none` (`OutOfGasError`). -/
@[simp]
def charge_state_gas_from_meter (m : GasMeter) (amount : Nat) : Option GasMeter :=
  if m.stateGasLeft ≥ amount then
    some { m with stateGasLeft := m.stateGasLeft - amount }
  else if m.stateGasLeft + m.gasLeft ≥ amount then
    let remainder := amount - m.stateGasLeft
    some { m with
      stateGasLeft := 0
      gasLeft := m.gasLeft - remainder
      stateGasSpilled := m.stateGasSpilled + remainder }
  else
    none

/-- `commit_state_gas` (`vm/gas.py:459-490`):
Mark state gas spent so far (e.g., EIP-7702 `set_delegation`) as non-refillable on frame revert. -/
@[simp]
def commit_state_gas (m : GasMeter) : GasMeter :=
  { m with
    stateGasCommittedSpill := m.stateGasCommittedSpill + m.stateGasSpilled
    stateGasBaseline := m.stateGasLeft
    stateGasSpilled := 0 }

/-- `restore_state_gas` (`vm/gas.py:493-517`):
Roll the frame's state gas back to `stateGasBaseline` on revert or exceptional halt,
crediting `stateGasSpilled` back to `gasLeft` in LIFO order and zeroing `refundCounter`. -/
@[simp]
def restore_state_gas (m : GasMeter) : GasMeter :=
  { m with
    gasLeft := m.gasLeft + m.stateGasSpilled
    stateGasSpilled := 0
    stateGasLeft := m.stateGasBaseline
    refundCounter := 0 }

/-- `restore_state_gas_to_entry` (`vm/gas.py:520-555`):
Roll the top frame's state gas back to frame entry (`stateGasReservoir`), undoing any commit. -/
@[simp]
def restore_state_gas_to_entry (m : GasMeter) (stateGasReservoir : Nat) : GasMeter :=
  { m with
    gasLeft := m.gasLeft + m.stateGasSpilled + m.stateGasCommittedSpill
    stateGasSpilled := 0
    stateGasCommittedSpill := 0
    stateGasLeft := stateGasReservoir
    stateGasBaseline := stateGasReservoir
    refundCounter := 0 }

/-- `tx_state_gas_used` (`vm/gas.py:558-591`):
Net state gas consumed by the transaction (`Int`), possibly negative when refunds exceed charges. -/
@[simp]
def tx_state_gas_used (m : GasMeter) (stateGasReservoir : Nat) : Int :=
  (stateGasReservoir : Int) - (m.stateGasLeft : Int) +
    (m.stateGasSpilled : Int) + (m.stateGasCommittedSpill : Int)

/-- `credit_state_gas_refund` (`vm/gas.py:594-616`):
Credit a state-gas refund in LIFO order (`gasLeft` up to `stateGasSpilled` first, then `stateGasLeft`). -/
@[simp]
def credit_state_gas_refund (m : GasMeter) (amount : Nat) : GasMeter :=
  let fromGasLeft := min amount m.stateGasSpilled
  { m with
    gasLeft := m.gasLeft + fromGasLeft
    stateGasSpilled := m.stateGasSpilled - fromGasLeft
    stateGasLeft := m.stateGasLeft + (amount - fromGasLeft) }

/-- `repay_state_gas_spill` (`vm/gas.py:619-647`):
Repay outstanding `stateGasSpilled` from `stateGasLeft` after a successful child frame merges. -/
@[simp]
def repay_state_gas_spill (m : GasMeter) : GasMeter :=
  let repayment := min m.stateGasLeft m.stateGasSpilled
  { m with
    gasLeft := m.gasLeft + repayment
    stateGasLeft := m.stateGasLeft - repayment
    stateGasSpilled := m.stateGasSpilled - repayment }

/-- `forfeit_remaining_gas` (`vm/gas.py:650-663`):
Consume all remaining `gasLeft` on an exceptional halt (after `restore_state_gas`). -/
@[simp]
def forfeit_remaining_gas (m : GasMeter) : GasMeter :=
  { m with gasLeft := 0 }

/-- `max_message_call_gas` (`vm/gas.py:846-861`):
`gas - (gas // 64)` (`63/64` rule). -/
@[simp]
def max_message_call_gas (gas : Nat) : Nat :=
  gas - gas / 64

/-- `withhold_create_gas` (`vm/gas.py:666-686`):
Deduct `max_message_call_gas(gas_meter.gas_left)` and return `(childGas, updatedMeter)`. -/
@[simp]
def withhold_create_gas (m : GasMeter) : Nat × GasMeter :=
  let childGas := max_message_call_gas m.gasLeft
  (childGas, { m with gasLeft := m.gasLeft - childGas })

/-- `drain_state_gas_reservoir` (`vm/gas.py:689-710`):
Empty `stateGasLeft` for a child frame and return `(reservoir, updatedMeter)`. -/
@[simp]
def drain_state_gas_reservoir (m : GasMeter) : Nat × GasMeter :=
  (m.stateGasLeft, { m with stateGasLeft := 0 })

/-- `restore_child_gas` (`vm/gas.py:713-734`):
Return a child frame's unused execution gas and state gas reservoir when preflight aborts. -/
@[simp]
def restore_child_gas (m : GasMeter) (gas stateGasReservoir : Nat) : GasMeter :=
  { m with
    gasLeft := m.gasLeft + gas
    stateGasLeft := m.stateGasLeft + stateGasReservoir }

/-- `incorporate_child` on `GasMeter` (`vm/__init__.py:188-245`):
Absorb returning child's `GasMeter` into parent's `GasMeter` (note: a failed child already ran
`restore_state_gas` and, on halt, `forfeit_remaining_gas` before returning), and if `!childError`,
run `repay_state_gas_spill`. -/
@[simp]
def incorporate_child_meter (parent child : GasMeter) (childError : Bool) : GasMeter :=
  let merged : GasMeter :=
    { parent with
      gasLeft := parent.gasLeft + child.gasLeft
      stateGasLeft := parent.stateGasLeft + child.stateGasLeft
      stateGasSpilled := parent.stateGasSpilled + child.stateGasSpilled
      refundCounter := parent.refundCounter + child.refundCounter }
  if !childError then
    repay_state_gas_spill merged
  else
    merged

/-! ## 6. Key Universal `GasMeter` Lemmas (`vm/gas.py` & `vm/__init__.py`) -/

/-- Theorem: `credit_state_gas_refund` after `charge_state_gas_from_meter` of the same `amount`
is an exact left-inverse on `GasMeter` whenever the `GasMeter` satisfies the spill invariant
(`stateGasLeft = 0 ∨ stateGasSpilled = 0`), restoring `gasLeft`, `stateGasLeft`, and `stateGasSpilled`. -/
theorem credit_after_charge_state_gas_exact (m post : GasMeter) (amount : Nat)
    (h_inv : m.stateGasLeft = 0 ∨ m.stateGasSpilled = 0)
    (h : charge_state_gas_from_meter m amount = some post) :
    credit_state_gas_refund post amount = m := by
  unfold charge_state_gas_from_meter at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    unfold credit_state_gas_refund
    ext <;> simp only <;> rcases h_inv with h0 | h0 <;> omega
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      unfold credit_state_gas_refund
      ext <;> simp only <;> rcases h_inv with h0 | h0 <;> omega
    · contradiction

/-- Theorem: `repay_state_gas_spill` preserves total available gas (`gasLeft + stateGasLeft`),
preserves net state gas (`stateGasSpilled - stateGasLeft`), and leaves at least one of
`stateGasLeft` or `stateGasSpilled` equal to `0` (`vm/gas.py:645`). -/
theorem repay_state_gas_spill_invariant (m : GasMeter) :
    let r := repay_state_gas_spill m
    r.gasLeft + r.stateGasLeft = m.gasLeft + m.stateGasLeft ∧
    (r.stateGasLeft = 0 ∨ r.stateGasSpilled = 0) := by
  unfold repay_state_gas_spill
  simp only
  constructor
  · omega
  · by_cases h : m.stateGasLeft ≤ m.stateGasSpilled
    · left; omega
    · right; omega

/-- `check_gas` (`vm/gas.py:363-376`): True iff `m.gasLeft ≥ amount`. -/
@[simp]
def check_gas (m : GasMeter) (amount : Nat) : Bool :=
  decide (m.gasLeft ≥ amount)

/-- `GasMeter` Spill Invariant (`vm/gas.py:260-303`): at least one of `stateGasLeft` or
`stateGasSpilled` is `0` at all times during normal execution. -/
def GasMeter.SpillInvariant (m : GasMeter) : Prop :=
  m.stateGasLeft = 0 ∨ m.stateGasSpilled = 0

/-- Theorem: Every single `GasMeter` transition (`charge_gas_from_meter`, `charge_state_gas_from_meter`,
`credit_state_gas_refund`, `commit_state_gas`, `restore_state_gas`, `repay_state_gas_spill`)
preserves `GasMeter.SpillInvariant`. -/
theorem spill_invariant_preserved_by_meter_ops (m post : GasMeter) (amount : Nat)
    (h_inv : m.SpillInvariant) :
    (charge_gas_from_meter m amount = some post → post.SpillInvariant) ∧
    (charge_state_gas_from_meter m amount = some post → post.SpillInvariant) ∧
    (credit_state_gas_refund m amount).SpillInvariant ∧
    (commit_state_gas m).SpillInvariant ∧
    (restore_state_gas m).SpillInvariant ∧
    (repay_state_gas_spill m).SpillInvariant := by
  refine ⟨?_, ?_, ?_, ?_, ?_, (repay_state_gas_spill_invariant m).2⟩
  · intro h
    unfold charge_gas_from_meter at h
    split at h
    · contradiction
    · simp only [Option.some.injEq] at h
      subst h
      exact h_inv
  · intro h
    unfold charge_state_gas_from_meter at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      unfold GasMeter.SpillInvariant at *
      rcases h_inv with h0 | h0 <;> simp_all
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        left; rfl
      · contradiction
  · unfold credit_state_gas_refund GasMeter.SpillInvariant
    dsimp only
    rcases h_inv with h0 | h0
    · by_cases h_le : amount ≤ m.stateGasSpilled
      · left; omega
      · right; omega
    · right; omega
  · right; rfl
  · right; rfl

/-- Multi-frame EVM execution state (`vm/__init__.py:124-245` & `vm/interpreter.py:235-392`)
pairing `TransactionState`, `GasMeter`, and the frame-local `accountsToDelete` list. -/
structure EvmFrame where
  txState : TransactionState
  gasMeter : GasMeter
  accountsToDelete : List Address := []
  deriving Repr, DecidableEq, BEq

/-- `incorporate_child` on `EvmFrame` (`vm/__init__.py:188-245` & `vm/interpreter.py:377-392`):
- On child success (`childError = false`), merges `child.accountsToDelete` into `parent.accountsToDelete`,
  adopts `child.txState`, and merges `child.gasMeter` with `repay_state_gas_spill`.
- On child error/revert (`childError = true`), discards `child.accountsToDelete`, restores
  `parent.txState` write maps via `restore_tx_state`, and merges the restored `child.gasMeter`. -/
def incorporate_child_frame (parentSnapshot child : EvmFrame) (childError : Bool) : EvmFrame :=
  if !childError then
    { txState := child.txState
      gasMeter := incorporate_child_meter parentSnapshot.gasMeter child.gasMeter false
      accountsToDelete := parentSnapshot.accountsToDelete ++ child.accountsToDelete }
  else
    { txState := restore_tx_state child.txState parentSnapshot.txState
      gasMeter := incorporate_child_meter parentSnapshot.gasMeter child.gasMeter true
      accountsToDelete := parentSnapshot.accountsToDelete }

/-- Theorem: When a child frame reverts or halts (`childError = true`), `incorporate_child_frame`
discards any `SELFDESTRUCT` registrations (`child.accountsToDelete`) and restores all 5 mutable
write maps of `parentSnapshot.txState`. -/
theorem incorporate_child_frame_revert_discards_deletes (parentSnapshot child : EvmFrame) :
    let post := incorporate_child_frame parentSnapshot child true
    post.accountsToDelete = parentSnapshot.accountsToDelete ∧
    post.txState.accountWrites = parentSnapshot.txState.accountWrites ∧
    post.txState.storageWrites = parentSnapshot.txState.storageWrites ∧
    post.txState.storageClears = parentSnapshot.txState.storageClears := by
  simp [incorporate_child_frame, restore_tx_state]

/-- Theorem: `restore_state_gas_to_entry` after `commit_state_gas` and any sequence of state-gas
charges restores the exact total gas (`gasLeft + stateGasLeft`) to the pre-charge sum whenever
`stateGasLeft = stateGasReservoir` and `stateGasCommittedSpill = 0` at entry. -/
theorem restore_state_gas_to_entry_sound (m : GasMeter) (reservoir : Nat)
    (h_left : m.stateGasLeft = reservoir)
    (h_spilled : m.stateGasSpilled = 0)
    (h_comm : m.stateGasCommittedSpill = 0)
    (c1 c2 : Nat) (m1 m2 : GasMeter)
    (hc1 : charge_state_gas_from_meter m c1 = some m1)
    (hc2 : charge_state_gas_from_meter (commit_state_gas m1) c2 = some m2) :
    let restored := restore_state_gas_to_entry m2 reservoir
    restored.gasLeft = m.gasLeft ∧
    restored.stateGasLeft = reservoir ∧
    restored.stateGasSpilled = 0 ∧
    restored.stateGasCommittedSpill = 0 := by
  unfold charge_state_gas_from_meter at hc1 hc2
  split at hc1 <;> (try split at hc1) <;> try contradiction
  all_goals
    simp only [Option.some.injEq] at hc1
    subst hc1
    dsimp [commit_state_gas] at hc2
    split at hc2 <;> (try split at hc2) <;> try contradiction
    all_goals
      simp only [Option.some.injEq] at hc2
      subst hc2
      simp only [restore_state_gas_to_entry, h_left, h_spilled, h_comm, and_self, and_true]
      omega

/-! ## 7. Compact Two-Leg `EvmGasFrame` Projection & C-ABI Export -/

structure EvmGasFrame where
  gasLeft : Nat
  stateGasReservoir : Nat
  refundCounter : Nat := 0
  deriving Repr, DecidableEq, BEq

def charge_gas (frame : EvmGasFrame) (regularGas stateGas : Nat) : Option EvmGasFrame :=
  let spill := if stateGas > frame.stateGasReservoir then stateGas - frame.stateGasReservoir else 0
  let totalRegularNeeded := regularGas + spill
  if frame.gasLeft < totalRegularNeeded then
    none
  else
    let newReservoir := frame.stateGasReservoir - min stateGas frame.stateGasReservoir
    let newGasLeft := frame.gasLeft - totalRegularNeeded
    some { frame with gasLeft := newGasLeft, stateGasReservoir := newReservoir }

/-- Equivalence between `charge_gas` on `EvmGasFrame` and `charge_gas_from_meter` followed by
`charge_state_gas_from_meter` on `GasMeter`. -/
theorem charge_gas_equiv_meter (frame : EvmGasFrame) (regularGas stateGas : Nat) :
    let m0 : GasMeter := ⟨frame.gasLeft, frame.stateGasReservoir, frame.stateGasReservoir, frame.refundCounter, 0, 0⟩
    let resMeter := match charge_gas_from_meter m0 regularGas with
      | none => none
      | some m1 => charge_state_gas_from_meter m1 stateGas
    (charge_gas frame regularGas stateGas).map (fun f => (f.gasLeft, f.stateGasReservoir)) =
      resMeter.map (fun m => (m.gasLeft, m.stateGasLeft)) := by
  dsimp only [charge_gas, charge_gas_from_meter, charge_state_gas_from_meter]
  by_cases h_spill : stateGas > frame.stateGasReservoir
  · by_cases h_reg : frame.gasLeft < regularGas
    · have h_tot : frame.gasLeft < regularGas + (stateGas - frame.stateGasReservoir) := by omega
      simp [h_spill, h_reg, h_tot]
    · by_cases h_tot : frame.gasLeft < regularGas + (stateGas - frame.stateGasReservoir)
      · have h_not_ge : ¬ (frame.stateGasReservoir ≥ stateGas) := by omega
        have h_not_sum : ¬ (frame.stateGasReservoir + (frame.gasLeft - regularGas) ≥ stateGas) := by omega
        simp [h_spill, h_reg, h_tot, h_not_ge, h_not_sum]
      · have h_not_ge : ¬ (frame.stateGasReservoir ≥ stateGas) := by omega
        have h_sum : frame.stateGasReservoir + (frame.gasLeft - regularGas) ≥ stateGas := by omega
        simp [h_spill, h_reg, h_tot, h_not_ge, h_sum]
        omega
  · by_cases h_reg : frame.gasLeft < regularGas
    · simp [h_spill, h_reg]
    · have h_ge : frame.stateGasReservoir ≥ stateGas := by omega
      have h_min : min stateGas frame.stateGasReservoir = stateGas := by omega
      simp [h_spill, h_reg, h_ge, h_min]

def incorporate_child_on_success (parent child : EvmGasFrame) : EvmGasFrame :=
  { parent with
    gasLeft := parent.gasLeft + child.gasLeft
    stateGasReservoir := child.stateGasReservoir
    refundCounter := parent.refundCounter + child.refundCounter }

def incorporate_child_on_error (parent child : EvmGasFrame) : EvmGasFrame :=
  { parent with
    gasLeft := parent.gasLeft + child.gasLeft
    stateGasReservoir := child.stateGasReservoir }

@[inline, export glamsterdam_charge_gas_ok_cabi]
def charge_gas_ok_cabi (gasLeft reservoir regularGas stateGas : UInt64) : Bool :=
  (charge_gas ⟨gasLeft.toNat, reservoir.toNat, 0⟩ regularGas.toNat stateGas.toNat).isSome

@[inline, export glamsterdam_charge_gas_left_cabi]
def charge_gas_left_cabi (gasLeft reservoir regularGas stateGas : UInt64) : UInt64 :=
  match charge_gas ⟨gasLeft.toNat, reservoir.toNat, 0⟩ regularGas.toNat stateGas.toNat with
  | some post => post.gasLeft.toUInt64
  | none => 0

@[inline, export glamsterdam_charge_gas_reservoir_cabi]
def charge_gas_reservoir_cabi (gasLeft reservoir regularGas stateGas : UInt64) : UInt64 :=
  match charge_gas ⟨gasLeft.toNat, reservoir.toNat, 0⟩ regularGas.toNat stateGas.toNat with
  | some post => post.stateGasReservoir.toUInt64
  | none => 0

end Glamsterdam.Common.ElCore
