/-
Copyright (c) 2026 Verity Labs / LFG Labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Marchand, Verity Audit Team
-/
import Glamsterdam.Common.ElCore

/-!
# Glamsterdam EIP-8246 Formal Specification and Verification
("Clear Destroyed Account Without Balance Wipe")

Pinned against `ethereum/execution-specs` @ `16898000911c1e3caa57be08509536c10ae92d3e`:
- `src/ethereum/forks/amsterdam/state_tracker.py` (`clear_account_preserving_balance:494-516`,
  `destroy_storage:518-540`, `modify_state:591-603`, `incorporate_tx_into_block:793-846`)
- `src/ethereum/forks/amsterdam/vm/instructions/system.py` (`selfdestruct:706-779`,
  `generic_create:59-186`)
- `src/ethereum/forks/amsterdam/vm/interpreter.py` (`process_create:324-392`,
  `process_top_level:235-321`)
- `src/ethereum/forks/amsterdam/fork.py` (`apply_body:783-852`,
  `process_unchecked_system_transaction:724-780`, `update_sender_state:924-963`,
  `disburse_gas_fees:965-1002`, `process_transaction:1004-1094`,
  `process_withdrawals:1096-1116`)
- `src/ethereum/forks/amsterdam/block_access_lists.py` (`update_builder_from_tx:760-825`)
- `EIPS/eip-8246.md` (`Specification:30-50`, `Backwards Compatibility:61-76`)
-/

namespace Glamsterdam.Eip8246.Spec

open Glamsterdam.Common.Prelude
open Glamsterdam.Common.MetaSpec
open Glamsterdam.Common.ElCore

/-! ## 1. Core `clear_account_preserving_balance` Theorems on `WorldSnapshot` (Single-Account Projection)
    and `TransactionState` (Multi-Account State Tracker) -/

/-- T-8246-BALANCE-PRESERVED: `clear_account_preserving_balance` never modifies
the target account's balance or recipient balance, regardless of whether the
account was created in the same transaction or marked for deletion. -/
theorem t_8246_balance_preserved (snap : WorldSnapshot) :
    (clear_account_preserving_balance snap).targetAccount.balance = snap.targetAccount.balance ∧
    (clear_account_preserving_balance snap).recipientBalance = snap.recipientBalance := by
  unfold clear_account_preserving_balance destroy_storage
  split <;> simp

/-- T-8246-SAME-TX-CREATE-DESTROY: When an account is both created in the current
transaction (`createdInTx = true`) and marked for deletion (`markedToDelete = true`),
`clear_account_preserving_balance` clears `nonce` to `0`, `codeEmpty` to `true`,
and wipes storage (`storageNonEmpty = false`) while preserving `balance`. -/
theorem t_8246_same_tx_create_destroy (snap : WorldSnapshot)
    (h_del : snap.markedToDelete = true) (h_cr : snap.createdInTx = true) :
    let post := (clear_account_preserving_balance snap).targetAccount
    post.nonce = 0 ∧ post.codeEmpty = true ∧ post.storageNonEmpty = false ∧
    post.balance = snap.targetAccount.balance := by
  simp [clear_account_preserving_balance, destroy_storage, h_del, h_cr]

/-- Exact `TransactionState` theorem (`state_tracker.py:494-516`):
`clear_account_preserving_balance_tx` preserves `get_account`'s balance for any `addr`,
clears `nonce` to `0`, resets `codeHash` to `EMPTY_CODE_HASH`, wipes `get_storage` to `0`,
and removes the account leaf (`get_account_optional = none`) if and only if its balance was `0`. -/
theorem t_8246_tx_state_clear_exact (txState : TransactionState) (addr : Address) (slot : StorageKey) :
    let post := clear_account_preserving_balance_tx txState addr
    (get_account post addr).balance = (get_account txState addr).balance ∧
    (get_account post addr).nonce = 0 ∧
    (get_account post addr).codeHash = EMPTY_CODE_HASH ∧
    get_storage post addr slot = 0 ∧
    ((get_account txState addr).balance = 0 → get_account_optional post addr = none) ∧
    ((get_account txState addr).balance > 0 → (get_account_optional post addr).isSome = true) := by
  dsimp only [clear_account_preserving_balance_tx, modify_state]
  rw [get_account_destroy_storage_tx]
  by_cases hb : (get_account txState addr).balance = 0
  · simp [destroy_account, hb, EMPTY_ACCOUNT, EMPTY_CODE_HASH]
  · have h_pos : (get_account txState addr).balance > 0 := by omega
    simp [hb, h_pos, EMPTY_CODE_HASH]

/-! ## 2. Exact `selfdestruct` Instruction Transcription (`vm/instructions/system.py:706-779`) -/

/-- Input parameters and pre-state for a single `SELFDESTRUCT` execution (`system.py:706-779`). -/
structure SelfdestructStep where
  originator : Address
  beneficiary : Address
  originatorBalance : Nat
  beneficiaryBalance : Nat
  beneficiaryAlive : Bool
  beneficiaryCold : Bool
  originatorCreatedInTx : Bool
  deriving Repr, DecidableEq, BEq

/-- Output of `selfdestruct` (`system.py:725-775`). -/
structure SelfdestructOutcome where
  execGasCharged : Nat
  stateGasCharged : Nat
  postOriginatorBalance : Nat
  postBeneficiaryBalance : Nat
  scheduledForClear : Bool
  deriving Repr, DecidableEq, BEq

/-- Validated projection of the `selfdestruct` opcode step (`vm/instructions/system.py:706-779`):
- Charges `5000` (`OPCODE_SELFDESTRUCT_BASE`) + `3000` (`COLD_ACCOUNT_ACCESS` if cold)
  + (`9000` `ACCOUNT_WRITE` + `183,600` `NEW_ACCOUNT` state gas if `!beneficiaryAlive && originatorBalance != 0`).
- Calls `move_ether(tx_state, originator, beneficiary, originator_balance)`:
  - If `originator == beneficiary`, `reduce_sender_balance` then `increase_recipient_balance` on the same
    address leaves `originatorBalance` intact (`postOriginatorBalance = postBeneficiaryBalance = originatorBalance`)!
  - If `originator != beneficiary`, `originator` becomes `0` and `beneficiary` gains `originatorBalance`.
- Adds `originator` to `accounts_to_delete` iff `originatorCreatedInTx` (`originator in tx_state.created_accounts`). -/
def exec_selfdestruct (s : SelfdestructStep) : SelfdestructOutcome :=
  let baseGas := 5000 + (if s.beneficiaryCold then 3000 else 0)
  let createsBeneficiary := !s.beneficiaryAlive && decide (s.originatorBalance ≠ 0)
  let accountWriteGas := if createsBeneficiary then 9000 else 0
  let stateGas := if createsBeneficiary then 183600 else 0
  let (postOrig, postBen) :=
    if s.originator == s.beneficiary then
      (s.originatorBalance, s.originatorBalance)
    else
      (0, s.beneficiaryBalance + s.originatorBalance)
  { execGasCharged := baseGas + accountWriteGas
    stateGasCharged := stateGas
    postOriginatorBalance := postOrig
    postBeneficiaryBalance := postBen
    scheduledForClear := s.originatorCreatedInTx }

/-- T-8246-SELFDESTRUCT-CONSERVATION: `exec_selfdestruct` conserves ETH both when
`originator ≠ beneficiary` (`postOrig + postBen = preOrig + preBen`) and when
`originator = beneficiary` (`postOrig = preOrig`, no self-burn!). -/
theorem t_8246_selfdestruct_conservation (s : SelfdestructStep) :
    (s.originator ≠ s.beneficiary →
      (exec_selfdestruct s).postOriginatorBalance + (exec_selfdestruct s).postBeneficiaryBalance =
        s.originatorBalance + s.beneficiaryBalance) ∧
    (s.originator = s.beneficiary →
      (exec_selfdestruct s).postOriginatorBalance = s.originatorBalance) := by
  unfold exec_selfdestruct
  by_cases h : s.originator = s.beneficiary <;> simp [h] <;> omega

/-- Under EIP-8246 + EIP-8037, same-tx `SELFDESTRUCT` grants zero state-gas refund. -/
def selfdestruct_state_gas_refund (_createdInTx _markedToDelete : Bool) : Nat := 0

/-- Two-step `GasMeter` trace for same-tx `CREATE` (charging `183,600` `NEW_ACCOUNT` state gas)
followed by `exec_selfdestruct` (`system.py:725-775`): unlike `SSTORE` dirty resets,
`exec_selfdestruct` never calls `credit_state_gas_refund`, so `tx_state_gas_used` retains the full
`183,600` creation state gas plus any beneficiary creation state gas. -/
def create_and_selfdestruct_meter (m0 : GasMeter) (s : SelfdestructStep) : Option GasMeter :=
  match charge_state_gas_from_meter m0 183600 with
  | none => none
  | some mAfterCreate =>
    match charge_gas_from_meter mAfterCreate (exec_selfdestruct s).execGasCharged with
    | none => none
    | some mAfterExec =>
      charge_state_gas_from_meter mAfterExec (exec_selfdestruct s).stateGasCharged

theorem charge_state_gas_from_meter_accounting (m post : GasMeter) (amount reservoir : Nat)
    (h : charge_state_gas_from_meter m amount = some post) :
    post.refundCounter = m.refundCounter ∧
    tx_state_gas_used post reservoir = tx_state_gas_used m reservoir + amount := by
  dsimp only [charge_state_gas_from_meter] at h
  split at h <;> (try split at h) <;> try contradiction
  all_goals
    simp only [Option.some.injEq] at h
    subst h
    dsimp only [tx_state_gas_used]
    refine ⟨rfl, by omega⟩

theorem charge_gas_from_meter_accounting (m post : GasMeter) (amount reservoir : Nat)
    (h : charge_gas_from_meter m amount = some post) :
    post.refundCounter = m.refundCounter ∧
    tx_state_gas_used post reservoir = tx_state_gas_used m reservoir := by
  dsimp only [charge_gas_from_meter] at h
  split at h
  · contradiction
  · simp only [Option.some.injEq] at h
    subst h
    dsimp only [tx_state_gas_used]
    exact ⟨rfl, rfl⟩

/-- T-8246-NO-STATE-GAS-REFUND: Same-tx `CREATE` + `SELFDESTRUCT` on `GasMeter` consumes the full
`183,600` (`CPSB * 120`) state gas from the `GasMeter` without any state-gas refund or `refundCounter`
credit (`post.refundCounter = m0.refundCounter` and `tx_state_gas_used post reservoir = 183600 + stateGasCharged`). -/
theorem t_8246_no_state_gas_refund (m0 post : GasMeter) (s : SelfdestructStep)
    (h_entry : m0.stateGasSpilled = 0 ∧ m0.stateGasCommittedSpill = 0)
    (h_step : create_and_selfdestruct_meter m0 s = some post) :
    post.refundCounter = m0.refundCounter ∧
    tx_state_gas_used post m0.stateGasLeft = 183600 + (exec_selfdestruct s).stateGasCharged := by
  unfold create_and_selfdestruct_meter at h_step
  rcases h_entry with ⟨h_sp, h_cm⟩
  cases h1 : charge_state_gas_from_meter m0 183600 with
  | none => rw [h1] at h_step; contradiction
  | some m1 =>
    rw [h1] at h_step
    dsimp only at h_step
    cases h2 : charge_gas_from_meter m1 (exec_selfdestruct s).execGasCharged with
    | none => rw [h2] at h_step; contradiction
    | some m2 =>
      rw [h2] at h_step
      dsimp only at h_step
      have a1 := charge_state_gas_from_meter_accounting m0 m1 183600 m0.stateGasLeft h1
      have a2 := charge_gas_from_meter_accounting m1 m2 (exec_selfdestruct s).execGasCharged m0.stateGasLeft h2
      have a3 := charge_state_gas_from_meter_accounting m2 post (exec_selfdestruct s).stateGasCharged m0.stateGasLeft h_step
      have h_init : tx_state_gas_used m0 m0.stateGasLeft = 0 := by
        simp [tx_state_gas_used, h_sp, h_cm]
      omega

/-! ## 3. Order-Independence of End-of-Transaction Account Clearing (`fork.py:1088-1089`) -/

/-- End-of-transaction loop `for address in tx_output.accounts_to_delete:` (`fork.py:1088-1089`).
We prove `OrderIndependence` (idempotence + commutativity) over `WorldSnapshot` target addresses. -/
def clear_if_match (targetAddr : Address) (snap : WorldSnapshot) (delAddr : Address) : WorldSnapshot :=
  if delAddr == targetAddr then clear_account_preserving_balance snap else snap

def clear_order_independence (targetAddr : Address) :
    OrderIndependence WorldSnapshot Address (clear_if_match targetAddr) where
  idempotent := by
    intro s x
    unfold clear_if_match clear_account_preserving_balance destroy_storage
    by_cases h : (x == targetAddr) = true
    · simp only [h, ↓reduceIte]
      split <;> simp_all
    · simp [h]
  commutative := by
    intro s x y
    unfold clear_if_match clear_account_preserving_balance destroy_storage
    by_cases hx : (x == targetAddr) = true <;> by_cases hy : (y == targetAddr) = true
    · simp only [hx, hy, ↓reduceIte]
    · simp [hx, hy]
    · simp [hx, hy]
    · simp [hx, hy]

/-! ## 4. Transaction-Level ETH Conservation (`fork.py:924-1002`) -/

/-- End-to-end EL transaction balance accounting across sender, contract, recipient,
coinbase, withdrawals, and burned base/blob fees. -/
structure ElEthAccounting where
  preSum : Nat
  withdrawals : Nat
  feesBurned : Nat
  postSum : Nat
  deriving Repr, DecidableEq, BEq

def ethConservationGate (a : ElEthAccounting) : Bool :=
  decide (a.postSum + a.feesBurned = a.preSum + a.withdrawals)

def ethConservationMetaGate : MetaGateSpec ElEthAccounting
    (fun a => a.postSum + a.feesBurned = a.preSum + a.withdrawals) where
  gate := ethConservationGate
  sound := fun a h => by simpa [ethConservationGate] using h
  complete := fun a h => by simpa [ethConservationGate] using h
  posWitness := ⟨1000, 50, 10, 1040⟩
  negWitness := ⟨1000, 50, 10, 940⟩
  nonVacuous := rfl
  tight := rfl

/-- Exact fee debit and disbursement across `update_sender_state` (`fork.py:924-963`)
and `disburse_gas_fees` (`fork.py:965-1002`):
- `update_sender_state` debits `gasLimit * effectiveGasPrice + blobFee` from `sender`.
- `disburse_gas_fees` credits `gasLeft * effectiveGasPrice` to `sender` and
  `gasUsed * (effectiveGasPrice - baseFeePerGas)` to `coinbase`.
- The burned fee is `gasUsed * baseFeePerGas + blobFee`. -/
theorem t_8246_tx_fee_settlement_conservation
    (senderBal coinbaseBal gasLimit gasUsed gasLeft effectiveGasPrice baseFeePerGas blobFee : Nat)
    (h_gas : gasUsed + gasLeft = gasLimit)
    (h_price : baseFeePerGas ≤ effectiveGasPrice)
    (h_afford : gasLimit * effectiveGasPrice + blobFee ≤ senderBal) :
    let senderAfterDebit := senderBal - (gasLimit * effectiveGasPrice + blobFee)
    let senderFinal := senderAfterDebit + gasLeft * effectiveGasPrice
    let coinbaseFinal := coinbaseBal + gasUsed * (effectiveGasPrice - baseFeePerGas)
    let burnedFee := gasUsed * baseFeePerGas + blobFee
    senderFinal + coinbaseFinal + burnedFee = senderBal + coinbaseBal := by
  have h_split :
      gasUsed * (effectiveGasPrice - baseFeePerGas) + gasUsed * baseFeePerGas =
        gasUsed * effectiveGasPrice := by
    rw [← Nat.mul_add, Nat.sub_add_cancel h_price]
  have h_limit :
      gasLeft * effectiveGasPrice + gasUsed * effectiveGasPrice =
        gasLimit * effectiveGasPrice := by
    rw [← Nat.add_mul, Nat.add_comm gasLeft gasUsed, h_gas]
  omega

/-- T-8246-ETH-CONSERVATION: 1-to-1 ETH conservation across `clear_account_preserving_balance`.
Any residual balance on a same-tx created and self-destructed contract (e.g. from
`selfdestruct(self)` or subsequent inbound transfers) is preserved in the post-state sum. -/
theorem t_8246_eth_conservation (snap : WorldSnapshot) :
    (clear_account_preserving_balance snap).targetAccount.balance +
      (clear_account_preserving_balance snap).recipientBalance =
    snap.targetAccount.balance + snap.recipientBalance := by
  have ⟨h1, h2⟩ := t_8246_balance_preserved snap
  omega

/-- Mutant M-8246-1 (pre-8246 `destroy_account` behavior that wipes `balance := 0`
during end-of-tx cleanup) is refuted by `WitnessRefuter` whenever residual balance > 0. -/
def clear_account_mutant_wipe_balance (snap : WorldSnapshot) : WorldSnapshot :=
  if snap.markedToDelete && snap.createdInTx then
    { snap with targetAccount := { nonce := 0, balance := 0, codeEmpty := true, storageNonEmpty := false } }
  else
    snap

def m_8246_1_refuter : WitnessRefuter WorldSnapshot WorldSnapshot
    (fun pre post => post.targetAccount.balance = pre.targetAccount.balance) where
  reference := clear_account_preserving_balance
  mutant := clear_account_mutant_wipe_balance
  ref_sound := fun snap => (t_8246_balance_preserved snap).1
  killWitness := { targetAccount := { balance := 100 }, createdInTx := true, markedToDelete := true }
  mutant_refuted := by decide

/-! ## 5. Formal Refuters for Discovered Upstream Bugs (`F-8246-BAL-STORAGE-CLEARS-IGNORED`
and `F-8246-UNCHECKED-SYS-TX-DROPS-ACCOUNTS-TO-DELETE`) -/

/-- State of a single `(address, slot)` entry at a given `block_access_index` for
EIP-7928 Block Access List construction (`block_access_lists.py:813-825`). -/
structure BalSlotClearState where
  indexStartVal : Nat
  priorSameIndexWrite : Option Nat
  txStorageWrite : Option Nat
  txStorageCleared : Bool
  deriving Repr, DecidableEq, BEq

/-- Validated projection (`mapping_kind: projection`) of `update_builder_from_tx`
(`block_access_lists.py:760-825` @ `16898000`):
Only iterates over `tx_state.storage_writes` (`lines 813-825`) and completely ignores `tx_state.storage_clears`
(populated by `destroy_storage` in `clear_account_preserving_balance`, `destroy_account`,
and `process_create`)! -/
def bal_recorded_post_val_buggy (s : BalSlotClearState) : Option Nat :=
  match s.txStorageWrite with
  | some postVal =>
    if postVal != s.indexStartVal then some postVal else none
  | none =>
    s.priorSameIndexWrite

/-- Patched `update_builder_from_tx`: when `txStorageCleared = true` (the address is in
`tx_state.storage_clears` and has no subsequent write in `tx_state.storage_writes`),
its effective post-transaction value is `0`, so if `indexStartVal != 0` it records `some 0`
and otherwise removes any stale `priorSameIndexWrite`. -/
def bal_recorded_post_val_patched (s : BalSlotClearState) : Option Nat :=
  match s.txStorageWrite with
  | some postVal =>
    if postVal != s.indexStartVal then some postVal else none
  | none =>
    if s.txStorageCleared then
      if s.indexStartVal != 0 then some 0 else none
    else
      s.priorSameIndexWrite

/-- Actual post-transaction storage value in `BlockState` after `incorporate_tx_into_block`
(`state_tracker.py:827-835`). -/
def actual_block_post_storage (s : BalSlotClearState) : Nat :=
  match s.txStorageWrite with
  | some postVal => postVal
  | none =>
    if s.txStorageCleared then 0
    else s.priorSameIndexWrite.getD s.indexStartVal

/-- Specification of BAL storage-change consistency: the BAL entry recorded for the current
`block_access_index` equals `some postVal` iff `postVal ≠ indexStartVal`, and `none` otherwise. -/
def bal_storage_consistent (s : BalSlotClearState) (recorded : Option Nat) : Prop :=
  let postVal := actual_block_post_storage s
  if postVal != s.indexStartVal then
    recorded = some postVal
  else
    recorded = none

/-- Theorem: `bal_recorded_post_val_patched` satisfies `bal_storage_consistent` for all states
where `priorSameIndexWrite` was consistent prior to the clear. -/
theorem t_8246_bal_patched_sound (s : BalSlotClearState)
    (h_prior : s.txStorageWrite = none → s.txStorageCleared = false →
      (if s.priorSameIndexWrite.getD s.indexStartVal != s.indexStartVal then
        s.priorSameIndexWrite = some (s.priorSameIndexWrite.getD s.indexStartVal)
      else s.priorSameIndexWrite = none)) :
    bal_storage_consistent s (bal_recorded_post_val_patched s) := by
  unfold bal_storage_consistent actual_block_post_storage bal_recorded_post_val_patched
  cases hw : s.txStorageWrite with
  | some v =>
    dsimp only
    split <;> rfl
  | none =>
    cases hc : s.txStorageCleared with
    | true =>
      by_cases h0 : s.indexStartVal = 0
      · simp [h0]
      · have h_neq : (0 != s.indexStartVal) = true := by
          rw [bne_iff_ne]; exact Ne.symm h0
        have h_neq2 : (s.indexStartVal != 0) = true := by
          rw [bne_iff_ne]; exact h0
        simp [h_neq, h_neq2]
    | false =>
      have hp := h_prior hw hc
      simpa using hp

/-- Explicit `WitnessRefuter` for `F-8246-BAL-STORAGE-CLEARS-IGNORED`:
When a pre-existing storage slot has `indexStartVal = 42` and is wiped by `destroy_storage`
(`txStorageCleared = true`, `txStorageWrite = none`), `bal_recorded_post_val_buggy` records
`none` instead of `some 0`! -/
def f_8246_bal_storage_clears_ignored_refuter :
    WitnessRefuter BalSlotClearState (Option Nat)
      (fun s rec => s.txStorageWrite = none ∧ s.txStorageCleared = true →
        bal_storage_consistent s rec) where
  reference := bal_recorded_post_val_patched
  mutant := bal_recorded_post_val_buggy
  ref_sound := by
    intro s ⟨hw, hc⟩
    apply t_8246_bal_patched_sound
    intro _ h_false
    rw [hc] at h_false
    contradiction
  killWitness := {
    indexStartVal := 42
    priorSameIndexWrite := none
    txStorageWrite := none
    txStorageCleared := true
  }
  mutant_refuted := by
    unfold bal_storage_consistent actual_block_post_storage bal_recorded_post_val_buggy
    decide

/-- Two-Transaction Cross-Block BAL vs `BlockState` Desynchronization Theorem on `TransactionState`
and `BlockState` (`state_tracker.py:827-835` vs `block_access_lists.py:813-825`):
- In `Tx1`, contract `addr` is created (`CREATE2`), writes slot `slot := val` (`val ≠ 0`), and
  commits (`b1 := incorporate_tx_into_block tx1`).
- In `Tx2`, `addr` is destroyed or cleared via `destroy_storage_tx` (`b2 := incorporate_tx_into_block tx2`).
- Then `get_block_storage b2 addr slot = 0` (the post-block state has wiped the slot to `0`),
  whereas `tx2.storageWrites` has no entry for `(addr, slot)` because `destroy_storage_tx` moved
  all keys to `storageReads` and recorded `addr` only in `tx2.storageClears`, leaving `Tx1`'s
  non-zero `val` as the final value in the Block Access List! -/
theorem t_8246_bal_tx_block_state_desync (pre : PreState) (addr : Address) (slot : StorageKey) (val : StorageVal) :
    let b0 : BlockState := { preState := pre }
    let tx1 : TransactionState := set_storage { parent := b0 } addr slot val
    let b1 : BlockState := incorporate_tx_into_block tx1
    let tx2 : TransactionState := destroy_storage_tx { parent := b1 } addr
    let b2 : BlockState := incorporate_tx_into_block tx2
    get_block_storage b1 addr slot = val ∧
    get_block_storage b2 addr slot = 0 ∧
    tx2.storageWrites.find? (fun p => p.1 == (addr, slot)) = none ∧
    tx2.storageClears.contains addr = true := by
  simp [set_storage, incorporate_tx_into_block, destroy_storage_tx, get_block_storage]

/-- Lemma: `clear_account_preserving_balance_tx` has the exact same `storageWrites` and `storageClears`
effects as `destroy_storage_tx` (since the subsequent `modify_state` only updates `accountWrites` or
runs an idempotent second `destroy_storage_tx` when `balance == 0`). -/
@[simp]
theorem clear_account_preserving_balance_tx_storage_effects (txState : TransactionState) (addr : Address) :
    (clear_account_preserving_balance_tx txState addr).storageWrites =
      (destroy_storage_tx txState addr).storageWrites ∧
    (clear_account_preserving_balance_tx txState addr).storageClears =
      (destroy_storage_tx txState addr).storageClears := by
  dsimp only [clear_account_preserving_balance_tx, modify_state, destroy_account]
  split
  · have hc := storageClears_destroy_storage_tx_contains txState addr
    dsimp only [set_account, destroy_storage_tx] at *
    rw [hc]
    simp [List.filter_filter]
  · exact ⟨rfl, rfl⟩

/-- End-to-end theorem (`t_8246_storage_clears_recorded_in_bal`) connecting `destroy_storage_tx`
(and `clear_account_preserving_balance_tx` via `clear_account_preserving_balance_tx_storage_effects`)
and `incorporate_tx_into_block` (`state_tracker.py:494-540, 793-846`) to `update_builder_from_tx`
(`block_access_lists.py:760-825`):
When `Tx1` writes a non-zero storage slot `val > 0` (`b1 := incorporate_tx_into_block tx1`) and `Tx2`
wipes `addr`'s storage via `destroy_storage_tx` (`b2 := incorporate_tx_into_block tx2`),
the resulting BAL slot state `balState` extracted from `tx2` has `bal_recorded_post_val_patched balState = some 0`
(matching `get_block_storage b2 addr slot = 0` and satisfying `bal_storage_consistent`), whereas
`bal_recorded_post_val_buggy balState = none`! -/
theorem t_8246_storage_clears_recorded_in_bal
    (pre : PreState) (addr : Address) (slot : StorageKey) (val : Nat) (h_pos : val > 0) :
    let b0 : BlockState := { preState := pre }
    let tx1 : TransactionState := set_storage { parent := b0 } addr slot val
    let b1 : BlockState := incorporate_tx_into_block tx1
    let tx2 : TransactionState := destroy_storage_tx { parent := b1 } addr
    let b2 : BlockState := incorporate_tx_into_block tx2
    let balState : BalSlotClearState :=
      { indexStartVal := get_block_storage b1 addr slot
        priorSameIndexWrite := none
        txStorageWrite := (tx2.storageWrites.find? (fun p => p.1 == (addr, slot))).map Prod.snd
        txStorageCleared := tx2.storageClears.contains addr }
    get_block_storage b2 addr slot = 0 ∧
    bal_recorded_post_val_patched balState = some 0 ∧
    bal_recorded_post_val_buggy balState = none ∧
    bal_storage_consistent balState (bal_recorded_post_val_patched balState) := by
  have h_ne : val ≠ 0 := Nat.ne_of_gt h_pos
  have h_ne_symm : 0 ≠ val := Ne.symm h_ne
  simp [set_storage, incorporate_tx_into_block, destroy_storage_tx, get_block_storage,
    bal_recorded_post_val_patched, bal_recorded_post_val_buggy, bal_storage_consistent,
    actual_block_post_storage, h_ne, h_ne_symm]

/-- Validated projection (`mapping_kind: projection`) of `process_unchecked_system_transaction`
(`fork.py:724-780` @ `16898000`):
Executes `process_top_level` and calls `incorporate_tx_into_block(system_tx_state, ...)` directly,
omitting the `for address in tx_output.accounts_to_delete: clear_account_preserving_balance(...)`
cleanup loop present in `process_transaction` (`fork.py:1088-1089`). -/
def finalize_unchecked_sys_tx_v16898000 (frame : EvmFrame) (target : Address) : TransactionState :=
  let _ := target
  frame.txState

/-- Full list-fold of `for address in tx_output.accounts_to_delete: clear_account_preserving_balance(tx_state, address)`
(`fork.py:1088-1089`). -/
def clear_accounts_to_delete_tx (txState : TransactionState) (accountsToDelete : List Address) : TransactionState :=
  accountsToDelete.foldl clear_account_preserving_balance_tx txState

/-- Target-address projection of patched `process_unchecked_system_transaction` (`fork.py:724-780`):
clears `target` via `clear_account_preserving_balance_tx` whenever `target ∈ frame.accountsToDelete`
(coinciding with `clear_accounts_to_delete_tx frame.txState [target]` when `frame.accountsToDelete = [target]`). -/
def finalize_unchecked_sys_tx_patched (frame : EvmFrame) (target : Address) : TransactionState :=
  if frame.accountsToDelete.contains target then
    clear_account_preserving_balance_tx frame.txState target
  else
    frame.txState

/-- Explicit `WitnessRefuter` for `F-8246-UNCHECKED-SYS-TX-DROPS-ACCOUNTS-TO-DELETE`:
When a system call spawns a child contract `0xbeef` that self-destructs in the same transaction
(`0xbeef ∈ frame.accountsToDelete`), `finalize_unchecked_sys_tx_v16898000` leaves `0xbeef`'s code
and storage intact instead of clearing them while preserving balance. -/
def f_8246_unchecked_sys_tx_drops_deletes_refuter :
    WitnessRefuter (EvmFrame × Address) TransactionState
      (fun ⟨pre, addr⟩ post =>
        pre.accountsToDelete.contains addr = true →
          (get_account post addr).codeHash = EMPTY_CODE_HASH ∧
          (get_account post addr).nonce = 0 ∧
          (get_account post addr).balance = (get_account pre.txState addr).balance) where
  reference := fun ⟨pre, addr⟩ => finalize_unchecked_sys_tx_patched pre addr
  mutant := fun ⟨pre, addr⟩ => finalize_unchecked_sys_tx_v16898000 pre addr
  ref_sound := by
    intro ⟨pre, addr⟩ h_mem
    dsimp [finalize_unchecked_sys_tx_patched]
    rw [h_mem]
    simp only [↓reduceIte]
    have h_clear := t_8246_tx_state_clear_exact pre.txState addr 0
    exact ⟨h_clear.2.2.1, h_clear.2.1, h_clear.1⟩
  killWitness := (
    { txState := set_account {} 0xbeef (some { nonce := 1, balance := 777, codeHash := 0x1234, codeEmpty := false })
      gasMeter := { gasLeft := 0, stateGasLeft := 0, stateGasBaseline := 0 }
      accountsToDelete := [0xbeef] },
    0xbeef
  )
  mutant_refuted := by decide

@[inline, export glamsterdam_eip8246_eth_conservation_cabi]
def eip8246_eth_conservation_cabi (preSum withdrawals feesBurned postSum : UInt64) : Bool :=
  ethConservationGate ⟨preSum.toNat, withdrawals.toNat, feesBurned.toNat, postSum.toNat⟩

@[inline, export glamsterdam_eip8246_selfdestruct_exec_gas_cabi]
def eip8246_selfdestruct_exec_gas_cabi (origBal benAlive benCold : UInt64) : UInt64 :=
  let s : SelfdestructStep := {
    originator := 1, beneficiary := 2, originatorBalance := origBal.toNat,
    beneficiaryBalance := 0, beneficiaryAlive := benAlive != 0,
    beneficiaryCold := benCold != 0, originatorCreatedInTx := false
  }
  (exec_selfdestruct s).execGasCharged.toUInt64

@[inline, export glamsterdam_eip8246_selfdestruct_state_gas_cabi]
def eip8246_selfdestruct_state_gas_cabi (origBal benAlive benCold : UInt64) : UInt64 :=
  let s : SelfdestructStep := {
    originator := 1, beneficiary := 2, originatorBalance := origBal.toNat,
    beneficiaryBalance := 0, beneficiaryAlive := benAlive != 0,
    beneficiaryCold := benCold != 0, originatorCreatedInTx := false
  }
  (exec_selfdestruct s).stateGasCharged.toUInt64

/-! ## 6. Multi-Account End-of-Transaction Clearing and Block-Level ETH Supply
    (`state_tracker.py:494-516`, `fork.py:783-852, 924-1002, 1088-1089, 1096-1116`) -/

/-- Total EL ETH held by the explicitly tracked `addrs` in a `TransactionState`. -/
def sum_balances_tx (st : TransactionState) (addrs : List Address) : Nat :=
  (addrs.map (fun a => (get_account st a).balance)).sum

/-- Total EL ETH held by the explicitly tracked `addrs` in a `BlockState`. -/
def sum_balances_block (bs : BlockState) (addrs : List Address) : Nat :=
  sum_balances_tx { parent := bs } addrs

/-- Lookup in a filtered association list when `target ≠ addr`. -/
theorem find?_filter_ne_addr {α : Type} (xs : List (Address × α)) (addr target : Address)
    (h_ne : target ≠ addr) :
    (xs.filter (fun p => p.1 != addr)).find? (fun p => p.1 == target) =
      xs.find? (fun p => p.1 == target) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    by_cases h_hd : hd.1 = addr
    · have h_neq : (hd.1 != addr) = false := by simp [h_hd]
      have h_t : (hd.1 == target) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        exact h_ne (heq.symm.trans h_hd)
      simp only [List.filter, h_neq, List.find?, h_t, ih]
    · have h_neq : (hd.1 != addr) = true := by
        rw [bne_iff_ne]
        exact h_hd
      simp only [List.filter, h_neq, List.find?]
      cases hd.1 == target
      · exact ih
      · rfl

/-- `set_account` only changes the account at `addr`; every other account lookup is unchanged. -/
theorem get_account_optional_set_account_ne (st : TransactionState) (addr target : Address)
    (acc : Option Account) (h_ne : target ≠ addr) :
    get_account_optional (set_account st addr acc) target = get_account_optional st target := by
  dsimp only [set_account, get_account_optional, get_pre_state_account_optional]
  have h_beq : (addr == target) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h => h_ne h.symm
  simp only [List.find?, h_beq, find?_filter_ne_addr st.accountWrites addr target h_ne]

/-- `get_account` on a non-target address is unchanged by `set_account`. -/
theorem get_account_set_account_ne (st : TransactionState) (addr target : Address)
    (acc : Option Account) (h_ne : target ≠ addr) :
    get_account (set_account st addr acc) target = get_account st target := by
  dsimp only [get_account]
  rw [get_account_optional_set_account_ne st addr target acc h_ne]

/-- `modify_state` preserves every non-target account balance. -/
theorem get_account_modify_state_ne (st : TransactionState) (addr target : Address)
    (f : Account → Account) (h_ne : target ≠ addr) :
    (get_account (modify_state st addr f) target).balance = (get_account st target).balance := by
  dsimp only [modify_state, destroy_account]
  split
  · rw [get_account_set_account_ne _ addr target none h_ne]
    rw [get_account_destroy_storage_tx]
    rw [get_account_set_account_ne _ addr target _ h_ne]
  · rw [get_account_set_account_ne _ addr target _ h_ne]

/-- T-8246-CLEAR-PRESERVES-ANY-ACCOUNT-BALANCE: the exact `TransactionState` transcription of
`clear_account_preserving_balance` preserves the balance of every account, not merely the cleared one. -/
theorem t_8246_clear_preserves_any_account_balance (st : TransactionState) (addr target : Address) :
    (get_account (clear_account_preserving_balance_tx st addr) target).balance =
      (get_account st target).balance := by
  by_cases h_eq : target = addr
  · subst h_eq
    exact (t_8246_tx_state_clear_exact st target 0).1
  · dsimp only [clear_account_preserving_balance_tx]
    rw [get_account_modify_state_ne _ addr target _ h_eq]
    rw [get_account_destroy_storage_tx]

/-- Sum form of `t_8246_clear_preserves_any_account_balance`. -/
theorem sum_balances_tx_clear (st : TransactionState) (addr : Address) (addrs : List Address) :
    sum_balances_tx (clear_account_preserving_balance_tx st addr) addrs =
      sum_balances_tx st addrs := by
  induction addrs with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [sum_balances_tx, List.map, List.sum_cons]
    rw [t_8246_clear_preserves_any_account_balance]
    dsimp only [sum_balances_tx] at ih
    rw [ih]

/-- T-8246-CLEAR-ACCOUNTS-LIST-PRESERVES-ALL-BALANCES: the entire end-of-transaction
`accounts_to_delete` fold preserves every tracked balance for arbitrary deletion and tracked lists. -/
theorem t_8246_clear_accounts_list_preserves_all_balances
    (st : TransactionState) (accountsToDelete addrs : List Address) :
    sum_balances_tx (clear_accounts_to_delete_tx st accountsToDelete) addrs =
      sum_balances_tx st addrs := by
  induction accountsToDelete generalizing st with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [clear_accounts_to_delete_tx, List.foldl]
    have h_step := ih (clear_account_preserving_balance_tx st a)
    dsimp only [clear_accounts_to_delete_tx] at h_step
    rw [h_step]
    exact sum_balances_tx_clear st a addrs

/-- Keyed association-list ledger for the stateful multi-account block accounting projection. -/
abbrev EthLedger := List (Address × Account)

/-- Deduplicate an `EthLedger` by keeping the first active binding per address, matching
`find?` semantics on arbitrary un-normalized association lists without any `Nodup` hypothesis. -/
def ledger_dedup (led : EthLedger) : EthLedger :=
  match led with
  | [] => []
  | (a, acc) :: tl => (a, acc) :: (ledger_dedup tl).filter (fun p => p.1 != a)

/-- Account lookup in an `EthLedger`; absent addresses return `EMPTY_ACCOUNT`. -/
def ledger_account (led : EthLedger) (addr : Address) : Account :=
  match (ledger_dedup led).find? (fun p => p.1 == addr) with
  | some (_, acc) => acc
  | none => EMPTY_ACCOUNT

/-- Balance lookup in an `EthLedger`; absent addresses hold zero ETH. -/
def ledger_balance (led : EthLedger) (addr : Address) : Nat :=
  (ledger_account led addr).balance

/-- Total EL ETH across all unique active addresses in `led`. -/
def ledger_total (led : EthLedger) : Nat :=
  ((ledger_dedup led).map (fun p => p.2.balance)).sum

/-- Insert or replace one address account while filtering shadowed bindings. -/
def ledger_put_account (led : EthLedger) (addr : Address) (acc : Account) : EthLedger :=
  (addr, acc) :: (ledger_dedup led).filter (fun p => p.1 != addr)

/-- Update the balance of `addr` in `led` while preserving its other account fields. -/
def ledger_set (led : EthLedger) (addr : Address) (balance : Nat) : EthLedger :=
  ledger_put_account led addr { ledger_account led addr with balance := balance }

/-- End-of-transaction EIP-8246 account clearing on `EthLedger`, mirroring
`clear_account_preserving_balance` (`state_tracker.py:494-516`). -/
def ledger_clear_account (led : EthLedger) (addr : Address) : EthLedger :=
  let acc := ledger_account led addr
  ledger_put_account led addr
    { acc with nonce := 0, codeHash := EMPTY_CODE_HASH, codeEmpty := true, storageNonEmpty := false }

/-- Fold `ledger_clear_account` across `accounts_to_delete` (`fork.py:1088-1089`). -/
def ledger_clear_accounts_list (led : EthLedger) (accountsToDelete : List Address) : EthLedger :=
  accountsToDelete.foldl ledger_clear_account led

/-- Filtering a list by `p.1 != a` removes every occurrence of `a`. -/
theorem find?_filter_self_eq_none {α : Type} (xs : List (Address × α)) (addr : Address) :
    (xs.filter (fun p => p.1 != addr)).find? (fun p => p.1 == addr) = none := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    by_cases h_hd : hd.1 = addr
    · have h_neq : (hd.1 != addr) = false := by simp [h_hd]
      simp only [List.filter, h_neq, ih]
    · have h_neq : (hd.1 != addr) = true := by
        rw [bne_iff_ne]
        exact h_hd
      have h_beq : (hd.1 == addr) = false := by
        rw [beq_eq_false_iff_ne]
        exact h_hd
      simp only [List.filter, h_neq, List.find?, h_beq, ih]

/-- Key structural invariant: `ledger_dedup` commutes with key filtering. -/
theorem filter_dedup_comm (xs : EthLedger) (a : Address) :
    ledger_dedup (xs.filter (fun p => p.1 != a)) =
      (ledger_dedup xs).filter (fun p => p.1 != a) := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    by_cases hk : k = a
    · subst hk
      simp only [List.filter, bne_self_eq_false, ledger_dedup, List.filter_filter]
      rw [ih]
      congr 1
      funext p
      cases p.1 != k <;> rfl
    · have h_ka : (k != a) = true := by
        rw [bne_iff_ne]
        exact hk
      simp only [List.filter, h_ka, ledger_dedup, ih, List.filter_filter]
      congr 2
      funext p
      cases p.1 != a <;> cases p.1 != k <;> rfl

/-- `ledger_dedup` is idempotent on every `EthLedger`. -/
theorem ledger_dedup_idem (ys : EthLedger) : ledger_dedup (ledger_dedup ys) = ledger_dedup ys := by
  induction ys with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    dsimp only [ledger_dedup]
    rw [filter_dedup_comm, ih, List.filter_filter]
    simp

/-- `ledger_dedup` is idempotent on `ledger_put_account`. -/
theorem ledger_dedup_put_account (led : EthLedger) (addr : Address) (acc : Account) :
    ledger_dedup (ledger_put_account led addr acc) = ledger_put_account led addr acc := by
  dsimp only [ledger_put_account, ledger_dedup]
  rw [filter_dedup_comm, ledger_dedup_idem, List.filter_filter]
  simp

/-- Predicate asserting that no address appears more than once in `xs`. -/
def ledger_unique_keys : EthLedger → Prop
  | [] => True
  | (a, _) :: tl => (tl.find? (fun p => p.1 == a) = none) ∧ ledger_unique_keys tl

/-- Filtering preserves `ledger_unique_keys`. -/
theorem ledger_unique_keys_filter (xs : EthLedger) (addr : Address)
    (h_u : ledger_unique_keys xs) :
    ledger_unique_keys (xs.filter (fun p => p.1 != addr)) := by
  induction xs with
  | nil => trivial
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    rcases h_u with ⟨h_none, h_tl⟩
    by_cases hk : k = addr
    · subst hk
      simp only [List.filter, bne_self_eq_false]
      exact ih h_tl
    · have h_neq : (k != addr) = true := by
        rw [bne_iff_ne]
        exact hk
      simp only [List.filter, h_neq, ledger_unique_keys]
      rw [find?_filter_ne_addr tl addr k hk]
      exact ⟨h_none, ih h_tl⟩

/-- `ledger_dedup` always produces a list satisfying `ledger_unique_keys`. -/
theorem ledger_unique_keys_dedup (led : EthLedger) : ledger_unique_keys (ledger_dedup led) := by
  induction led with
  | nil => trivial
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    dsimp only [ledger_dedup, ledger_unique_keys]
    exact ⟨find?_filter_self_eq_none (ledger_dedup tl) k, ledger_unique_keys_filter (ledger_dedup tl) k ih⟩

/-- When `xs.find? (fun p => p.1 == addr) = none`, filtering by `p.1 != addr` leaves `xs` unchanged. -/
theorem filter_eq_self_of_find?_none (xs : EthLedger) (addr : Address)
    (h_none : xs.find? (fun p => p.1 == addr) = none) :
    xs.filter (fun p => p.1 != addr) = xs := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    dsimp only [List.find?] at h_none
    cases h_beq : (k == addr)
    · rw [h_beq] at h_none
      have h_neq : (k != addr) = true := by
        rw [bne_iff_ne]
        rw [beq_eq_false_iff_ne] at h_beq
        exact h_beq
      simp only [List.filter, h_neq]
      rw [ih h_none]
    · rw [h_beq] at h_none
      contradiction

/-- Helper lookup matching `ledger_account` on an arbitrary `EthLedger` list. -/
def list_lookup_account (xs : EthLedger) (addr : Address) : Account :=
  match xs.find? (fun p => p.1 == addr) with
  | some (_, acc) => acc
  | none => EMPTY_ACCOUNT

/-- Sum decomposition on any `xs` satisfying `ledger_unique_keys`. -/
theorem sum_filter_unique_eq (xs : EthLedger) (addr : Address) (h_u : ledger_unique_keys xs) :
    ((xs.filter (fun p => p.1 != addr)).map (fun p => p.2.balance)).sum +
      (list_lookup_account xs addr).balance =
      (xs.map (fun p => p.2.balance)).sum := by
  induction xs with
  | nil => simp [list_lookup_account, EMPTY_ACCOUNT]
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    rcases h_u with ⟨h_none, h_tl⟩
    by_cases hk : k = addr
    · subst hk
      have h_lk : list_lookup_account ((k, v) :: tl) k = v := by
        simp [list_lookup_account]
      simp only [List.filter, bne_self_eq_false, List.map, List.sum_cons, h_lk]
      rw [filter_eq_self_of_find?_none tl k h_none]
      omega
    · have h_neq : (k != addr) = true := by
        rw [bne_iff_ne]
        exact hk
      have h_beq : (k == addr) = false := by
        rw [beq_eq_false_iff_ne]
        exact hk
      have h_lk : list_lookup_account ((k, v) :: tl) addr = list_lookup_account tl addr := by
        simp [list_lookup_account, h_beq]
      simp only [List.filter, h_neq, List.map, List.sum_cons, h_lk]
      have h_ih := ih h_tl
      omega

/-- Sum decomposition on a deduplicated list: removing `addr` subtracts its unique balance. -/
theorem sum_filter_dedup_eq (led : EthLedger) (addr : Address) :
    (((ledger_dedup led).filter (fun p => p.1 != addr)).map (fun p => p.2.balance)).sum +
      ledger_balance led addr = ledger_total led := by
  exact sum_filter_unique_eq (ledger_dedup led) addr (ledger_unique_keys_dedup led)

/-- Total-balance equation for `ledger_put_account` on arbitrary ledgers (zero `Nodup` hypothesis). -/
theorem ledger_total_put_account (led : EthLedger) (addr : Address) (acc : Account) :
    ledger_total (ledger_put_account led addr acc) + ledger_balance led addr =
      ledger_total led + acc.balance := by
  have h_sum := sum_filter_dedup_eq led addr
  unfold ledger_total at h_sum ⊢
  rw [ledger_dedup_put_account]
  dsimp only [ledger_put_account, List.map, List.sum_cons]
  omega

/-- Total-balance equation for `ledger_set` on arbitrary ledgers. -/
theorem ledger_total_set (led : EthLedger) (addr : Address) (balance : Nat) :
    ledger_total (ledger_set led addr balance) + ledger_balance led addr =
      ledger_total led + balance := by
  exact ledger_total_put_account led addr { ledger_account led addr with balance := balance }

/-- EIP-8246 `ledger_clear_account` preserves `ledger_total` identically. -/
theorem ledger_total_clear_account (led : EthLedger) (addr : Address) :
    ledger_total (ledger_clear_account led addr) = ledger_total led := by
  dsimp only [ledger_clear_account]
  have h := ledger_total_put_account led addr
    { ledger_account led addr with
      nonce := 0, codeHash := EMPTY_CODE_HASH, codeEmpty := true, storageNonEmpty := false }
  dsimp only [ledger_balance] at h
  omega

/-- Folding `ledger_clear_account` across `accounts_to_delete` preserves `ledger_total`. -/
theorem ledger_total_clear_accounts_list (led : EthLedger) (accountsToDelete : List Address) :
    ledger_total (ledger_clear_accounts_list led accountsToDelete) = ledger_total led := by
  induction accountsToDelete generalizing led with
  | nil => rfl
  | cons a rest ih =>
    dsimp only [ledger_clear_accounts_list, List.foldl]
    have h_tail := ih (ledger_clear_account led a)
    dsimp only [ledger_clear_accounts_list] at h_tail
    rw [h_tail, ledger_total_clear_account]

/-- Lookup of `ledger_balance` after `ledger_put_account`. -/
theorem ledger_balance_put_account (led : EthLedger) (addr target : Address) (acc : Account) :
    ledger_balance (ledger_put_account led addr acc) target =
      if target = addr then acc.balance else ledger_balance led target := by
  dsimp only [ledger_balance, ledger_account]
  rw [ledger_dedup_put_account]
  dsimp only [ledger_put_account]
  by_cases h : target = addr
  · subst h
    simp only [List.find?, beq_self_eq_true, ↓reduceIte]
  · have h_beq : (addr == target) = false := by
      rw [beq_eq_false_iff_ne]
      exact fun heq => h heq.symm
    have h_find := find?_filter_ne_addr (ledger_dedup led) addr target h
    simp only [List.find?, h_beq, h_find, h, ↓reduceIte]

/-- Lookup of `ledger_balance` after `ledger_set`. -/
theorem ledger_balance_set (led : EthLedger) (addr target : Address) (balance : Nat) :
    ledger_balance (ledger_set led addr balance) target =
      if target = addr then balance else ledger_balance led target := by
  exact ledger_balance_put_account led addr target { ledger_account led addr with balance := balance }

/-- Balance-guarded wrapper over `move_ether` (`state_tracker.py:606-638`): upstream `move_ether`
raises `AssertionError` (`reduce_sender_balance`, lines `628-630`) when `sender.balance < amount`
and is only invoked after the caller's balance guard (`process_call` / `regularTx`). As a total
helper, `ledger_safe_transfer` transfers `amount` iff `ledger_balance led sender ≥ amount` and
leaves `led` unchanged otherwise. -/
def ledger_safe_transfer (led : EthLedger) (sender recipient : Address) (amount : Nat) : EthLedger :=
  if ledger_balance led sender < amount then
    led
  else
    let s1 := ledger_set led sender (ledger_balance led sender - amount)
    ledger_set s1 recipient (ledger_balance s1 recipient + amount)

/-- `ledger_safe_transfer` conserves `ledger_total` unconditionally (both when `sender = recipient`
and when `sender ≠ recipient`, and whether `sender` has sufficient balance or not). -/
theorem ledger_safe_transfer_total (led : EthLedger) (sender recipient : Address) (amount : Nat) :
    ledger_total (ledger_safe_transfer led sender recipient amount) = ledger_total led := by
  dsimp only [ledger_safe_transfer]
  by_cases h_lt : ledger_balance led sender < amount
  · simp only [h_lt, ↓reduceIte]
  · simp only [h_lt, ↓reduceIte]
    have h1 := ledger_total_set led sender (ledger_balance led sender - amount)
    have h2 := ledger_total_set (ledger_set led sender (ledger_balance led sender - amount))
      recipient (ledger_balance (ledger_set led sender (ledger_balance led sender - amount)) recipient + amount)
    omega

/-- Concrete `apply_body` balance-accounting steps (`fork.py:783-852`):
- `regularTx`: models `process_transaction` (`fork.py:1004-1094`): upfront gas deduction
  (`(gasUsed + gasLeft) * (baseFeePerGas + priorityTip) + blobFee` in `update_sender_state` at
  `fork.py:924-963`), value transfer (`recipient`), `SELFDESTRUCT` transfer (`sdOriginator` to
  `sdBeneficiary`), unused-gas refund (`gasLeft * (baseFeePerGas + priorityTip)` to `sender`) and
  priority-fee tip (`gasUsed * priorityTip` to `coinbase` in `disburse_gas_fees` at `fork.py:965-1002`),
  base-fee + blob-fee burn (`gasUsed * baseFeePerGas + blobFee`), and end-of-tx
  `accounts_to_delete` EIP-8246 clearing (`fork.py:1088-1089`).
- `clWithdrawal`: models `process_withdrawals` (`fork.py:1096-1116`), crediting `amount` to
  `recipient` via `create_ether` (`state_tracker.py:640-660`).
- `uncheckedSystemTx`: models `process_unchecked_system_transaction` (`fork.py:724-780`) with zero
  value transfer and zero fee burn, plus optional internal transfer and EIP-8246 clear list. -/
inductive BlockAccountStep where
  | regularTx (sender recipient coinbase sdOriginator sdBeneficiary : Address)
      (gasUsed gasLeft baseFeePerGas priorityTip blobFee value sdAmount : Nat)
      (accountsToDelete : List Address)
  | clWithdrawal (recipient : Address) (amount : Nat)
  | uncheckedSystemTx (caller target : Address) (accountsToDelete : List Address)
  deriving Repr, DecidableEq, BEq

/-- Execute one `BlockAccountStep` on `EthLedger`; for `regularTx`, `check_transaction` enforces
that `sender` can afford `upfrontFee + value`, else the step does not mutate balances. -/
def apply_block_account_step (led : EthLedger) (step : BlockAccountStep) : EthLedger :=
  match step with
  | .regularTx s r c sdOrig sdBen gasUsed gasLeft baseFee tip blobFee value sdAmt toDel =>
    let effPrice := baseFee + tip
    let upfrontFee := (gasUsed + gasLeft) * effPrice + blobFee
    if ledger_balance led s < upfrontFee + value then
      led
    else
      let l1 := ledger_set led s (ledger_balance led s - upfrontFee)
      let l2 := ledger_safe_transfer l1 s r value
      let l3 := ledger_safe_transfer l2 sdOrig sdBen sdAmt
      let l4 := ledger_set l3 s (ledger_balance l3 s + gasLeft * effPrice)
      let l5 := ledger_set l4 c (ledger_balance l4 c + gasUsed * tip)
      ledger_clear_accounts_list l5 toDel
  | .clWithdrawal recipient amount =>
    ledger_set led recipient (ledger_balance led recipient + amount)
  | .uncheckedSystemTx caller target toDel =>
    let l1 := ledger_safe_transfer led caller target 0
    ledger_clear_accounts_list l1 toDel

/-- Independently tracked EL ETH fee burn (`gasUsed * baseFeePerGas + blobFee` when the regular tx
is affordable under `check_transaction`, `0` otherwise and `0` on withdrawals / system txs). -/
def block_step_burned (led : EthLedger) (step : BlockAccountStep) : Nat :=
  match step with
  | .regularTx s _ _ _ _ gasUsed gasLeft baseFee tip blobFee value _ _ =>
    let upfrontFee := (gasUsed + gasLeft) * (baseFee + tip) + blobFee
    if ledger_balance led s < upfrontFee + value then 0 else gasUsed * baseFee + blobFee
  | .clWithdrawal _ _ => 0
  | .uncheckedSystemTx _ _ _ => 0

/-- Independently tracked CL-to-EL withdrawal inflow (`process_withdrawals` at `fork.py:1096-1116`). -/
def block_step_cl_inflow (step : BlockAccountStep) : Nat :=
  match step with
  | .regularTx _ _ _ _ _ _ _ _ _ _ _ _ _ => 0
  | .clWithdrawal _ amount => amount
  | .uncheckedSystemTx _ _ _ => 0

/-- Single-step EL supply conservation across all three `apply_body` step variants. -/
theorem apply_block_account_step_conserved (led : EthLedger) (step : BlockAccountStep) :
    ledger_total (apply_block_account_step led step) + block_step_burned led step =
      ledger_total led + block_step_cl_inflow step := by
  cases step with
  | regularTx s r c sdOrig sdBen gasUsed gasLeft baseFee tip blobFee value sdAmt toDel =>
    dsimp only [apply_block_account_step, block_step_burned, block_step_cl_inflow]
    by_cases h_aff : ledger_balance led s < (gasUsed + gasLeft) * (baseFee + tip) + blobFee + value
    · simp only [h_aff, ↓reduceIte, Nat.add_zero]
    · simp only [h_aff, ↓reduceIte]
      let effPrice := baseFee + tip
      let upfront := (gasUsed + gasLeft) * effPrice + blobFee
      let l1 := ledger_set led s (ledger_balance led s - upfront)
      let l2 := ledger_safe_transfer l1 s r value
      let l3 := ledger_safe_transfer l2 sdOrig sdBen sdAmt
      let l4 := ledger_set l3 s (ledger_balance l3 s + gasLeft * effPrice)
      let l5 := ledger_set l4 c (ledger_balance l4 c + gasUsed * tip)
      have h_ge : upfront ≤ ledger_balance led s := by
        dsimp only [upfront, effPrice]
        omega
      have h_clr : ledger_total (ledger_clear_accounts_list l5 toDel) = ledger_total l5 :=
        ledger_total_clear_accounts_list l5 toDel
      have h5 : ledger_total l5 + ledger_balance l4 c =
          ledger_total l4 + (ledger_balance l4 c + gasUsed * tip) :=
        ledger_total_set l4 c (ledger_balance l4 c + gasUsed * tip)
      have h4 : ledger_total l4 + ledger_balance l3 s =
          ledger_total l3 + (ledger_balance l3 s + gasLeft * effPrice) :=
        ledger_total_set l3 s (ledger_balance l3 s + gasLeft * effPrice)
      have h3 : ledger_total l3 = ledger_total l2 :=
        ledger_safe_transfer_total l2 sdOrig sdBen sdAmt
      have h2 : ledger_total l2 = ledger_total l1 :=
        ledger_safe_transfer_total l1 s r value
      have h1 : ledger_total l1 + ledger_balance led s =
          ledger_total led + (ledger_balance led s - upfront) :=
        ledger_total_set led s (ledger_balance led s - upfront)
      have h_fee_decomp :
          gasLeft * effPrice + gasUsed * tip + (gasUsed * baseFee + blobFee) = upfront := by
        dsimp only [upfront, effPrice]
        have h_u : gasUsed * (baseFee + tip) = gasUsed * baseFee + gasUsed * tip := Nat.mul_add _ _ _
        have h_g : (gasUsed + gasLeft) * (baseFee + tip) =
            gasUsed * (baseFee + tip) + gasLeft * (baseFee + tip) := Nat.add_mul _ _ _
        omega
      change ledger_total (ledger_clear_accounts_list l5 toDel) + (gasUsed * baseFee + blobFee) =
        ledger_total led + 0
      omega
  | clWithdrawal recipient amount =>
    dsimp only [apply_block_account_step, block_step_burned, block_step_cl_inflow]
    have h := ledger_total_set led recipient (ledger_balance led recipient + amount)
    omega
  | uncheckedSystemTx caller target toDel =>
    dsimp only [apply_block_account_step, block_step_burned, block_step_cl_inflow]
    rw [ledger_total_clear_accounts_list, ledger_safe_transfer_total]

/-- Result of folding an arbitrary sequence of concrete block-accounting steps. -/
structure BlockAccountingResult where
  postLedger : EthLedger
  totalBaseFeeBurned : Nat
  totalClWithdrawals : Nat
  deriving Repr, DecidableEq, BEq

/-- Stateful fold of `apply_body` (`fork.py:783-852`): system transactions, regular user
transactions (with `SELFDESTRUCT` and EIP-8246 clearing), and CL withdrawals. -/
def fold_block_account_steps (steps : List BlockAccountStep) (led : EthLedger) : BlockAccountingResult :=
  match steps with
  | [] => { postLedger := led, totalBaseFeeBurned := 0, totalClWithdrawals := 0 }
  | step :: rest =>
    let burned := block_step_burned led step
    let inflow := block_step_cl_inflow step
    let nextLed := apply_block_account_step led step
    let tail := fold_block_account_steps rest nextLed
    { postLedger := tail.postLedger
      totalBaseFeeBurned := burned + tail.totalBaseFeeBurned
      totalClWithdrawals := inflow + tail.totalClWithdrawals }

/-- T-8246-BLOCK-EL-SUPPLY-CONSERVATION: across an arbitrary multi-step block execution (`apply_body`
at `fork.py:783-852`), total post-block EL balance plus cumulative EIP-1559 base/blob fees burned
equals total pre-block EL balance plus cumulative CL withdrawals credited via `create_ether`,
with zero ETH burned by EIP-8246 `SELFDESTRUCT` or `clear_account_preserving_balance`. -/
theorem t_8246_block_el_supply_conservation (steps : List BlockAccountStep) (pre : EthLedger) :
    let post := fold_block_account_steps steps pre
    ledger_total post.postLedger + post.totalBaseFeeBurned =
      ledger_total pre + post.totalClWithdrawals := by
  induction steps generalizing pre with
  | nil => rfl
  | cons step rest ih =>
    dsimp only [fold_block_account_steps]
    have h_step := apply_block_account_step_conserved pre step
    have h_tail := ih (apply_block_account_step pre step)
    dsimp only at h_tail
    omega

/-- Concrete multi-account block witness exercising system call, affordable regular transaction
with `SELFDESTRUCT` + EIP-8246 `accounts_to_delete` clear, and CL withdrawal. -/
theorem t_8246_concrete_block_supply_witness :
    let steps : List BlockAccountStep := [
      .uncheckedSystemTx 0xffff 0xeeee [],
      .regularTx 0xaaaa 0xbbbb 0xcccc 0xbbbb 0xbbbb 21000 4000 7 3 0 40 40 [0xbbbb],
      .clWithdrawal 0xdddd 90
    ]
    let pre : EthLedger := [
      (0xaaaa, { balance := 300000 }),
      (0xbbbb, { nonce := 1, balance := 5, codeHash := 0x99, codeEmpty := false }),
      (0xcccc, { balance := 0 }),
      (0xdddd, { balance := 1 }),
      (0xffff, { balance := 0 })
    ]
    let post := fold_block_account_steps steps pre
    ledger_total post.postLedger + post.totalBaseFeeBurned =
      ledger_total pre + post.totalClWithdrawals ∧
    ledger_total post.postLedger = 153096 ∧
    post.totalBaseFeeBurned = 147000 ∧
    post.totalClWithdrawals = 90 ∧
    (ledger_account post.postLedger 0xbbbb).balance = 45 ∧
    (ledger_account post.postLedger 0xbbbb).codeHash = EMPTY_CODE_HASH := by
  decide

/-! ## 7. Same-Tx `CREATE` + `selfdestruct(self)` Fork Delta (`FINDING-023` & `FINDING-037`)
    (`vm/instructions/system.py:706-779`, `fork.py:1088-1089`, `EIPS/eip-8246.md:34-50, 73-76`) -/

/-- Canonical Symbiotic Mainnet `wstETH_Burner` address (`FINDING-023`, `fradamt/8037-coordination#411`). -/
def SYMBIOTIC_WSTETH_BURNER_ADDR : Address := 0xdCaC890b14121FD5D925E2589017Be68C2B5B324

/-- Canonical OP-Stack `L2ToL1MessagePasser` predeploy address (`FINDING-037`, `EIPS/eip-8246.md:75`). -/
def OP_L2_TO_L1_MESSAGE_PASSER_ADDR : Address := 0x4200000000000000000000000000000000000016

/-- Deploy and endow a freshly created burner contract in `TransactionState`, mirroring
`process_create` + `process_call` (`interpreter.py:324-449`) for `new SelfDestruct{value: slashAmount}()`
(`SelfDestruct.sol`, `FINDING-023`) and `new Burner{value: slashAmount}()` (`Burn.sol`, `FINDING-037`):
1. `destroy_storage_tx`, `mark_account_created`, and `increment_nonce` (`nonce := 1`) at `burnerAddr`;
2. `move_ether_tx` transferring `slashAmount` from `vaultAddr` to `burnerAddr`;
3. `set_code` writing non-empty burner runtime/init marker `burnerCodeHash` and `set_storage` on `slot`. -/
def deploy_and_endow_same_tx_burner (pre : TransactionState) (vaultAddr burnerAddr : Address)
    (slashAmount : Nat) (burnerCodeHash : Hash32) (slot : StorageKey) (slotVal : StorageVal) :
    Option TransactionState :=
  let s1 := destroy_storage_tx pre burnerAddr
  let s2 := mark_account_created s1 burnerAddr
  let s3 := increment_nonce s2 burnerAddr
  match move_ether_tx s3 vaultAddr burnerAddr slashAmount with
  | none => none
  | some s4 =>
    let s5 := set_code s4 burnerAddr burnerCodeHash 1
    some (set_storage s5 burnerAddr slot slotVal)

/-- Pre-Amsterdam (Osaka / EIP-6780) execution of same-tx `CREATE` + `selfdestruct(address(this))`:
the constructor's self-beneficiary `SELFDESTRUCT` zeroes `burnerAddr`'s balance via
`set_account_balance_tx` (`0`) and schedules `burnerAddr` in `accounts_to_delete`, where end-of-tx
finalization calls `destroy_account` (`state_tracker.py:474-491`), burning `slashAmount`. -/
def exec_same_tx_burner_osaka (pre : TransactionState) (vaultAddr burnerAddr : Address)
    (slashAmount : Nat) (burnerCodeHash : Hash32) (slot : StorageKey) (slotVal : StorageVal) :
    Option TransactionState :=
  match deploy_and_endow_same_tx_burner pre vaultAddr burnerAddr slashAmount burnerCodeHash slot slotVal with
  | none => none
  | some sCreated =>
    let sZeroed := set_account_balance_tx sCreated burnerAddr 0
    some (destroy_account sZeroed burnerAddr)

/-- Amsterdam (EIP-8246) execution of same-tx `CREATE` + `selfdestruct(address(this))`
(`vm/instructions/system.py:760-773`, `fork.py:1088-1089`, `state_tracker.py:494-516`):
`selfdestruct` executes `move_ether_tx sCreated burnerAddr burnerAddr balance` (self-transfer no-op
on balance) and registers `burnerAddr` in `accounts_to_delete`, where end-of-tx finalization calls
`clear_account_preserving_balance_tx` — clearing `nonce`, `codeHash`, and storage while preserving
`slashAmount` on the now-codeless plain-`CREATE` address (`FINDING-023` & `FINDING-037`). -/
def exec_same_tx_burner_amsterdam (pre : TransactionState) (vaultAddr burnerAddr : Address)
    (slashAmount : Nat) (burnerCodeHash : Hash32) (slot : StorageKey) (slotVal : StorageVal) :
    Option TransactionState :=
  match deploy_and_endow_same_tx_burner pre vaultAddr burnerAddr slashAmount burnerCodeHash slot slotVal with
  | none => none
  | some sCreated =>
    let curBal := (get_account sCreated burnerAddr).balance
    match move_ether_tx sCreated burnerAddr burnerAddr curBal with
    | none => none
    | some sAfterSd =>
      some (clear_account_preserving_balance_tx sAfterSd burnerAddr)

/-- Explicit OP-Stack L2↔L1 bridge supply-accounting model (`FINDING-037`, `EIPS/eip-8246.md:75`):
given `l2PreSupply` prior to `L2ToL1MessagePasser.burn()`, `slashAmount` swept into `Burner`, and
whether the L2 EL uses unmodified EIP-8246 `preserveBalance` (`true`) vs an explicit burn (`false`),
returns `(l1Released, l2PostSupply)` when `WithdrawerBalanceBurnt(slashAmount)` is emitted unconditionally. -/
def op_l2_bridge_burn_sweep_supply (l2PreSupply slashAmount : Nat) (l2PreservesSelfdestructBalance : Bool) :
    Nat × Nat :=
  let l1Released := slashAmount
  let l2PostSupply := if l2PreservesSelfdestructBalance then l2PreSupply else l2PreSupply - slashAmount
  (l1Released, l2PostSupply)

/-- Balance of `target` after `modify_state` on the same address. -/
theorem get_account_modify_state_same_balance (st : TransactionState) (addr : Address)
    (f : Account → Account) :
    (get_account (modify_state st addr f) addr).balance = (f (get_account st addr)).balance := by
  dsimp only [modify_state, destroy_account]
  cases h_emp : (f (get_account st addr)).isEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte, get_account_set_account_some_same]
  · simp only [↓reduceIte, get_account_set_account_none_same, EMPTY_ACCOUNT]
    simp only [Account.isEmpty, Bool.and_eq_true, beq_iff_eq] at h_emp
    omega

/-- Balance of `burnerAddr` and `vaultAddr` after `deploy_and_endow_same_tx_burner` when `burnerAddr`
starts with zero balance (`get_account pre burnerAddr = EMPTY_ACCOUNT`), `vaultBalance ≥ slashAmount`,
and `vaultAddr ≠ burnerAddr`. -/
theorem deploy_and_endow_same_tx_burner_balances
    (pre : TransactionState) (vaultAddr burnerAddr : Address)
    (slashAmount : Nat) (burnerCodeHash : Hash32) (slot : StorageKey) (slotVal : StorageVal)
    (h_ne : vaultAddr ≠ burnerAddr)
    (h_fresh : (get_account pre burnerAddr).balance = 0)
    (h_afford : (get_account pre vaultAddr).balance ≥ slashAmount) :
    ∃ sCreated,
      deploy_and_endow_same_tx_burner pre vaultAddr burnerAddr slashAmount burnerCodeHash slot slotVal =
        some sCreated ∧
      (get_account sCreated vaultAddr).balance = (get_account pre vaultAddr).balance - slashAmount ∧
      (get_account sCreated burnerAddr).balance = slashAmount := by
  dsimp only [deploy_and_endow_same_tx_burner]
  let s1 := destroy_storage_tx pre burnerAddr
  let s2 := mark_account_created s1 burnerAddr
  let s3 := increment_nonce s2 burnerAddr
  have h_s2_acct : ∀ a, get_account s2 a = get_account pre a := by
    intro a
    dsimp only [s2, mark_account_created]
    split
    · exact get_account_destroy_storage_tx pre burnerAddr a
    · dsimp only [get_account, get_account_optional, get_pre_state_account_optional]
      rfl
  have h_s3_vault : (get_account s3 vaultAddr).balance = (get_account pre vaultAddr).balance := by
    dsimp only [s3, increment_nonce]
    rw [get_account_modify_state_ne s2 burnerAddr vaultAddr _ h_ne, h_s2_acct]
  have h_s3_burner : (get_account s3 burnerAddr).balance = 0 := by
    dsimp only [s3, increment_nonce]
    rw [get_account_modify_state_same_balance, h_s2_acct, h_fresh]
  have h_not_lt : ¬ (get_account s3 vaultAddr).balance < slashAmount := by omega
  have h_mv_eq :
      move_ether_tx s3 vaultAddr burnerAddr slashAmount =
        some (modify_state
          (modify_state s3 vaultAddr (fun acc => { acc with balance := acc.balance - slashAmount }))
          burnerAddr (fun acc => { acc with balance := acc.balance + slashAmount })) := by
    dsimp only [move_ether_tx]
    simp only [h_not_lt, ↓reduceIte]
  rw [h_mv_eq]
  dsimp only
  let s4a := modify_state s3 vaultAddr (fun acc => { acc with balance := acc.balance - slashAmount })
  let s4 := modify_state s4a burnerAddr (fun acc => { acc with balance := acc.balance + slashAmount })
  let s5 := set_code s4 burnerAddr burnerCodeHash 1
  let s6 := set_storage s5 burnerAddr slot slotVal
  refine ⟨s6, rfl, ?_, ?_⟩
  · have h_s6 : get_account s6 vaultAddr = get_account s5 vaultAddr := rfl
    have h_s5 : (get_account s5 vaultAddr).balance = (get_account s4 vaultAddr).balance := by
      dsimp only [s5, set_code]
      rw [get_account_modify_state_ne _ burnerAddr vaultAddr _ h_ne]
      split <;> rfl
    have h_s4 : (get_account s4 vaultAddr).balance = (get_account s4a vaultAddr).balance :=
      get_account_modify_state_ne s4a burnerAddr vaultAddr _ h_ne
    have h_s4a : (get_account s4a vaultAddr).balance = (get_account s3 vaultAddr).balance - slashAmount :=
      get_account_modify_state_same_balance s3 vaultAddr _
    rw [h_s6, h_s5, h_s4, h_s4a, h_s3_vault]
  · have h_s6 : get_account s6 burnerAddr = get_account s5 burnerAddr := rfl
    have h_s5 : (get_account s5 burnerAddr).balance = (get_account s4 burnerAddr).balance := by
      dsimp only [s5, set_code]
      rw [get_account_modify_state_same_balance]
      dsimp only
      split <;> rfl
    have h_s4 : (get_account s4 burnerAddr).balance = (get_account s4a burnerAddr).balance + slashAmount :=
      get_account_modify_state_same_balance s4a burnerAddr _
    have h_s4a : (get_account s4a burnerAddr).balance = (get_account s3 burnerAddr).balance :=
      get_account_modify_state_ne s3 vaultAddr burnerAddr _ (Ne.symm h_ne)
    rw [h_s6, h_s5, h_s4, h_s4a, h_s3_burner, Nat.zero_add]

/-- T-8246-FINDING-023-037-SELFDESTRUCT-SELF-BURN-BECOMES-STRAND
(`FINDING-023` Symbiotic native-ETH burners & `FINDING-037` OP-Stack `L2ToL1MessagePasser.burn()`):
For any vault/caller `vaultAddr` with `balance ≥ slashAmount > 0` and fresh plain-`CREATE` burner
`burnerAddr ≠ vaultAddr`:
1. **Osaka / EIP-6780**: `exec_same_tx_burner_osaka` succeeds (`some postOsaka`), deletes `burnerAddr`
   (`balance = 0`, `nonce = 0`, `codeHash = EMPTY_CODE_HASH`, `is_account_alive = false`), and reduces
   combined `(vault + burner)` balance from `vaultBalance` to `vaultBalance - slashAmount` (true burn).
2. **Amsterdam / EIP-8246**: `exec_same_tx_burner_amsterdam` succeeds (`some postAmst`), clears
   `nonce = 0`, `codeHash = EMPTY_CODE_HASH`, `codeEmpty = true`, and storage (`get_storage = 0`),
   YET preserves `(get_account postAmst burnerAddr).balance = slashAmount > 0` with
   `is_account_alive postAmst burnerAddr = true`, leaving `(vault + burner)` balance equal to
   `vaultBalance` (`0` ETH burned — silent permanent strand).
3. **OP-Stack L2 Bridge Inflation Corollary (`FINDING-037`)**: if an OP-Stack L2 sweeps `slashAmount ≤ l2PreSupply`
   under unmodified EIP-8246 preserve-balance while L1 still releases `slashAmount` upon
   `WithdrawerBalanceBurnt(slashAmount)`, cross-domain ETH supply inflates by exactly `+slashAmount`
   (`l1Released + l2PostSupply = l2PreSupply + slashAmount`), whereas explicit L2 burn preserves
   `l1Released + l2PostSupply = l2PreSupply`. -/
theorem t_8246_finding_023_037_selfdestruct_self_burn_becomes_strand
    (pre : TransactionState) (vaultAddr burnerAddr : Address)
    (slashAmount l2PreSupply : Nat) (burnerCodeHash : Hash32) (slot : StorageKey) (slotVal : StorageVal)
    (h_pos : slashAmount > 0)
    (h_ne : vaultAddr ≠ burnerAddr)
    (h_fresh : (get_account pre burnerAddr).balance = 0)
    (h_afford : (get_account pre vaultAddr).balance ≥ slashAmount)
    (h_l2_supply : l2PreSupply ≥ slashAmount) :
    ∃ postOsaka postAmst,
      exec_same_tx_burner_osaka pre vaultAddr burnerAddr slashAmount burnerCodeHash slot slotVal =
        some postOsaka ∧
      exec_same_tx_burner_amsterdam pre vaultAddr burnerAddr slashAmount burnerCodeHash slot slotVal =
        some postAmst ∧
      -- (1) Osaka EIP-6780: burner deleted, balance = 0, slashAmount genuinely burned
      (get_account postOsaka burnerAddr).balance = 0 ∧
      (get_account postOsaka burnerAddr).nonce = 0 ∧
      (get_account postOsaka burnerAddr).codeHash = EMPTY_CODE_HASH ∧
      is_account_alive postOsaka burnerAddr = false ∧
      sum_balances_tx postOsaka [vaultAddr, burnerAddr] =
        (get_account pre vaultAddr).balance - slashAmount ∧
      -- (2) Amsterdam EIP-8246: code/nonce/storage cleared, YET slashAmount > 0 stranded alive
      (get_account postAmst burnerAddr).nonce = 0 ∧
      (get_account postAmst burnerAddr).codeHash = EMPTY_CODE_HASH ∧
      (get_account postAmst burnerAddr).codeEmpty = true ∧
      get_storage postAmst burnerAddr slot = 0 ∧
      (get_account postAmst burnerAddr).balance = slashAmount ∧
      is_account_alive postAmst burnerAddr = true ∧
      sum_balances_tx postAmst [vaultAddr, burnerAddr] = (get_account pre vaultAddr).balance ∧
      -- (3) OP-Stack L2↔L1 bridge corollary: +slashAmount inflation vs exact conservation
      (let (l1RelPreserve, l2PostPreserve) := op_l2_bridge_burn_sweep_supply l2PreSupply slashAmount true
       let (l1RelBurn, l2PostBurn) := op_l2_bridge_burn_sweep_supply l2PreSupply slashAmount false
       l1RelPreserve + l2PostPreserve = l2PreSupply + slashAmount ∧
       l1RelBurn + l2PostBurn = l2PreSupply) := by
  obtain ⟨sCreated, h_dep, h_c_vault, h_c_burner⟩ :=
    deploy_and_endow_same_tx_burner_balances pre vaultAddr burnerAddr
      slashAmount burnerCodeHash slot slotVal h_ne h_fresh h_afford
  dsimp only [exec_same_tx_burner_osaka, exec_same_tx_burner_amsterdam]
  rw [h_dep]
  dsimp only
  have h_self_move :
      ∃ sAfterSd,
        move_ether_tx sCreated burnerAddr burnerAddr (get_account sCreated burnerAddr).balance =
          some sAfterSd ∧
        (get_account sAfterSd vaultAddr).balance = (get_account sCreated vaultAddr).balance ∧
        (get_account sAfterSd burnerAddr).balance = slashAmount := by
    dsimp only [move_ether_tx]
    have h_nlt : ¬ (get_account sCreated burnerAddr).balance < (get_account sCreated burnerAddr).balance :=
      Nat.lt_irrefl _
    simp only [h_nlt, ↓reduceIte]
    let fSub : Account → Account :=
      fun acc => { acc with balance := acc.balance - (get_account sCreated burnerAddr).balance }
    let fAdd : Account → Account :=
      fun acc => { acc with balance := acc.balance + (get_account sCreated burnerAddr).balance }
    let m1 := modify_state sCreated burnerAddr fSub
    let m2 := modify_state m1 burnerAddr fAdd
    refine ⟨m2, rfl, ?_, ?_⟩
    · have hm2 := get_account_modify_state_ne m1 burnerAddr vaultAddr fAdd h_ne
      have hm1 := get_account_modify_state_ne sCreated burnerAddr vaultAddr fSub h_ne
      rw [hm2, hm1]
    · have hm2 := get_account_modify_state_same_balance m1 burnerAddr fAdd
      have hm1 := get_account_modify_state_same_balance sCreated burnerAddr fSub
      change (get_account m2 burnerAddr).balance = slashAmount
      rw [hm2]
      dsimp only [fAdd]
      rw [hm1]
      dsimp only [fSub]
      rw [h_c_burner]
      omega
  obtain ⟨sAfterSd, h_mv, h_sd_vault, h_sd_burner⟩ := h_self_move
  rw [h_mv]
  let postOsaka := destroy_account (set_account_balance_tx sCreated burnerAddr 0) burnerAddr
  let postAmst := clear_account_preserving_balance_tx sAfterSd burnerAddr
  refine ⟨postOsaka, postAmst, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [postOsaka, destroy_account, EMPTY_ACCOUNT]
  · simp [postOsaka, destroy_account, EMPTY_ACCOUNT]
  · simp [postOsaka, destroy_account, EMPTY_ACCOUNT]
  · simp [postOsaka, destroy_account, is_account_alive]
  · dsimp only [sum_balances_tx, List.map, List.sum_cons, List.sum_nil]
    have h_osaka_vault : (get_account postOsaka vaultAddr).balance =
        (get_account sCreated vaultAddr).balance := by
      dsimp only [postOsaka, destroy_account, set_account_balance_tx]
      rw [get_account_set_account_ne _ burnerAddr vaultAddr none h_ne]
      rw [get_account_destroy_storage_tx]
      exact get_account_modify_state_ne sCreated burnerAddr vaultAddr _ h_ne
    have h_osaka_burner : (get_account postOsaka burnerAddr).balance = 0 := by
      simp [postOsaka, destroy_account, EMPTY_ACCOUNT]
    rw [h_osaka_vault, h_osaka_burner, h_c_vault]
    omega
  · exact (t_8246_tx_state_clear_exact sAfterSd burnerAddr slot).2.1
  · exact (t_8246_tx_state_clear_exact sAfterSd burnerAddr slot).2.2.1
  · dsimp only [postAmst, clear_account_preserving_balance_tx, modify_state]
    rw [get_account_destroy_storage_tx]
    split
    · simp [destroy_account, EMPTY_ACCOUNT]
    · simp
  · exact (t_8246_tx_state_clear_exact sAfterSd burnerAddr slot).2.2.2.1
  · rw [(t_8246_tx_state_clear_exact sAfterSd burnerAddr slot).1, h_sd_burner]
  · dsimp only [postAmst, clear_account_preserving_balance_tx, modify_state, is_account_alive]
    rw [get_account_destroy_storage_tx]
    have h_ne_zero : ((get_account sAfterSd burnerAddr).balance == 0) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    simp [Account.isEmpty, h_ne_zero]
  · dsimp only [sum_balances_tx, List.map, List.sum_cons, List.sum_nil]
    have h_amst_vault := t_8246_clear_preserves_any_account_balance sAfterSd burnerAddr vaultAddr
    have h_amst_burner := (t_8246_tx_state_clear_exact sAfterSd burnerAddr slot).1
    rw [h_amst_vault, h_amst_burner, h_sd_vault, h_sd_burner, h_c_vault]
    omega
  · dsimp only [op_l2_bridge_burn_sweep_supply]
    simp only [↓reduceIte, Bool.false_eq_true]
    omega

/-- C-ABI differential export for `FINDING-023` / `FINDING-037`: returns post-transaction balance
at a newly `CREATE`-deployed contract that executes `selfdestruct(address(this))` in the same
transaction (`0` under Osaka EIP-6780 `isAmsterdam == 0`; `slashAmount` under Amsterdam EIP-8246
`isAmsterdam != 0`). -/
@[inline, export glamsterdam_eip8246_same_tx_selfdestruct_self_post_balance_cabi]
def eip8246_same_tx_selfdestruct_self_post_balance_cabi (isAmsterdam slashAmount : UInt64) : UInt64 :=
  let pre : TransactionState :=
    set_account {} SYMBIOTIC_WSTETH_BURNER_ADDR (some { nonce := 1, balance := slashAmount.toNat })
  let burnerAddr : Address := 0xdeadbeef01
  let postOpt :=
    if isAmsterdam != 0 then
      exec_same_tx_burner_amsterdam pre SYMBIOTIC_WSTETH_BURNER_ADDR burnerAddr slashAmount.toNat 1 0 0
    else
      exec_same_tx_burner_osaka pre SYMBIOTIC_WSTETH_BURNER_ADDR burnerAddr slashAmount.toNat 1 0 0
  match postOpt with
  | some st => (get_account st burnerAddr).balance.toUInt64
  | none => 0

/-- Concrete `by decide` witness instantiating `SYMBIOTIC_WSTETH_BURNER_ADDR`,
`OP_L2_TO_L1_MESSAGE_PASSER_ADDR`, and `eip8246_same_tx_selfdestruct_self_post_balance_cabi`
across Osaka (burn) vs Amsterdam (strand). -/
theorem t_8246_finding_023_037_concrete_witness :
    let preSym : TransactionState :=
      set_account {} SYMBIOTIC_WSTETH_BURNER_ADDR (some { nonce := 5, balance := 1000 })
    let preOp : TransactionState :=
      set_account {} OP_L2_TO_L1_MESSAGE_PASSER_ADDR (some { nonce := 1, balance := 5000 })
    let burnerChild : Address := 0xdeadbeef01
    let osakaSym := exec_same_tx_burner_osaka preSym SYMBIOTIC_WSTETH_BURNER_ADDR burnerChild 250 0x7777 0 1
    let amstSym := exec_same_tx_burner_amsterdam preSym SYMBIOTIC_WSTETH_BURNER_ADDR burnerChild 250 0x7777 0 1
    let osakaOp := exec_same_tx_burner_osaka preOp OP_L2_TO_L1_MESSAGE_PASSER_ADDR burnerChild 500 0x8888 0 1
    let amstOp := exec_same_tx_burner_amsterdam preOp OP_L2_TO_L1_MESSAGE_PASSER_ADDR burnerChild 500 0x8888 0 1
    (osakaSym.map (fun st => (get_account st burnerChild).balance)) = some 0 ∧
    (amstSym.map (fun st => (get_account st burnerChild).balance)) = some 250 ∧
    (amstSym.map (fun st => (get_account st burnerChild).codeHash)) = some EMPTY_CODE_HASH ∧
    (osakaOp.map (fun st => (get_account st burnerChild).balance)) = some 0 ∧
    (amstOp.map (fun st => (get_account st burnerChild).balance)) = some 500 ∧
    eip8246_same_tx_selfdestruct_self_post_balance_cabi 0 500 = 0 ∧
    eip8246_same_tx_selfdestruct_self_post_balance_cabi 1 500 = 500 := by
  decide

end Glamsterdam.Eip8246.Spec
