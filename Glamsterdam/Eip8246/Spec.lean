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
- `src/ethereum/forks/amsterdam/fork.py` (`process_transaction:1004-1094`,
  `process_unchecked_system_transaction:724-780`)
- `src/ethereum/forks/amsterdam/block_access_lists.py` (`update_builder_from_tx:760-825`)
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

/-- After transaction cleanup, the address passes the pinned state tracker's
nonce/code collision check even if its balance survives. This establishes
eligibility for creation, independent of gas and initcode execution. -/
theorem t_8246_cleared_address_deployable (txState : TransactionState) (addr : Address) :
    account_deployable (clear_account_preserving_balance_tx txState addr) addr = true := by
  obtain ⟨_, hn, hc, _⟩ := t_8246_tx_state_clear_exact txState addr 0
  simp [account_deployable, hn, hc]

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

end Glamsterdam.Eip8246.Spec
