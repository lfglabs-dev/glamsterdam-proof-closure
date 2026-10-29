/-
Copyright (c) 2026 Verity Labs / LFG Labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Marchand, Verity Audit Team
-/
import Glamsterdam.Common.MetaSpec

/-!
# Glamsterdam Gloas Consensus Layer (`EIP-7732` + `EIP-8282`) Formal Specification and Verification

Pinned against `ethereum/consensus-specs` @ `aa16bb4c156184e9548a997d53efaf2a228a6304`
(`v1.7.0-beta.4`, `specs/gloas/beacon-chain.md` & `specs/gloas/fork.md`), with dual-pin coverage
of post-`v1.7.0-beta.4` PRs `consensus-specs#5736` (`8b374fa81b`) and `consensus-specs#5763`
(`1bdf4b8be5`), plus client-export bid-validation boundaries (`FINDING-028` & `FINDING-031`).
(Note: full LMD-GHOST tree and P2P gossip remain outside core BeaconState transition scope;
deterministic should_build_on_full vs proposal-slot alignment from consensus-specs#5763 is
formalized in Section 9.)

## Core First-Principles Consensus Invariants (Potuz Scope)
1. **Supply Neutrality / No ETH Minting (`t_7732_single_settlement`, `t_7732_no_eth_minting`)**:
   Every committed builder bid (`process_execution_payload_bid:2162-2216`) is settled at most once
   across `apply_parent_execution_payload` (`settle_builder_payment:1538-1544`, `1784-1831`) and
   `process_builder_pending_payments` (`1719-1732`), is backed by `can_builder_cover_bid`
   (`1184-1193`), and is debited 1-for-1 in `apply_withdrawals` (`1997-2007`) without saturation
   inflation (`t_7732_builder_withdrawal_no_underflow`). Relative to pre-Gloas consensus issuance
   and EIP-1559 burn, builder bid settlement is strictly supply-neutral.
2. **Proposer Payment Guarantee (`t_7732_payment_guarantee`)**:
   Whenever a committed bid has positive value and the payload is either confirmed by the child
   block (`isParentFull = true`) or reaches the 60% slot attestation quorum (`weight ≥ quorum`),
   the proposer's `fee_recipient` is guaranteed to receive a `BuilderPendingWithdrawal` for the
   exact `bid.value`.
3. **Unconditional Quorum Weight Anti-Double-Counting (`t_7732_quorum_no_double_count`,
   `t_7732_quorum_weight_unconditional`)**:
   In `process_attestation` (`beacon-chain.md:2396-2481`), the participation gate
   `will_set_new_flag and had_no_participation` (`2447-2467`) guarantees unconditionally that each
   validator contributes `effective_balance` to `payment.weight` at most once per epoch.
4. **Same-Slot Unbundling Resistance (`t_7732_same_slot_unbundling`)**:
   Because `process_execution_payload_bid` (`2162-2216`) commits the slot's block header to
   `state.latest_execution_payload_bid.block_hash = bid.block_hash` and
   `process_parent_execution_payload` (`1841-1854`) accepts a full execution payload for that slot
   if and only if `child_bid.parent_block_hash == parent_bid.block_hash`, no canonical payload at
   slot `N` other than the builder's committed payload can include a private transaction known only
   to the builder prior to payload reveal.
5. **Builder Solvency, Exit Safety, and Consensus Frame Preservation (`t_7732_builder_solvency`,
   `t_7732_exit_safety`, `t_7732_deferred_exec_equiv_empty`, `t_7732_frame`,
   `t_8282_7732_queue_safety`)**.

## Specification Edge-Case Findings in `v1.7.0-beta.4` (`aa16bb4c`)
- `F-7732-SLASHED-PAYMENT-RESURRECTION` (`slash_validator:1549-1582` vs
  `apply_parent_execution_payload:1799-1814`).
- `F-8282-TOPUP-CREDENTIAL-PREFIX-DROP` & `F-7732-FORK-ONBOARD-CROSS-CREDENTIAL`: cross-function
  ordering divergence between `process_builder_deposit_request` (`beacon-chain.md:2334-2361`) and
  `onboard_builders_from_pending_deposits` (`fork.md:70-120`).
- `F-7732-FORK-SLOT-AVAILABILITY-BIT-HIGH` (`fork.md:198-200`) &
  `F-7732-AVAILABILITY-RING-BUFFER-CLOBBER` (`beacon-chain.md:1620-1622, 1829`).
-/

namespace Glamsterdam.Gloas7732.Spec

open Glamsterdam.Common.Prelude
open Glamsterdam.Common.MetaSpec

/-! ## 0. Pinned Gloas Constants (`specs/gloas/beacon-chain.md:546-636` @ `aa16bb4c`) -/

def MIN_DEPOSIT_AMOUNT : Nat := 1000000000
def FAR_FUTURE_EPOCH : Nat := 18446744073709551615
def BUILDER_INDEX_FLAG : Nat := 1099511627776 -- 2^40 (`beacon-chain.md:556`)
def BUILDER_INDEX_SELF_BUILD : Nat := 18446744073709551615 -- `UINT64_MAX` (`beacon-chain.md:571`)
def BUILDER_PAYMENT_THRESHOLD_NUMERATOR : Nat := 6 -- `beacon-chain.md:572`
def BUILDER_PAYMENT_THRESHOLD_DENOMINATOR : Nat := 10 -- `beacon-chain.md:573`
def MIN_BUILDER_WITHDRAWABILITY_DELAY : Nat := 64 -- `2**6` (`beacon-chain.md:635`)
def PAYLOAD_BUILDER_VERSION : Nat := 0x00 -- `Uint8(0)` (`beacon-chain.md:585`)
def BUILDER_WITHDRAWAL_PREFIX : Nat := 0xB0 -- `Bytes1("0xB0")` (`beacon-chain.md:579`)
def BUILDER_DEPOSIT_REQUEST_TYPE : Nat := 0x03 -- `Bytes1("0x03")` (`beacon-chain.md:591`)
def BUILDER_EXIT_REQUEST_TYPE : Nat := 0x04 -- `Bytes1("0x04")` (`beacon-chain.md:592`)

structure BuilderPendingWithdrawal where
  feeRecipient : Nat
  amount : Nat
  builderIndex : Nat
  deriving Repr, DecidableEq, BEq

structure BuilderPendingPayment where
  weight : Nat := 0
  withdrawal : BuilderPendingWithdrawal := ⟨0, 0, 0⟩
  proposerIndex : Nat := 0
  deriving Repr, DecidableEq, BEq

structure Builder where
  pubkey : Nat := 0
  version : Nat := PAYLOAD_BUILDER_VERSION
  executionAddress : Nat := 0
  balance : Nat
  depositEpoch : Nat
  withdrawableEpoch : Nat
  deriving Repr, DecidableEq, BEq

structure UntouchedClInvariants where
  validatorRegistryRoot : Nat
  blsToExecutionRoot : Nat
  syncCommitteeRoot : Nat
  deriving Repr, DecidableEq, BEq

structure GloasParentPaymentState where
  parentEpoch : Nat
  currentEpoch : Nat
  parentProposerSlashed : Bool
  latestBidValue : Nat
  latestBidFeeRecipient : Nat
  latestBidBuilderIndex : Nat
  pendingPaymentSlotAmount : Nat
  pendingWithdrawals : List BuilderPendingWithdrawal
  builderBalance : Nat
  builderWithdrawableEpoch : Nat
  untouchedCl : UntouchedClInvariants
  deriving Repr, DecidableEq, BEq

/-! ## 1. Builder Payment Settlement, Single-Settlement Invariant, Payment Guarantee,
    and Supply Neutrality (`No ETH Minting`) -/

/-- Exact `settle_builder_payment` (`beacon-chain.md:1538-1544`):
If `payment.withdrawal.amount > 0`, append `payment.withdrawal` to `builder_pending_withdrawals`,
and clear `builder_pending_payments[payment_index]` to `BuilderPendingPayment.empty()`. -/
def settle_builder_payment
    (payment : BuilderPendingPayment)
    (pendingWithdrawals : List BuilderPendingWithdrawal) :
    BuilderPendingPayment × List BuilderPendingWithdrawal :=
  let nextWithdrawals :=
    if payment.withdrawal.amount > 0 then
      pendingWithdrawals ++ [payment.withdrawal]
    else
      pendingWithdrawals
  ({}, nextWithdrawals)

/-- Exact `get_builder_payment_quorum_threshold` (`beacon-chain.md:1433-1440`). -/
def get_builder_payment_quorum_threshold (totalActiveBalance slotsPerEpoch : Nat) : Nat :=
  let perSlotBalance := totalActiveBalance / slotsPerEpoch
  let quorum := perSlotBalance * BUILDER_PAYMENT_THRESHOLD_NUMERATOR
  quorum / BUILDER_PAYMENT_THRESHOLD_DENOMINATOR

/-- Exact `process_builder_pending_payments` (`beacon-chain.md:1719-1732`):
For each payment in the previous epoch (`firstEpochPayments`), if `payment.weight >= quorum`,
append `payment.withdrawal` to `builder_pending_withdrawals`; then rotate `secondEpochPayments`
into the first half and fill the second half with empty payments. -/
def process_builder_pending_payments
    (quorum : Nat)
    (firstEpochPayments secondEpochPayments : List BuilderPendingPayment)
    (pendingWithdrawals : List BuilderPendingWithdrawal) :
    List BuilderPendingPayment × List BuilderPendingPayment × List BuilderPendingWithdrawal :=
  let settledWithdrawals :=
    firstEpochPayments.foldl
      (fun acc p => if p.weight ≥ quorum then acc ++ [p.withdrawal] else acc)
      pendingWithdrawals
  let emptyHalf := secondEpochPayments.map (fun _ => ({} : BuilderPendingPayment))
  (secondEpochPayments, emptyHalf, settledWithdrawals)

/-- Sum of `amount` across a list of `BuilderPendingWithdrawal` entries. -/
def sum_withdrawal_amounts (ws : List BuilderPendingWithdrawal) : Nat :=
  ws.foldl (fun acc w => acc + w.amount) 0

/-- Timing of child-block confirmation (`apply_parent_execution_payload`, `beacon-chain.md:1799-1814`)
relative to `parent_epoch = compute_epoch_at_slot(parent_slot)` across the 2-epoch
`builder_pending_payments` window:
- `notConfirmed`: parent payload is not confirmed by the child block (`isParentFull = false`);
  settlement can only occur via the 2-epoch attestation quorum in `process_builder_pending_payments`.
- `confirmedSameEpoch`: `parent_epoch == get_current_epoch(state)` (`lines 1799-1801`), settling
  and clearing `secondEpochPayments[slot]` before any epoch boundary.
- `confirmedNextEpoch`: `parent_epoch == get_previous_epoch(state)` (`lines 1802-1804`), after one
  epoch boundary has rotated `secondEpochPayments` into `firstEpochPayments`, settling and clearing
  `firstEpochPayments[slot]` before the second epoch boundary (and before `process_operations` in
  the child block, where `payment.withdrawal.amount > 0` at line 2464 prevents weight accrual on a
  cleared payment).
- `confirmedAfterTwoEpochs`: `parent_epoch < get_previous_epoch(state)` (`lines 1805-1814`). Because
  `parent_slot = state.latest_block_header.slot` when the child block arrives, no block intervened in
  `parent_epoch` or `parent_epoch + 1` to include attestations for `parent_slot`, so `weight = 0`
  when both epoch boundaries rotate the entry out of `builder_pending_payments`, and the child block
  appends `parent_bid.value` directly at lines `1808-1814`. -/
inductive ChildConfirmationTiming where
  | notConfirmed
  | confirmedSameEpoch
  | confirmedNextEpoch
  | confirmedAfterTwoEpochs
  deriving Repr, DecidableEq, BEq

/-- Full 2-epoch slot settlement lifecycle combining all three `parent_epoch` branches of
`apply_parent_execution_payload` (`settle_builder_payment:1538-1544`, `1799-1814`) and two
epoch-boundary rotations of `process_builder_pending_payments` (`1719-1732`):
- `.notConfirmed`: Epoch boundary 1 rotates `secondEpoch` -> `firstEpoch`; Epoch boundary 2 settles
  iff `attestedWeight >= quorum`.
- `.confirmedSameEpoch`: Child block in `parent_epoch` calls `settle_builder_payment` on `secondEpoch`,
  clearing it to `{}` before Epoch boundary 1.
- `.confirmedNextEpoch`: No block after `parent_slot` in `parent_epoch` (`weight = 0` at Epoch
  boundary 1); Epoch boundary 1 rotates `secondEpoch` into `firstEpoch`; child block in
  `parent_epoch + 1` calls `settle_builder_payment` on `firstEpoch` (clearing `amount = 0` before
  `process_attestation` at line 2464); Epoch boundary 2 sees `{}`.
- `.confirmedAfterTwoEpochs`: No block after `parent_slot` in `parent_epoch` or `parent_epoch + 1`
  (`weight = 0` across both epoch boundaries); child block at `current_epoch >= parent_epoch + 2`
  enters `elif parent_bid.value > 0:`. -/
def settle_slot_bid_lifecycle
    (feeRecipient bidValue builderIdx proposerIdx attestedWeight quorum : Nat)
    (timing : ChildConfirmationTiming) : List BuilderPendingWithdrawal :=
  let mkPayment (w : Nat) : BuilderPendingPayment :=
    if bidValue > 0 then
      { weight := w
        withdrawal := ⟨feeRecipient, bidValue, builderIdx⟩
        proposerIndex := proposerIdx }
    else
      {}
  match timing with
  | .notConfirmed =>
    let (first1, second1, w1) :=
      process_builder_pending_payments quorum [{}] [mkPayment attestedWeight] []
    let (_, _, w2) := process_builder_pending_payments quorum first1 second1 w1
    w2
  | .confirmedSameEpoch =>
    let (clearedSlot, wChild) := settle_builder_payment (mkPayment attestedWeight) []
    let (first1, second1, w1) :=
      process_builder_pending_payments quorum [{}] [clearedSlot] wChild
    let (_, _, w2) := process_builder_pending_payments quorum first1 second1 w1
    w2
  | .confirmedNextEpoch =>
    let (first1, second1, w1) :=
      process_builder_pending_payments quorum [{}] [mkPayment 0] []
    let (clearedSlot, wChild) :=
      match first1 with
      | p :: _ => settle_builder_payment p w1
      | [] => ({}, w1)
    let (_, _, w2) := process_builder_pending_payments quorum [clearedSlot] second1 wChild
    w2
  | .confirmedAfterTwoEpochs =>
    let (first1, second1, w1) :=
      process_builder_pending_payments quorum [{}] [mkPayment 0] []
    let (_, _, w2) := process_builder_pending_payments quorum first1 second1 w1
    if bidValue > 0 then
      w2 ++ [⟨feeRecipient, bidValue, builderIdx⟩]
    else
      w2

/-- T-7732-SINGLE-SETTLEMENT: Across all four `ChildConfirmationTiming` cases (`notConfirmed`,
`confirmedSameEpoch`, `confirmedNextEpoch`, `confirmedAfterTwoEpochs`), every committed builder bid
(`bidValue`) is settled at most once across `apply_parent_execution_payload` and
`process_builder_pending_payments`: for any `quorum > 0`, the total withdrawal amount queued is at
most `bidValue` (never double-settled as `2 * bidValue`). -/
theorem t_7732_single_settlement
    (feeRecipient bidValue builderIdx proposerIdx attestedWeight quorum : Nat)
    (timing : ChildConfirmationTiming)
    (h_quorum : quorum > 0) :
    sum_withdrawal_amounts
      (settle_slot_bid_lifecycle feeRecipient bidValue builderIdx proposerIdx
        attestedWeight quorum timing) ≤ bidValue := by
  have h_q0 : quorum ≠ 0 := by omega
  dsimp [settle_slot_bid_lifecycle, settle_builder_payment, process_builder_pending_payments,
    sum_withdrawal_amounts]
  cases timing <;> by_cases h_bid : bidValue > 0 <;> simp [h_bid, h_q0]
  by_cases h_wt : attestedWeight ≥ quorum <;> simp [h_wt]

/-- T-7732-PAYMENT-GUARANTEE (Potuz Property 2): If a committed bid has `bidValue > 0` and
`quorum > 0`, and the block's payload is either confirmed by the child block (`timing ≠ .notConfirmed`)
or attested up to the payment quorum (`attestedWeight ≥ quorum`), the proposer's `feeRecipient`
is guaranteed to receive the exact `BuilderPendingWithdrawal` of `amount = bidValue`. -/
theorem t_7732_payment_guarantee
    (feeRecipient bidValue builderIdx proposerIdx attestedWeight quorum : Nat)
    (timing : ChildConfirmationTiming)
    (h_bid : bidValue > 0)
    (h_quorum : quorum > 0)
    (h_timely : timing ≠ .notConfirmed ∨ attestedWeight ≥ quorum) :
    settle_slot_bid_lifecycle feeRecipient bidValue builderIdx proposerIdx
      attestedWeight quorum timing = [⟨feeRecipient, bidValue, builderIdx⟩] := by
  have h_q0 : quorum ≠ 0 := by omega
  dsimp [settle_slot_bid_lifecycle, settle_builder_payment, process_builder_pending_payments]
  cases timing
  · rcases h_timely with h_conf | h_att
    · contradiction
    · simp [h_bid, h_q0, h_att]
  · simp [h_bid, h_q0]
  · simp [h_bid, h_q0]
  · simp [h_bid, h_q0]

/-! ## 2. Builder Solvency (`T-7732-BUILDER-SOLVENCY`), Supply Neutrality (`T-7732-NO-ETH-MINTING`),
    and Exit Safety (`T-7732-EXIT-SAFETY`) -/

/-- Exact `get_pending_balance_to_withdraw_for_builder` (`beacon-chain.md:1168-1179`). -/
def get_pending_balance_to_withdraw_for_builder
    (pendingWithdrawals : List BuilderPendingWithdrawal)
    (pendingPayments : List BuilderPendingPayment)
    (builderIndex : Nat) : Nat :=
  let wSum :=
    pendingWithdrawals.foldl
      (fun acc w => if w.builderIndex == builderIndex then acc + w.amount else acc) 0
  let pSum :=
    pendingPayments.foldl
      (fun acc p => if p.withdrawal.builderIndex == builderIndex then acc + p.withdrawal.amount else acc) 0
  wSum + pSum

/-- Exact `can_builder_cover_bid` (`beacon-chain.md:1184-1193`). -/
def can_builder_cover_bid (builderBalance pendingToWithdraw bidAmount : Nat) : Bool :=
  let minBalance := MIN_DEPOSIT_AMOUNT + pendingToWithdraw
  if builderBalance < minBalance then false
  else decide (builderBalance - minBalance ≥ bidAmount)

/-- T-7732-BUILDER-SOLVENCY: `can_builder_cover_bid = true` guarantees that the builder's
balance covers `MIN_DEPOSIT_AMOUNT` plus all pending withdrawals/payments plus `bidAmount`. -/
theorem t_7732_builder_solvency (builderBalance pendingToWithdraw bidAmount : Nat)
    (h : can_builder_cover_bid builderBalance pendingToWithdraw bidAmount = true) :
    builderBalance ≥ MIN_DEPOSIT_AMOUNT + pendingToWithdraw + bidAmount := by
  dsimp only [can_builder_cover_bid] at h
  split at h
  · contradiction
  · simp only [decide_eq_true_eq] at h
    omega

/-- Exact `get_builder_balance_after_withdrawals` (`beacon-chain.md:1895-1906`) and
`apply_withdrawals` (`beacon-chain.md:1997-2007`):
When a builder's balance covers `withdrawn` (guaranteed by `can_builder_cover_bid` and
sweep accounting), `saturatingSub builderBalance withdrawn` equals exact subtraction
`builderBalance - withdrawn` with zero saturation inflation. -/
theorem t_7732_builder_withdrawal_no_underflow (builderBalance withdrawn : Nat)
    (h_solv : withdrawn ≤ builderBalance) :
    saturatingSub builderBalance withdrawn + withdrawn = builderBalance := by
  unfold saturatingSub
  split <;> omega

/-- T-7732-NO-ETH-MINTING (Potuz Property 1 — Supply Neutrality of Builder Bids):
For any committed builder bid validated by `can_builder_cover_bid` (`beacon-chain.md:1184-1193`,
`2179`) and settled through `settle_slot_bid_lifecycle` (`apply_parent_execution_payload` /
`process_builder_pending_payments`) and `apply_withdrawals` (`beacon-chain.md:1997-2007`),
the builder's post-withdrawal Beacon Chain balance plus the execution-layer withdrawal credited
to `feeRecipient` equals the builder's pre-settlement balance (`postBuilderBalance + settled =
builderBalance`), and the builder's remaining balance stays at or above `MIN_DEPOSIT_AMOUNT +
pendingToWithdraw`. Thus builder bids never mint or destroy ETH across CL + EL. -/
theorem t_7732_no_eth_minting
    (builderBalance pendingToWithdraw feeRecipient bidValue builderIdx proposerIdx
      attestedWeight quorum : Nat)
    (timing : ChildConfirmationTiming)
    (h_cover : can_builder_cover_bid builderBalance pendingToWithdraw bidValue = true)
    (h_quorum : quorum > 0) :
    let settled :=
      sum_withdrawal_amounts
        (settle_slot_bid_lifecycle feeRecipient bidValue builderIdx proposerIdx
          attestedWeight quorum timing)
    let postBuilderBalance := saturatingSub builderBalance settled
    postBuilderBalance + settled = builderBalance ∧
    postBuilderBalance ≥ MIN_DEPOSIT_AMOUNT + pendingToWithdraw := by
  have h_solv := t_7732_builder_solvency builderBalance pendingToWithdraw bidValue h_cover
  have h_single :=
    t_7732_single_settlement feeRecipient bidValue builderIdx proposerIdx
      attestedWeight quorum timing h_quorum
  dsimp only
  unfold saturatingSub
  split <;> omega

/-- Exact `is_active_builder` (`beacon-chain.md:1053-1065`):
`builder.deposit_epoch < state.finalized_checkpoint.epoch and builder.withdrawable_epoch == FAR_FUTURE_EPOCH`. -/
def is_active_builder (b : Builder) (finalizedEpoch : Nat) : Bool :=
  b.withdrawableEpoch == FAR_FUTURE_EPOCH && decide (b.depositEpoch < finalizedEpoch)

def can_builder_exit (isActive : Bool) (pendingToWithdraw : Nat) : Bool :=
  isActive && decide (pendingToWithdraw = 0)

/-- T-7732-EXIT-SAFETY: `process_builder_exit_request` (`beacon-chain.md:2368-2384`) only initiates
a builder exit when `pendingToWithdraw = 0`, preventing an exiting builder from defaulting on
pending bids. -/
theorem t_7732_exit_safety (isActive : Bool) (pendingToWithdraw : Nat)
    (h : can_builder_exit isActive pendingToWithdraw = true) :
    isActive = true ∧ pendingToWithdraw = 0 := by
  simpa [can_builder_exit] using h

/-! ## 3. Unconditional Quorum Weight Anti-Double-Counting
    (`T-7732-QUORUM-NO-DOUBLE-COUNT`, `T-7732-QUORUM-WEIGHT-UNCONDITIONAL`,
    `beacon-chain.md:2447-2467`) -/

/-- Single-validator weight accrual step in `process_attestation` (`beacon-chain.md:2447-2467`):
`had_no_participation = (epoch_participation[index] == 0b0000_0000)`.
When `alreadyParticipated = false` (`had_no_participation = true`), the first attestation that sets
a new participation flag transitions `alreadyParticipated` to `true` and adds `effectiveBalance`
to `payment.weight`. Any subsequent attestation for the same validator in the same epoch sees
`alreadyParticipated = true` (`had_no_participation = false`) and leaves `payment.weight`
unchanged. -/
def accrue_attester_weight (alreadyParticipated : Bool) (currentWeight effectiveBalance : Nat) :
    Bool × Nat :=
  if alreadyParticipated then
    (true, currentWeight)
  else
    (true, currentWeight + effectiveBalance)

/-- Multi-attestation fold for a validator across an arbitrary sequence of attestations in an epoch
(`beacon-chain.md:2445-2467`), where each `willSetNewFlag : Bool` indicates whether that
attestation sets a new participation flag for the validator. -/
def accrue_attester_weight_trace
    (alreadyParticipated : Bool) (currentWeight effectiveBalance : Nat)
    (steps : List Bool) : Bool × Nat :=
  steps.foldl
    (fun (st : Bool × Nat) willSetNewFlag =>
      if willSetNewFlag then
        accrue_attester_weight st.1 st.2 effectiveBalance
      else
        st)
    (alreadyParticipated, currentWeight)

/-- T-7732-QUORUM-NO-DOUBLE-COUNT: Two attestations from the same validator within the same epoch
add `effectiveBalance` to `payment.weight` at most once (`beacon-chain.md:2447-2467`). -/
theorem t_7732_quorum_no_double_count (w eb : Nat) :
    let (flag1, w1) := accrue_attester_weight false w eb
    let (_, w2) := accrue_attester_weight flag1 w1 eb
    w2 = w + eb := rfl

private theorem accrue_attester_weight_trace_already_participated
    (w eb : Nat) (steps : List Bool) :
    (accrue_attester_weight_trace true w eb steps).2 = w := by
  induction steps generalizing w with
  | nil => rfl
  | cons willSet rest ih =>
    dsimp [accrue_attester_weight_trace]
    cases willSet <;> simp [accrue_attester_weight, accrue_attester_weight_trace] at ih ⊢ <;> exact ih w

/-- T-7732-QUORUM-WEIGHT-UNCONDITIONAL: Unconditionally across any arbitrary sequence of
attestations `steps : List Bool` in an epoch, a single validator contributes at most
`effectiveBalance` to `payment.weight` (`beacon-chain.md:2447-2467`). -/
theorem t_7732_quorum_weight_unconditional
    (alreadyParticipated : Bool) (w eb : Nat) (steps : List Bool) :
    (accrue_attester_weight_trace alreadyParticipated w eb steps).2 ≤
      w + (if alreadyParticipated then 0 else eb) := by
  induction steps generalizing alreadyParticipated w with
  | nil =>
    dsimp [accrue_attester_weight_trace]
    omega
  | cons willSet rest ih =>
    cases alreadyParticipated
    · cases willSet
      · change (accrue_attester_weight_trace false w eb rest).2 ≤ w + (if false = true then 0 else eb)
        exact ih false w
      · change (accrue_attester_weight_trace true (w + eb) eb rest).2 ≤ w + (if false = true then 0 else eb)
        rw [accrue_attester_weight_trace_already_participated (w + eb) eb rest]
        simp
    · rw [accrue_attester_weight_trace_already_participated w eb (willSet :: rest)]
      simp

/-! ## 4. Same-Slot Unbundling Resistance (`T-7732-SAME-SLOT-UNBUNDLING`,
    `beacon-chain.md:1841-1854, 2162-2216`) -/

/-- Candidate execution payload for a slot, modeled by its `blockHash` (`payload.block_hash`)
and list of included transactions `transactions`. -/
structure SlotCandidatePayload where
  blockHash : Nat
  transactions : List Nat
  deriving Repr, DecidableEq, BEq

/-- In `process_execution_payload_bid` (`beacon-chain.md:2162-2216`), the beacon block at slot `N`
commits to `state.latest_execution_payload_bid.block_hash = bid.block_hash`.
In `process_parent_execution_payload` (`beacon-chain.md:1841-1854`), a full execution payload for
slot `N` becomes canonical if and only if `child_bid.parent_block_hash == parent_bid.block_hash`
(and if not, slot `N` is canonical with an empty payload, so no slot-`N` execution transactions
take effect). -/
def is_canonical_full_slot_payload (committedBidBlockHash : Nat) (candidate : SlotCandidatePayload) : Bool :=
  candidate.blockHash == committedBidBlockHash

/-- T-7732-SAME-SLOT-UNBUNDLING (Potuz Property 3 — Same-Slot Unbundling Resistance):
Suppose at slot `N`:
1. The unique consensus block at slot `N` commits via `process_execution_payload_bid`
   (`beacon-chain.md:2215`) to the builder's bid hash `committedBidBlockHash = builderPayload.blockHash`.
2. `block_hash` is collision-resistant across candidate payloads at slot `N`
   (`candidate.blockHash = builderPayload.blockHash → candidate = builderPayload`).
Then for any candidate execution payload `candidate` that becomes canonical at slot `N`
(`is_canonical_full_slot_payload committedBidBlockHash candidate = true`) and includes a private
transaction `txPriv` (`txPriv ∈ candidate.transactions`), `candidate` is necessarily the builder's
own committed payload (`candidate = builderPayload ∧ txPriv ∈ builderPayload.transactions`). No
other canonical block at slot `N` can unbundle and include `txPriv`. -/
theorem t_7732_same_slot_unbundling
    (committedBidBlockHash txPriv : Nat)
    (builderPayload candidate : SlotCandidatePayload)
    (h_bid_commit : committedBidBlockHash = builderPayload.blockHash)
    (h_hash_inj : candidate.blockHash = builderPayload.blockHash → candidate = builderPayload)
    (h_canonical : is_canonical_full_slot_payload committedBidBlockHash candidate = true)
    (h_tx_in : txPriv ∈ candidate.transactions) :
    candidate = builderPayload ∧ txPriv ∈ builderPayload.transactions := by
  unfold is_canonical_full_slot_payload at h_canonical
  rw [beq_iff_eq] at h_canonical
  have h_hash_eq : candidate.blockHash = builderPayload.blockHash := by
    omega
  have h_eq : candidate = builderPayload := h_hash_inj h_hash_eq
  subst h_eq
  exact ⟨rfl, h_tx_in⟩

/-! ## 5. Faithful `slash_validator` Pending-Payment Loop (`beacon-chain.md:1549-1582`),
    `F-7732-SLASHED-PAYMENT-RESURRECTION`, and `T-7732-SLASHED-NO-RESURRECTION` -/

/-- Exact transcription of the Gloas addition in `slash_validator` (`beacon-chain.md:1578-1581`):
```python
for payment_index, payment in enumerate(state.builder_pending_payments):
    if payment.proposer_index == slashed_index:
        state.builder_pending_payments[payment_index] = BuilderPendingPayment.empty()
```
Clears every pending payment entry in `state.builder_pending_payments` whose `proposer_index`
equals `slashedIndex`. -/
def slash_validator_pending_payments
    (slashedIndex : Nat) (payments : List BuilderPendingPayment) :
    List BuilderPendingPayment :=
  payments.map (fun payment =>
    if payment.proposerIndex == slashedIndex then {} else payment)

/-- Every entry in `slash_validator_pending_payments slashedIndex payments` whose original
or remaining `proposerIndex` equals `slashedIndex` has `withdrawal.amount = 0` and `weight = 0`. -/
theorem t_7732_slash_validator_clears_matching_payments
    (slashedIndex : Nat) (payment : BuilderPendingPayment)
    (h_match : payment.proposerIndex = slashedIndex) :
    (slash_validator_pending_payments slashedIndex [payment]) = [{}] := by
  simp [slash_validator_pending_payments, h_match]

/-- Unpatched `v1.7.0-beta.4` (`aa16bb4c`) `slash_validator` + `apply_parent_execution_payload`
(`beacon-chain.md:1579-1581, 1799-1814`):
`slash_validator` clears all matching entries in `state.builder_pending_payments` (PR #5719),
setting `pendingPaymentSlotAmount := 0`, but leaves `state.latest_execution_payload_bid.value > 0`.
When `parentEpoch + 1 < currentEpoch` (`parent_epoch < get_previous_epoch(state)`, 2+ missed epochs),
`apply_parent_execution_payload` falls into `elif parent_bid.value > 0:` (`lines 1805-1814`) and
resurrects the slashed proposer's withdrawal directly from `parent_bid.value`! -/
def apply_parent_payment_v170_beta4_buggy (s : GloasParentPaymentState) : GloasParentPaymentState :=
  let slotPayment := if s.parentProposerSlashed then 0 else s.pendingPaymentSlotAmount
  if s.parentEpoch == s.currentEpoch || s.parentEpoch + 1 == s.currentEpoch then
    if slotPayment > 0 then
      { s with
        pendingPaymentSlotAmount := 0
        pendingWithdrawals := s.pendingWithdrawals ++
          [⟨s.latestBidFeeRecipient, slotPayment, s.latestBidBuilderIndex⟩] }
    else
      { s with pendingPaymentSlotAmount := 0 }
  else if s.latestBidValue > 0 then
    { s with
      pendingWithdrawals := s.pendingWithdrawals ++
        [⟨s.latestBidFeeRecipient, s.latestBidValue, s.latestBidBuilderIndex⟩] }
  else
    s

/-- Patched `slash_validator` + `apply_parent_execution_payload`:
Slashing the parent proposer zeroes `latestBidValue` (or gates the `elif parent_bid.value > 0`
branch on `not state.validators[parent_proposer_index].slashed`) alongside
`builder_pending_payments[payment_index]`, preventing payment resurrection across any number of
missed epochs. -/
def apply_parent_payment_patched (s : GloasParentPaymentState) : GloasParentPaymentState :=
  let slotPayment := if s.parentProposerSlashed then 0 else s.pendingPaymentSlotAmount
  let bidValue := if s.parentProposerSlashed then 0 else s.latestBidValue
  if s.parentEpoch == s.currentEpoch || s.parentEpoch + 1 == s.currentEpoch then
    if slotPayment > 0 then
      { s with
        pendingPaymentSlotAmount := 0
        latestBidValue := bidValue
        pendingWithdrawals := s.pendingWithdrawals ++
          [⟨s.latestBidFeeRecipient, slotPayment, s.latestBidBuilderIndex⟩] }
    else
      { s with pendingPaymentSlotAmount := 0, latestBidValue := bidValue }
  else if bidValue > 0 then
    { s with
      latestBidValue := bidValue
      pendingWithdrawals := s.pendingWithdrawals ++
        [⟨s.latestBidFeeRecipient, bidValue, s.latestBidBuilderIndex⟩] }
  else
    { s with latestBidValue := bidValue }

/-- T-7732-SLASHED-NO-RESURRECTION: On the patched specification, if `parentProposerSlashed = true`,
`apply_parent_execution_payload` never appends a `BuilderPendingWithdrawal` regardless of how
many epochs elapsed between the parent block and the child block. -/
theorem t_7732_slashed_no_resurrection (s : GloasParentPaymentState)
    (h_slashed : s.parentProposerSlashed = true) :
    (apply_parent_payment_patched s).pendingWithdrawals = s.pendingWithdrawals := by
  unfold apply_parent_payment_patched
  simp [h_slashed]
  split <;> rfl

/-- Explicit `WitnessRefuter` proving the bug `F-7732-SLASHED-PAYMENT-RESURRECTION` in
`ethereum/consensus-specs` `v1.7.0-beta.4` (`aa16bb4c`): when `parentProposerSlashed = true`
and `parentEpoch = 4, currentEpoch = 6`, `apply_parent_payment_v170_beta4_buggy` resurrects
the 1,000,000 Gwei withdrawal for the slashed proposer. -/
def f_7732_slashed_payment_resurrection_refuter :
    WitnessRefuter GloasParentPaymentState GloasParentPaymentState
      (fun pre post => pre.parentProposerSlashed = true → post.pendingWithdrawals = pre.pendingWithdrawals) where
  reference := apply_parent_payment_patched
  mutant := apply_parent_payment_v170_beta4_buggy
  ref_sound := fun s h => t_7732_slashed_no_resurrection s h
  killWitness := {
    parentEpoch := 4
    currentEpoch := 6
    parentProposerSlashed := true
    latestBidValue := 1000000
    latestBidFeeRecipient := 0xab
    latestBidBuilderIndex := 0
    pendingPaymentSlotAmount := 0
    pendingWithdrawals := []
    builderBalance := MIN_DEPOSIT_AMOUNT + 1000000
    builderWithdrawableEpoch := FAR_FUTURE_EPOCH
    untouchedCl := ⟨1, 2, 3⟩
  }
  mutant_refuted := by decide

/-- Multi-step operational trace of `process_execution_payload_bid` -> `slash_validator` ->
`2x process_builder_pending_payments` -> `apply_parent_execution_payload` (`beacon-chain.md:1579-1581`,
`1719-1732`, `1784-1831`):
1. At parent slot in `parentEpoch`, `process_execution_payload_bid` records `latestBidValue := bidValue`
   and populates `secondEpochPayments[slotIdx]` with `amount := bidValue, proposerIndex := headerProposer`.
2. In `slash_validator` (`beacon-chain.md:1579-1581`), `slash_validator_pending_payments` iterates over
   `state.builder_pending_payments` and clears every entry with `payment.proposer_index == slashedIdx`
   to `{}`, while leaving `state.latest_execution_payload_bid.value` (`latestBidValue`) untouched!
3. Two epoch boundaries pass without a block (`process_builder_pending_payments` runs twice, rotating
   and clearing both halves of `builder_pending_payments`).
4. Child block arrives at `currentEpoch ≥ parentEpoch + 2` and runs `apply_parent_execution_payload`,
   which enters the `elif parent_bid.value > 0:` branch (`parent_epoch < previous_epoch`, lines 1805-1814)
   and appends `latestBidValue` to `builder_pending_withdrawals`! -/
def trace_bid_slash_rotate_apply_v170_beta4
    (bidValue feeRecipient builderIdx headerProposer slashedIdx : Nat) :
    List BuilderPendingWithdrawal :=
  let paymentAfterBid : BuilderPendingPayment :=
    { weight := 0
      withdrawal := ⟨feeRecipient, bidValue, builderIdx⟩
      proposerIndex := headerProposer }
  let paymentsAfterSlash := slash_validator_pending_payments slashedIdx [paymentAfterBid]
  let latestBidAfterSlash : Nat := bidValue
  let (first1, second1, w1) := process_builder_pending_payments 1 [{}] paymentsAfterSlash []
  let (_, _, w2) := process_builder_pending_payments 1 first1 second1 w1
  let s : GloasParentPaymentState := {
    parentEpoch := 4
    currentEpoch := 6
    parentProposerSlashed := (slashedIdx == headerProposer)
    latestBidValue := latestBidAfterSlash
    latestBidFeeRecipient := feeRecipient
    latestBidBuilderIndex := builderIdx
    pendingPaymentSlotAmount := 0
    pendingWithdrawals := w2
    builderBalance := MIN_DEPOSIT_AMOUNT + bidValue
    builderWithdrawableEpoch := FAR_FUTURE_EPOCH
    untouchedCl := ⟨1, 2, 3⟩
  }
  (apply_parent_payment_v170_beta4_buggy s).pendingWithdrawals

theorem t_7732_composed_trace_resurrects_slashed_payment :
    trace_bid_slash_rotate_apply_v170_beta4 1000000 0xab 0 42 42 = [⟨0xab, 1000000, 0⟩] := by
  decide

/-! ## 6. Deferred Execution Equivalence (`T-7732-DEFERRED-EXEC-EQUIV`) & Frame Theorem (`T-7732-FRAME`) -/

/-- T-7732-DEFERRED-EXEC-EQUIV: When `bid.parent_block_hash != parent_bid.block_hash` (empty parent),
`process_parent_execution_payload` (`beacon-chain.md:1841-1854`) leaves builder pending withdrawals,
builder balances, and builder exit epochs untouched. -/
def process_parent_payload_if_full (isParentFull : Bool) (s : GloasParentPaymentState) :
    GloasParentPaymentState :=
  if isParentFull then apply_parent_payment_patched s else s

theorem t_7732_deferred_exec_equiv_empty (s : GloasParentPaymentState) :
    process_parent_payload_if_full false s = s := rfl

/-- T-7732-FRAME: All EIP-7732 parent payload and builder payment transitions preserve
untouched Consensus Layer state invariants (validator deposits/exits, BLS-to-execution
changes, sync committee duties). -/
def eip7732_frame_invariant : FrameInvariant GloasParentPaymentState Bool UntouchedClInvariants where
  project := fun s => s.untouchedCl
  step := fun s isFull => process_parent_payload_if_full isFull s
  preserved := by
    intro s isFull
    dsimp only [process_parent_payload_if_full, apply_parent_payment_patched]
    repeat (first | rfl | split)

theorem t_7732_frame (s : GloasParentPaymentState) (steps : List Bool) :
    (steps.foldl (fun st isFull => process_parent_payload_if_full isFull st) s).untouchedCl =
      s.untouchedCl :=
  eip7732_frame_invariant.preserved_list s steps

/-! ## 7. EIP-8282 -> EIP-7732 Builder Queue Closure (`T-8282-7732-QUEUE-SAFETY`) and
    Cross-Function Credential-Check Divergence (`beacon-chain.md:2334-2361` vs `fork.md:70-120`) -/

/-- Under Gloas (`process_parent_execution_payload:1841-1854`), `bid.parent_block_hash` is compared
against `parent_bid.block_hash`: when `bidParentBlockHash ≠ parentBidBlockHash` (EMPTY parent),
`block.body.parent_execution_requests` MUST be empty (`requestsEmpty = true`); when
`bidParentBlockHash = parentBidBlockHash` (FULL parent), `hash_tree_root(requests)` (`requestsRoot`)
MUST equal `parent_bid.execution_requests_root` (`parentCommittedRoot`). -/
def valid_parent_execution_requests (bidParentBlockHash parentBidBlockHash : Nat)
    (requestsEmpty : Bool) (requestsRoot parentCommittedRoot : Nat) : Bool :=
  if bidParentBlockHash != parentBidBlockHash then
    requestsEmpty
  else
    requestsRoot == parentCommittedRoot

theorem t_8282_7732_queue_safety (bidParentBlockHash parentBidBlockHash : Nat)
    (requestsEmpty : Bool) (requestsRoot parentCommittedRoot : Nat) :
    valid_parent_execution_requests bidParentBlockHash parentBidBlockHash
        requestsEmpty requestsRoot parentCommittedRoot = true ↔
      ((bidParentBlockHash ≠ parentBidBlockHash ∧ requestsEmpty = true) ∨
       (bidParentBlockHash = parentBidBlockHash ∧ requestsRoot = parentCommittedRoot)) := by
  unfold valid_parent_execution_requests
  by_cases h_eq : bidParentBlockHash = parentBidBlockHash <;> simp [h_eq]

/-- Input to `process_builder_deposit_request` (`beacon-chain.md:2334-2361`) and
`onboard_builders_from_pending_deposits` (`fork.md:70-120`). -/
structure BuilderDepositStep where
  pubkeyRegistered : Bool
  credentialPrefix : Nat
  signatureValid : Bool
  currentBalance : Nat
  depositAmount : Nat
  deriving Repr, DecidableEq, BEq

/-- `process_builder_deposit_request` (`beacon-chain.md:2334-2361` @ `v1.7.0-beta.4`):
Checks `if not is_builder_withdrawal_credential(request.withdrawal_credentials): return` at line 2336
BEFORE checking `if request.pubkey not in builder_pubkeys:` at line 2340!
If an existing builder (`pubkeyRegistered = true`) submits a top-up with a non-`0xB0` credential
prefix (e.g., `0x00` or `0x01`), the deposit is silently ignored and the ETH burned on the EL is
not credited on the CL, diverging from `onboard_builders_from_pending_deposits` in `fork.md:92-118`
(which checks `if deposit.pubkey not in builder_pubkeys:` at line 92 first and credits top-ups at
lines 115-117 without checking `withdrawal_credentials`). -/
def process_builder_deposit_v170_beta4_buggy (s : BuilderDepositStep) : Nat :=
  if s.credentialPrefix != BUILDER_WITHDRAWAL_PREFIX then
    s.currentBalance
  else if !s.pubkeyRegistered then
    if s.signatureValid then s.depositAmount else s.currentBalance
  else
    s.currentBalance + s.depositAmount

/-- Top-up-permissive `process_builder_deposit_request` (matching `fork.md:92-118`):
Checks `if request.pubkey not in builder_pubkeys:` first, so top-ups to already-registered builders
always credit `builder.balance += request.amount` regardless of `withdrawal_credentials`. -/
def process_builder_deposit_eip8282_patched (s : BuilderDepositStep) : Nat :=
  if !s.pubkeyRegistered then
    if s.credentialPrefix == BUILDER_WITHDRAWAL_PREFIX && s.signatureValid then
      s.depositAmount
    else
      s.currentBalance
  else
    s.currentBalance + s.depositAmount

/-- Explicit `WitnessRefuter` for `F-8282-TOPUP-CREDENTIAL-PREFIX-DROP`:
For an existing builder (`pubkeyRegistered = true`, `currentBalance = 1,000,000,000`), a top-up of
`500,000,000` Gwei with `credentialPrefix = 0x00` is credited by `process_builder_deposit_eip8282_patched`
(`1,500,000,000`) but dropped by `process_builder_deposit_v170_beta4_buggy` (`1,000,000,000`). -/
def f_8282_topup_credential_prefix_drop_refuter :
    WitnessRefuter BuilderDepositStep Nat
      (fun s postBal => s.pubkeyRegistered = true → postBal = s.currentBalance + s.depositAmount) where
  reference := process_builder_deposit_eip8282_patched
  mutant := process_builder_deposit_v170_beta4_buggy
  ref_sound := by
    intro s h_reg
    simp [process_builder_deposit_eip8282_patched, h_reg]
  killWitness := {
    pubkeyRegistered := true
    credentialPrefix := 0x00
    signatureValid := false
    currentBalance := MIN_DEPOSIT_AMOUNT
    depositAmount := 500000000
  }
  mutant_refuted := by decide

/-- Cross-function divergence in `onboard_builders_from_pending_deposits` (`fork.md:70-120` vs
`beacon-chain.md:2336`):
In `onboard_builders_from_pending_deposits` (`fork.md:92-118`), `if deposit.pubkey not in builder_pubkeys:`
is checked at line 92 before `if not is_builder_withdrawal_credential(deposit.withdrawal_credentials):`
at line 93. Thus a pending deposit in `state.pending_deposits` with `is_builder_withdrawal_credential == false`
(e.g., `0x01`) whose `pubkey` is already in `builder_pubkeys` (registered by an earlier `0xB0` deposit in
the same queue) enters the `else:` branch at lines 115-117 and is consumed into
`state.builders[builder_index].balance` instead of remaining in `state.pending_deposits`, whereas
`process_builder_deposit_request` (`beacon-chain.md:2336`) checks `is_builder_withdrawal_credential` first. -/
def onboard_pending_deposit_fork_v170_beta4 (s : BuilderDepositStep) : Bool × Nat :=
  if s.pubkeyRegistered then
    (true, s.currentBalance + s.depositAmount)
  else if s.credentialPrefix == BUILDER_WITHDRAWAL_PREFIX then
    if s.signatureValid then (true, s.depositAmount) else (true, s.currentBalance)
  else
    (false, s.currentBalance)

def onboard_pending_deposit_credential_routed (s : BuilderDepositStep) : Bool × Nat :=
  if s.credentialPrefix != BUILDER_WITHDRAWAL_PREFIX then
    (false, s.currentBalance)
  else if s.pubkeyRegistered then
    (true, s.currentBalance + s.depositAmount)
  else if s.signatureValid then
    (true, s.depositAmount)
  else
    (true, s.currentBalance)

def f_7732_fork_onboard_cross_credential_refuter :
    WitnessRefuter BuilderDepositStep (Bool × Nat)
      (fun s out =>
        s.credentialPrefix ≠ BUILDER_WITHDRAWAL_PREFIX → out.1 = false) where
  reference := onboard_pending_deposit_credential_routed
  mutant := onboard_pending_deposit_fork_v170_beta4
  ref_sound := by
    intro s h_ne
    dsimp [onboard_pending_deposit_credential_routed]
    have h_bne : (s.credentialPrefix != BUILDER_WITHDRAWAL_PREFIX) = true := by
      rw [bne_iff_ne]; exact h_ne
    simp [h_bne]
  killWitness := {
    pubkeyRegistered := true
    credentialPrefix := 0x01
    signatureValid := true
    currentBalance := MIN_DEPOSIT_AMOUNT
    depositAmount := 32000000000
  }
  mutant_refuted := by decide

/-! ## 8. `F-7732-FORK-SLOT-AVAILABILITY-BIT-HIGH` (`fork.md:198-200`) and
    `F-7732-AVAILABILITY-RING-BUFFER-CLOBBER` (`beacon-chain.md:1620-1622, 1829`) -/

/-- Genuine Ring-Buffer State Model for `state.execution_payload_availability`
(`Bitvector[SLOTS_PER_HISTORICAL_ROOT]`, `fork.md:198-200`, `beacon-chain.md:1620-1622, 1829`). -/
structure AvailabilityRing where
  size : Nat
  bits : List (Nat × Bool) := []
  deriving Repr, DecidableEq, BEq

/-- Bit-lookup on `AvailabilityRing` (unwritten slots default to `true`, matching `0b1`
initialization in `upgrade_to_gloas` at `fork.md:199`). -/
def AvailabilityRing.getBit (r : AvailabilityRing) (slot : Nat) : Bool :=
  let idx := slot % r.size
  match r.bits.find? (fun p => p.1 == idx) with
  | some (_, b) => b
  | none => true

def AvailabilityRing.setBit (r : AvailabilityRing) (slot : Nat) (val : Bool) : AvailabilityRing :=
  let idx := slot % r.size
  { r with bits := (idx, val) :: r.bits.filter (fun p => p.1 != idx) }

/-- `process_slot` (`beacon-chain.md:1608-1623`, specifically lines `1620-1622`):
At the end of `process_slot(state)` (just before `state.slot += 1` in `process_slots`),
sets `state.execution_payload_availability[(state.slot + 1) % SLOTS_PER_HISTORICAL_ROOT] = 0b0`. -/
def process_slot_ring (r : AvailabilityRing) (currentSlot : Nat) : AvailabilityRing :=
  r.setBit (currentSlot + 1) false

/-- `apply_parent_execution_payload` (`beacon-chain.md:1784-1831`, specifically line `1829`):
When the child block confirms that the parent block at `parentSlot` had a full payload
(`isParentFull = true`), sets `state.execution_payload_availability[parentSlot % size] = 0b1`. -/
def apply_parent_payload_ring (r : AvailabilityRing) (parentSlot : Nat) (isParentFull : Bool) :
    AvailabilityRing :=
  if isParentFull then r.setBit parentSlot true else r

/-- Finding 1.2 (`F-7732-FORK-SLOT-AVAILABILITY-BIT-HIGH`, `fork.md:198-200`):
At `s_fork`, `upgrade_to_gloas` runs AFTER `process_slots(state, s_fork)` has already completed,
initializing all bits of `execution_payload_availability` to `true` (`0b1`), including `s_fork % size`.
When the fork block at `s_fork` has its payload withheld (`isForkBlockFull = false`), and the next
block at `s_fork + 1` builds on the empty parent (`apply_parent_payload_ring _ s_fork false`),
`getBit s_fork` remains `true` instead of `false`! -/
def fork_slot_availability_v170_beta4_buggy (isForkBlockFull : Bool) : Bool :=
  let r0 : AvailabilityRing := { size := 64, bits := [] }
  let r1 := process_slot_ring r0 64
  let r2 := apply_parent_payload_ring r1 64 isForkBlockFull
  r2.getBit 64

/-- Patched `upgrade_to_gloas`: clears `s_fork % SLOTS_PER_HISTORICAL_ROOT` to `false` during
`upgrade_to_gloas` so `s_fork`'s bit becomes `true` iff `s_fork`'s payload is confirmed. -/
def fork_slot_availability_patched (isForkBlockFull : Bool) : Bool :=
  let r0 : AvailabilityRing := ({ size := 64, bits := [] } : AvailabilityRing).setBit 64 false
  let r1 := process_slot_ring r0 64
  let r2 := apply_parent_payload_ring r1 64 isForkBlockFull
  r2.getBit 64

def f_7732_fork_slot_availability_refuter :
    WitnessRefuter Bool Bool (fun isFull bit => bit = isFull) where
  reference := fork_slot_availability_patched
  mutant := fork_slot_availability_v170_beta4_buggy
  ref_sound := by
    intro isFull
    cases isFull <;> decide
  killWitness := false
  mutant_refuted := by decide

/-- Ring-buffer clobber scenario on `AvailabilityRing` (`F-7732-AVAILABILITY-RING-BUFFER-CLOBBER`,
`beacon-chain.md:1620-1622` vs `1829`):
1. `process_slots` advances to `childSlot` by running `process_slot_ring` at `childSlot - 1`,
   which sets `childSlot % size` to `false`.
2. Next, `process_block` at `childSlot` runs `apply_parent_payload_ring` for `parentSlot`.
When `childSlot - parentSlot = k * size` (`parentSlot % size == childSlot % size`) and
`isParentFull = true`, Step 2 overwrites `childSlot`'s own availability bit back to `true`! -/
def child_slot_availability_after_parent_apply_v170_beta4_buggy
    (slotsPerHistoricalRoot parentSlot childSlot : Nat) (isParentFull : Bool) : Bool :=
  let r0 : AvailabilityRing := { size := slotsPerHistoricalRoot }
  let rAfterProcessSlots := process_slot_ring r0 (childSlot - 1)
  let rAfterParentApply := apply_parent_payload_ring rAfterProcessSlots parentSlot isParentFull
  rAfterParentApply.getBit childSlot

/-- Patched ring-buffer update: skips writing `parentSlot % size = true` when
`childSlot - parentSlot ≥ slotsPerHistoricalRoot` (or clears `childSlot % size` after parent apply),
so `childSlot`'s own availability bit is always `false` before `childSlot`'s child block arrives. -/
def child_slot_availability_after_parent_apply_patched
    (slotsPerHistoricalRoot parentSlot childSlot : Nat) (isParentFull : Bool) : Bool :=
  let r0 : AvailabilityRing := { size := slotsPerHistoricalRoot }
  let rAfterParentApply :=
    if childSlot - parentSlot < slotsPerHistoricalRoot then
      apply_parent_payload_ring r0 parentSlot isParentFull
    else
      r0
  let rAfterSlotClear := (rAfterParentApply).setBit childSlot false
  rAfterSlotClear.getBit childSlot

/-- Explicit `WitnessRefuter` for `F-7732-AVAILABILITY-RING-BUFFER-CLOBBER`:
With `slotsPerHistoricalRoot = 64` (`minimal` preset), `parentSlot = 10`, `childSlot = 74`,
and `isParentFull = true`, `child_slot_availability_after_parent_apply_v170_beta4_buggy`
clobbers `childSlot`'s availability bit to `true`! -/
def f_7732_availability_ring_buffer_clobber_refuter :
    WitnessRefuter (Nat × Nat × Nat × Bool) Bool
      (fun ⟨n, _, _, _⟩ childBitAfterParentApply => n > 0 → childBitAfterParentApply = false) where
  reference := fun ⟨n, p, c, f⟩ => child_slot_availability_after_parent_apply_patched n p c f
  mutant := fun ⟨n, p, c, f⟩ => child_slot_availability_after_parent_apply_v170_beta4_buggy n p c f
  ref_sound := by
    intro ⟨n, p, c, f⟩ _
    dsimp [child_slot_availability_after_parent_apply_patched, AvailabilityRing.getBit, AvailabilityRing.setBit]
    simp
  killWitness := (64, 10, 74, true)
  mutant_refuted := by decide

/-! ## 9. Dual-Pin `consensus-specs#5736` (`8b374fa81b`), `consensus-specs#5763`
    (`1bdf4b8be5`), and Client-Export Bid-Validation Boundaries (`FINDING-028` & `FINDING-031`) -/

/-- Input to the same-key fork onboarding routing decision in `onboard_builders_from_pending_deposits`
(dual-pin of `consensus-specs#5736` @ `8b374fa81b`; base `fork.md:70-120` @ `aa16bb4c`).
`isBuilderCredential` projects `is_builder_withdrawal_credential(withdrawal_credentials)`,
`pubkeyIsExistingValidator` projects `deposit.pubkey in validator_pubkeys`,
`pubkeyIsRegisteredBuilder` projects `deposit.pubkey in builder_pubkeys` (recomputed each
iteration), and `pubkeyIsPendingValidator` projects `is_pending_validator(pending_deposits, pubkey)`. -/
structure ForkOnboardingDeposit where
  isBuilderCredential : Bool
  pubkeyIsExistingValidator : Bool
  pubkeyIsRegisteredBuilder : Bool
  pubkeyIsPendingValidator : Bool
  signatureValid : Bool
  currentBuilderBalance : Nat
  depositAmount : Nat
  deriving Repr, DecidableEq, BEq

/-- Per-deposit onboarding outcome: `consumedFromPending` is `false` iff the deposit is appended
back to `pending_deposits`; `builderBalanceAfter` is the same-key builder balance after this step
(or `currentBuilderBalance` when no builder was credited); `registeredNewBuilder` is `true` iff
`add_builder_to_registry` is invoked (base balance `depositAmount`). -/
structure ForkOnboardingOutcome where
  consumedFromPending : Bool
  builderBalanceAfter : Nat
  registeredNewBuilder : Bool
  deriving Repr, DecidableEq, BEq

/-- Patched `onboard_builders_from_pending_deposits` per-deposit routing (`consensus-specs#5736`
@ `8b374fa81b`):
1. Non-builder-credential deposits (`isBuilderCredential = false`) ALWAYS stay queued, even when a
   builder with the same pubkey is already registered (cross-credential key collision is not a
   builder top-up).
2. A builder-credential deposit for an already-registered builder credits
   `currentBuilderBalance + depositAmount` without any signature check.
3. A builder-credential deposit for a NEW pubkey with a valid signature registers a new builder
   with balance `depositAmount` (a validator may share the pubkey).
4. A builder-credential deposit for a NEW pubkey with an INVALID signature is dropped (consumed,
   not credited), UNLESS an existing or earlier-valid pending validator shares the pubkey, in
   which case it stays queued as a validator top-up. -/
def onboard_builders_pending_deposit_pr5736 (d : ForkOnboardingDeposit) : ForkOnboardingOutcome :=
  if !d.isBuilderCredential then
    { consumedFromPending := false
      builderBalanceAfter := d.currentBuilderBalance
      registeredNewBuilder := false }
  else if d.pubkeyIsRegisteredBuilder then
    { consumedFromPending := true
      builderBalanceAfter := d.currentBuilderBalance + d.depositAmount
      registeredNewBuilder := false }
  else if d.signatureValid then
    { consumedFromPending := true
      builderBalanceAfter := d.depositAmount
      registeredNewBuilder := true }
  else if d.pubkeyIsExistingValidator || d.pubkeyIsPendingValidator then
    { consumedFromPending := false
      builderBalanceAfter := d.currentBuilderBalance
      registeredNewBuilder := false }
  else
    { consumedFromPending := true
      builderBalanceAfter := d.currentBuilderBalance
      registeredNewBuilder := false }

/-- Pre-#5736 `v1.7.0-beta.4` fork routing (`fork.md:70-120` @ `aa16bb4c`): the first
`if deposit.pubkey in validator_pubkeys:` gate keeps every existing-validator deposit queued,
even a valid builder-credential registration, and the `else:` branch at `fork.md:115-117`
credits non-builder-credential deposits to a same-key builder. -/
def onboard_builders_pending_deposit_v170_beta4 (d : ForkOnboardingDeposit) : ForkOnboardingOutcome :=
  if d.pubkeyIsExistingValidator then
    { consumedFromPending := false
      builderBalanceAfter := d.currentBuilderBalance
      registeredNewBuilder := false }
  else if d.pubkeyIsRegisteredBuilder then
    { consumedFromPending := true
      builderBalanceAfter := d.currentBuilderBalance + d.depositAmount
      registeredNewBuilder := false }
  else if !d.isBuilderCredential then
    { consumedFromPending := false
      builderBalanceAfter := d.currentBuilderBalance
      registeredNewBuilder := false }
  else if d.pubkeyIsPendingValidator then
    { consumedFromPending := false
      builderBalanceAfter := d.currentBuilderBalance
      registeredNewBuilder := false }
  else if d.signatureValid then
    { consumedFromPending := true
      builderBalanceAfter := d.depositAmount
      registeredNewBuilder := true }
  else
    { consumedFromPending := true
      builderBalanceAfter := d.currentBuilderBalance
      registeredNewBuilder := false }

/-- T-7732-PR5736-SAME-KEY-VALIDATOR-TOPUP-PRESERVED: Exhaustive 4-way partition of
`onboard_builders_pending_deposit_pr5736` (`consensus-specs#5736` @ `8b374fa81b`):
1. Every non-builder-credential deposit (`isBuilderCredential = false`) remains pending and leaves
   `builderBalanceAfter = currentBuilderBalance`, even when the pubkey is a registered builder.
2. Every `0xB0` deposit for an already-registered builder (`pubkeyIsRegisteredBuilder = true`) is
   consumed and tops up `builderBalanceAfter = currentBuilderBalance + depositAmount` regardless of
   `signatureValid` (matching `fork.md` `else: state.builders[builder_index].balance += deposit.amount`).
3. A `0xB0` deposit for an unregistered pubkey with `signatureValid = true` registers a new builder
   with `builderBalanceAfter = depositAmount` even when an existing validator shares the pubkey.
4. A `0xB0` deposit for an unregistered pubkey with `signatureValid = false` stays pending iff an
   existing or pending validator claims that pubkey (otherwise it is consumed and discarded). -/
theorem t_7732_pr5736_same_key_validator_topup_preserved (d : ForkOnboardingDeposit) :
    (d.isBuilderCredential = false →
      (onboard_builders_pending_deposit_pr5736 d).consumedFromPending = false ∧
      (onboard_builders_pending_deposit_pr5736 d).builderBalanceAfter = d.currentBuilderBalance) ∧
    (d.isBuilderCredential = true → d.pubkeyIsRegisteredBuilder = true →
      (onboard_builders_pending_deposit_pr5736 d).consumedFromPending = true ∧
      (onboard_builders_pending_deposit_pr5736 d).registeredNewBuilder = false ∧
      (onboard_builders_pending_deposit_pr5736 d).builderBalanceAfter =
        d.currentBuilderBalance + d.depositAmount) ∧
    (d.isBuilderCredential = true → d.pubkeyIsRegisteredBuilder = false → d.signatureValid = true →
      (onboard_builders_pending_deposit_pr5736 d).registeredNewBuilder = true ∧
      (onboard_builders_pending_deposit_pr5736 d).builderBalanceAfter = d.depositAmount) ∧
    (d.isBuilderCredential = true → d.pubkeyIsRegisteredBuilder = false → d.signatureValid = false →
      ((onboard_builders_pending_deposit_pr5736 d).consumedFromPending = false ↔
        (d.pubkeyIsExistingValidator = true ∨ d.pubkeyIsPendingValidator = true))) := by
  unfold onboard_builders_pending_deposit_pr5736
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h_credential
    simp [h_credential]
  · intro h_credential h_registered
    simp [h_credential, h_registered]
  · intro h_credential h_unregistered h_signature
    simp [h_credential, h_unregistered, h_signature]
  · intro h_credential h_unregistered h_signature
    simp [h_credential, h_unregistered, h_signature]
    cases d.pubkeyIsExistingValidator <;> cases d.pubkeyIsPendingValidator <;> simp

/-- `WitnessRefuter` for the pre-#5736 same-key cross-credential routing: a non-builder-credential
validator top-up (`0x01`) on a pubkey already registered as a builder is consumed and credited to
the builder by `onboard_builders_pending_deposit_v170_beta4`, but correctly stays pending with an
unchanged builder balance under `onboard_builders_pending_deposit_pr5736`. -/
def f_7732_pr5736_same_key_cross_credential_refuter :
    WitnessRefuter ForkOnboardingDeposit ForkOnboardingOutcome
      (fun d out => d.isBuilderCredential = false →
        out.consumedFromPending = false ∧ out.builderBalanceAfter = d.currentBuilderBalance) where
  reference := onboard_builders_pending_deposit_pr5736
  mutant := onboard_builders_pending_deposit_v170_beta4
  ref_sound := by
    intro d h_credential
    have h_preservation :=
      (t_7732_pr5736_same_key_validator_topup_preserved d).1 h_credential
    exact h_preservation
  killWitness := {
    isBuilderCredential := false
    pubkeyIsExistingValidator := false
    pubkeyIsRegisteredBuilder := true
    pubkeyIsPendingValidator := false
    signatureValid := true
    currentBuilderBalance := MIN_DEPOSIT_AMOUNT
    depositAmount := 32000000000
  }
  mutant_refuted := by decide

/-- Consecutive-slot PTC-quorum slice of `should_build_on_full(store, head, slot)` in Gloas
(`consensus-specs#5763` @ `1bdf4b8be5`; Gloas `validator.md`, honest proposer
`prepare_execution_payload` and `signed_execution_payload_bid` construction). Abstracts the
adjacent-slot (`querySlot = parentSlot + 1` with payload locally available) branch that distinguishes
`wallclockSlot` from `proposalSlot`; non-adjacent `PAYLOAD_STATUS_FULL`/`EMPTY` and unavailable-payload
fork-choice branches are orthogonal to the `#5763` slot-argument fix and excluded per `E-FORK-CHOICE`. -/
def should_build_on_full
    (parentSlot querySlot : Nat) (ptcQuorumObservedAtSlot : Bool) : Bool :=
  decide (parentSlot < querySlot) && ptcQuorumObservedAtSlot

/-- Input context for `prepare_execution_payload` and `signed_execution_payload_bid` construction
at a proposal slot (`consensus-specs#5763`): `parentSlot` is the parent block's slot,
`wallclockSlot` is `get_current_slot(store)` when `prepare_execution_payload` runs, `proposalSlot`
is `state.slot` of the block being constructed, `ptcQuorumAtWallclock` / `ptcQuorumAtProposal` are
the PTC-quorum views at those slots, and `parentBidBlockHash` / `parentBidParentBlockHash` are
`state.latest_execution_payload_bid.block_hash` and `.parent_block_hash`. -/
structure ProposalSlotPrepContext where
  parentSlot : Nat
  wallclockSlot : Nat
  proposalSlot : Nat
  ptcQuorumAtWallclock : Bool
  ptcQuorumAtProposal : Bool
  parentBidBlockHash : Nat
  parentBidParentBlockHash : Nat
  deriving Repr, DecidableEq, BEq

/-- Execution parent `block_hash` selected by `signed_execution_payload_bid` at `state.slot`:
`parentBidBlockHash` when `should_build_on_full(store, head, state.slot)` is `true`, otherwise
`parentBidParentBlockHash`. -/
def select_bid_parent_block_hash (ctx : ProposalSlotPrepContext) : Nat :=
  if should_build_on_full ctx.parentSlot ctx.proposalSlot ctx.ptcQuorumAtProposal then
    ctx.parentBidBlockHash
  else
    ctx.parentBidParentBlockHash

/-- Pre-#5763 wall-clock payload preparation: calls `should_build_on_full` at
`get_current_slot(store)` (`wallclockSlot`), which during early preparation (`wallclockSlot =
parentSlot`) selects `parentBidParentBlockHash` even when `proposalSlot = parentSlot + 1` builds
on `parentBidBlockHash`. -/
def select_prepared_parent_block_hash_buggy (ctx : ProposalSlotPrepContext) : Nat :=
  if should_build_on_full ctx.parentSlot ctx.wallclockSlot ctx.ptcQuorumAtWallclock then
    ctx.parentBidBlockHash
  else
    ctx.parentBidParentBlockHash

/-- Patched #5763 proposal-slot payload preparation: `prepare_execution_payload` evaluates
`should_build_on_full(store, head, state.slot)` (`proposalSlot`) instead of `wallclockSlot`. -/
def select_prepared_parent_block_hash_pr5763 (ctx : ProposalSlotPrepContext) : Nat :=
  if should_build_on_full ctx.parentSlot ctx.proposalSlot ctx.ptcQuorumAtProposal then
    ctx.parentBidBlockHash
  else
    ctx.parentBidParentBlockHash

/-- `WitnessRefuter` for the pre-#5763 wall-clock desynchronization: preparing during the parent
slot (`wallclockSlot = 10`, `ptcQuorumAtWallclock = false`) for `proposalSlot = 11` where PTC
quorum holds (`ptcQuorumAtProposal = true`) prepares against `parentBidParentBlockHash` (`0x1111`)
while the bid at `state.slot = 11` commits to `parentBidBlockHash` (`0x2222`), whereas the
#5763-patched `prepare_execution_payload` matches `select_bid_parent_block_hash`. -/
def f_7732_pr5763_wallclock_slot_desync_refuter :
    WitnessRefuter ProposalSlotPrepContext Nat
      (fun ctx preparedHash => preparedHash = select_bid_parent_block_hash ctx) where
  reference := select_prepared_parent_block_hash_pr5763
  mutant := select_prepared_parent_block_hash_buggy
  ref_sound := by
    intro ctx
    rfl
  killWitness := {
    parentSlot := 10
    wallclockSlot := 10
    proposalSlot := 11
    ptcQuorumAtWallclock := false
    ptcQuorumAtProposal := true
    parentBidBlockHash := 0x2222
    parentBidParentBlockHash := 0x1111
  }
  mutant_refuted := by decide

/-- T-7732-PR5763-PROPOSAL-SLOT-AGREEMENT: Under `consensus-specs#5763`, `prepare_execution_payload`
selects the exact execution parent hash committed by `signed_execution_payload_bid` at `state.slot`
(`select_bid_parent_block_hash ctx`), AND selects the full parent (`parentBidBlockHash`) when
`parentBidBlockHash ≠ parentBidParentBlockHash` iff `parentSlot < proposalSlot` and PTC quorum
holds at the proposal slot — independent of `wallclockSlot` and `ptcQuorumAtWallclock`. -/
theorem t_7732_pr5763_proposal_slot_agreement (ctx : ProposalSlotPrepContext) :
    select_prepared_parent_block_hash_pr5763 ctx = select_bid_parent_block_hash ctx ∧
    (ctx.parentBidBlockHash ≠ ctx.parentBidParentBlockHash →
      (select_prepared_parent_block_hash_pr5763 ctx = ctx.parentBidBlockHash ↔
        ctx.parentSlot < ctx.proposalSlot ∧ ctx.ptcQuorumAtProposal = true)) := by
  have h_agree :
      select_prepared_parent_block_hash_pr5763 ctx = select_bid_parent_block_hash ctx := rfl
  refine ⟨h_agree, ?_⟩
  intro h_distinct
  rw [h_agree]
  dsimp [select_bid_parent_block_hash, should_build_on_full]
  by_cases h_lt : ctx.parentSlot < ctx.proposalSlot
  · cases ctx.ptcQuorumAtProposal
    · simp [h_lt, Ne.symm h_distinct]
    · simp [h_lt]
  · simp [h_lt, Ne.symm h_distinct]

/-- Input to proposer-side bid validation (`ExecutionPayloadBid` fields plus the proposer's expected
`fee_recipient`, builder status, solvency, and per-epoch blob limit). `bidValue > 0` activates the
conditional `can_builder_cover_bid` check in `builder-specs` (whereas `consensus-specs` asserts
`can_builder_cover_bid` unconditionally on the external-builder branch); `gasLimitCompatible`
represents `is_gas_limit_target_compatible` solely in `builder-specs` (`consensus-specs` imposes no
gas-limit target compatibility assert in `process_execution_payload_bid`); `blockHash` /
`parentBlockHash` are the bid's `block_hash` / `parent_block_hash`; `blobCommitmentCount` is
`len(bid.blob_kzg_commitments)` and `maxBlobsPerBlock` is
`get_blob_parameters(get_current_epoch(state)).max_blobs_per_block` (`beacon-chain.md:2183-2187`). -/
structure BidValidationInput where
  isActiveBuilder : Bool
  builderVersion : Nat
  bidValue : Nat
  canCoverBid : Bool
  signatureValid : Bool
  slotMatchesState : Bool
  parentBlockHashMatches : Bool
  parentBlockRootMatches : Bool
  prevRandaoMatches : Bool
  gasLimitCompatible : Bool
  feeRecipientMatchesProposer : Bool
  blockHash : Nat
  parentBlockHash : Nat
  blobCommitmentCount : Nat
  maxBlobsPerBlock : Nat
  deriving Repr, DecidableEq, BEq

/-- Shared builder-specs `validate_bid` pre-filter (client-export `FINDING-028` & `FINDING-031`):
checks builder activity, slot, parent hash/root, `prev_randao`, `is_gas_limit_target_compatible`
(`gasLimitCompatible`), conditional solvency (`if bid.value > 0: can_builder_cover_bid`),
signature, and `bid.fee_recipient == fee_recipient`. It OMITS the consensus asserts
`bid.block_hash != bid.parent_block_hash`, `len(bid.blob_kzg_commitments) <= max_blobs_per_block`,
and `builder.version == PAYLOAD_BUILDER_VERSION`. -/
def validate_bid_builder_specs (v : BidValidationInput) : Bool :=
  v.isActiveBuilder && (v.bidValue == 0 || v.canCoverBid) && v.signatureValid &&
    v.slotMatchesState && v.parentBlockHashMatches && v.parentBlockRootMatches &&
    v.prevRandaoMatches && v.gasLimitCompatible && v.feeRecipientMatchesProposer

/-- Consensus `process_execution_payload_bid` validity gate on the external-builder branch
(`builder_index != BUILDER_INDEX_SELF_BUILD`, `beacon-chain.md:2162-2216`):
checks `is_active_builder`, `state.builders[builder_index].version == PAYLOAD_BUILDER_VERSION`,
unconditional `can_builder_cover_bid`, `verify_execution_payload_bid_signature`,
`len(bid.blob_kzg_commitments) <= max_blobs_per_block`, `bid.slot == state.slot`,
`bid.parent_block_hash`, `bid.block_hash != bid.parent_block_hash`, `bid.parent_block_root`, and
`bid.prev_randao` (with NO `is_gas_limit_target_compatible` or `fee_recipient` constraint;
FINDING-031: consensus records `bid.fee_recipient` verbatim). -/
def process_bid_consensus_specs (v : BidValidationInput) : Bool :=
  v.isActiveBuilder && v.canCoverBid && v.signatureValid && v.slotMatchesState &&
    v.parentBlockHashMatches && v.parentBlockRootMatches && v.prevRandaoMatches &&
    (v.builderVersion == PAYLOAD_BUILDER_VERSION) &&
    (v.blobCommitmentCount <= v.maxBlobsPerBlock) && (v.blockHash != v.parentBlockHash)

/-- Aligned proposer-side validation (recommended fix for FINDING-028 & FINDING-031): requires
BOTH the consensus state-transition validity conditions (`process_bid_consensus_specs`) AND the
proposer-side `is_gas_limit_target_compatible` and `bid.fee_recipient == fee_recipient` checks. -/
def validate_bid_aligned (v : BidValidationInput) : Bool :=
  process_bid_consensus_specs v && v.gasLimitCompatible && v.feeRecipientMatchesProposer

/-- T-7732-FINDING-028-031-BID-VALIDATION-BOUNDARY:
1. FINDING-028 (grief): `validate_bid_builder_specs` accepting a bid does NOT imply
   `process_bid_consensus_specs` accepts it (missing `block_hash != parent_block_hash` /
   blob-count / builder-version / zero-value `can_builder_cover_bid`); a proposer using ONLY the
   pre-filter can select a consensus-invalid bid.
2. FINDING-031 (self-payment): `process_bid_consensus_specs` accepting a bid does NOT imply the
   proposer's `fee_recipient` matches; a self-paying bid yields a fully VALID consensus block.
3. `validate_bid_aligned` is accepted iff consensus validity AND the proposer's gas-limit and
   fee-recipient conditions all hold, closing both boundaries. -/
theorem t_7732_finding_028_031_bid_validation_boundary :
    (∃ v : BidValidationInput,
      validate_bid_builder_specs v = true ∧ process_bid_consensus_specs v = false) ∧
    (∃ v : BidValidationInput,
      process_bid_consensus_specs v = true ∧ v.feeRecipientMatchesProposer = false) ∧
    (∀ v : BidValidationInput,
      validate_bid_aligned v = true ↔
        (process_bid_consensus_specs v = true ∧
          v.gasLimitCompatible = true ∧
          v.feeRecipientMatchesProposer = true)) := by
  let griefBid : BidValidationInput := {
    isActiveBuilder := true
    builderVersion := PAYLOAD_BUILDER_VERSION
    bidValue := 1000000
    canCoverBid := true
    signatureValid := true
    slotMatchesState := true
    parentBlockHashMatches := true
    parentBlockRootMatches := true
    prevRandaoMatches := true
    gasLimitCompatible := true
    feeRecipientMatchesProposer := true
    blockHash := 0xdead
    parentBlockHash := 0xdead
    blobCommitmentCount := 7
    maxBlobsPerBlock := 6
  }
  let selfPayingBid : BidValidationInput := {
    isActiveBuilder := true
    builderVersion := PAYLOAD_BUILDER_VERSION
    bidValue := 1000000
    canCoverBid := true
    signatureValid := true
    slotMatchesState := true
    parentBlockHashMatches := true
    parentBlockRootMatches := true
    prevRandaoMatches := true
    gasLimitCompatible := true
    feeRecipientMatchesProposer := false
    blockHash := 0xbeef
    parentBlockHash := 0xdead
    blobCommitmentCount := 6
    maxBlobsPerBlock := 6
  }
  refine ⟨⟨griefBid, by decide⟩, ⟨selfPayingBid, by decide⟩, ?_⟩
  intro v
  unfold validate_bid_aligned
  cases process_bid_consensus_specs v <;>
    cases v.gasLimitCompatible <;>
    cases v.feeRecipientMatchesProposer <;> simp

/-- Concrete FINDING-028 `WitnessRefuter`: `validate_bid_builder_specs` accepts a bid with
`blockHash == parentBlockHash` and `blobCommitmentCount > maxBlobsPerBlock`, which the aligned
validator rejects (so proposer acceptance implies consensus validity under the aligned gate). -/
def f_7732_finding_028_incomplete_prefilter_refuter :
    WitnessRefuter BidValidationInput Bool
      (fun v accepted => accepted = true → process_bid_consensus_specs v = true) where
  reference := validate_bid_aligned
  mutant := validate_bid_builder_specs
  ref_sound := by
    intro v h_accepted
    have h_aligned := (t_7732_finding_028_031_bid_validation_boundary).2.2 v
    exact (h_aligned.mp h_accepted).1
  killWitness := {
    isActiveBuilder := true
    builderVersion := PAYLOAD_BUILDER_VERSION
    bidValue := 1000000
    canCoverBid := true
    signatureValid := true
    slotMatchesState := true
    parentBlockHashMatches := true
    parentBlockRootMatches := true
    prevRandaoMatches := true
    gasLimitCompatible := true
    feeRecipientMatchesProposer := true
    blockHash := 0xdead
    parentBlockHash := 0xdead
    blobCommitmentCount := 7
    maxBlobsPerBlock := 6
  }
  mutant_refuted := by decide

/-- Concrete FINDING-031 `WitnessRefuter`: the consensus-only checklist accepts a self-paying bid
(`feeRecipientMatchesProposer = false`), while `validate_bid_aligned` rejects it; any accepted bid
under the aligned gate pays the proposer's own `fee_recipient`. -/
def f_7732_finding_031_self_paying_bid_refuter :
    WitnessRefuter BidValidationInput Bool
      (fun v accepted => accepted = true → v.feeRecipientMatchesProposer = true) where
  reference := validate_bid_aligned
  mutant := process_bid_consensus_specs
  ref_sound := by
    intro v h_accepted
    have h_aligned := (t_7732_finding_028_031_bid_validation_boundary).2.2 v
    exact (h_aligned.mp h_accepted).2.2
  killWitness := {
    isActiveBuilder := true
    builderVersion := PAYLOAD_BUILDER_VERSION
    bidValue := 1000000
    canCoverBid := true
    signatureValid := true
    slotMatchesState := true
    parentBlockHashMatches := true
    parentBlockRootMatches := true
    prevRandaoMatches := true
    gasLimitCompatible := true
    feeRecipientMatchesProposer := false
    blockHash := 0xbeef
    parentBlockHash := 0xdead
    blobCommitmentCount := 6
    maxBlobsPerBlock := 6
  }
  mutant_refuted := by decide

/-! ## 10. Multi-Builder CL+EL Supply Conservation and Concrete `BeaconState` Frame
    (`apply_withdrawals` at `beacon-chain.md:1997-2007`, `BeaconState` at `862-934`) -/

/-- One execution-layer builder withdrawal (`Withdrawal`): `builderIndex` projects the registry
index recovered by `convert_validator_index_to_builder_index(withdrawal.validator_index)` when
`is_builder_index(withdrawal.validator_index)` holds, `amount` is `withdrawal.amount` in Gwei, and
`executionRecipient` is the EL address credited (`withdrawal.address`). -/
structure BuilderWithdrawal where
  builderIndex : Nat
  amount : Nat
  executionRecipient : Nat
  deriving Repr, DecidableEq, BEq

/-- Concrete `BeaconState` projection (`beacon-chain.md:862-934`) for builder accounting:
`builders` is `state.builders`, `builderPendingWithdrawals` is the queue consumed by
`get_builder_withdrawals`, `validatorBalances` is `state.balances`, and `untouchedCl` captures
every field not written by builder payment/withdrawal transitions (validator registry,
`latest_block_header`, `block_roots`, `state_roots`, `randao_mixes`, `justification_bits`,
`current_sync_committee`, `next_sync_committee`, `ptc_window`, ...). -/
structure GloasBeaconState where
  builders : List Builder
  builderPendingWithdrawals : List BuilderPendingWithdrawal
  validatorBalances : List Nat
  untouchedCl : UntouchedClInvariants
  deriving Repr, DecidableEq, BEq

/-- Total CL Gwei locked in the builder registry (`sum(state.builders[i].balance)`). -/
def total_builders_balance (builders : List Builder) : Nat :=
  builders.foldl (fun acc b => acc + b.balance) 0

/-- Total EL Gwei credited by a batch of builder withdrawals. -/
def total_execution_withdrawal_credit (ws : List BuilderWithdrawal) : Nat :=
  ws.foldl (fun acc w => acc + w.amount) 0

/-- Total Gwei withdrawn from a specific builder index across a withdrawal batch
(`beacon-chain.md:1899-1905`). -/
def builder_withdrawn_in_batch (ws : List BuilderWithdrawal) (builderIdx : Nat) : Nat :=
  ws.foldl (fun acc w => if w.builderIndex == builderIdx then acc + w.amount else acc) 0

/-- Positional list update matching `state.builders[builder_index].balance = saturating_sub(...)`
in `apply_withdrawals` (`beacon-chain.md:1997-2007`). -/
def debit_builder_at_index : List Builder → Nat → Nat → List Builder
  | [], _, _ => []
  | b :: rest, 0, amt => { b with balance := saturatingSub b.balance amt } :: rest
  | b :: rest, idx + 1, amt => b :: debit_builder_at_index rest idx amt

/-- Lookup the balance of `builders[idx]` (`0` when `idx >= builders.length`). -/
def builder_balance_at : List Builder → Nat → Nat
  | [], _ => 0
  | b :: _, 0 => b.balance
  | _ :: rest, idx + 1 => builder_balance_at rest idx

/-- Boolean solvency gate for a batch of builder withdrawals against `builders`
(`beacon-chain.md:1184-1193`, `1895-1906`): every withdrawal references an in-bounds
`builderIndex < builders.length`, and for every withdrawal the builder's initial balance covers
the cumulative withdrawals for that `builderIndex` across the entire batch. -/
def builder_withdrawals_solvency_ok
    (builders : List Builder) (ws : List BuilderWithdrawal) : Bool :=
  ws.all (fun w =>
    decide (w.builderIndex < builders.length) &&
      decide (builder_withdrawn_in_batch ws w.builderIndex ≤
        builder_balance_at builders w.builderIndex))

/-- One `apply_withdrawals` builder-registry update (`beacon-chain.md:2000-2004`): deducts
`w.amount` from `state.builders[w.builderIndex].balance` via `saturatingSub` (and slices the
processed head entry off `builderPendingWithdrawals` when non-empty, `beacon-chain.md:2088`). -/
def apply_builder_withdrawal_step (s : GloasBeaconState) (w : BuilderWithdrawal) : GloasBeaconState :=
  { s with
    builders := debit_builder_at_index s.builders w.builderIndex w.amount
    builderPendingWithdrawals := s.builderPendingWithdrawals.drop 1 }

/-- Batch application of `apply_withdrawals` to all builder-indexed withdrawals
(`beacon-chain.md:1997-2007`), preserving `validatorBalances` and `untouchedCl`. -/
def apply_builder_withdrawals_registry
    (s : GloasBeaconState) (ws : List BuilderWithdrawal) : GloasBeaconState :=
  ws.foldl apply_builder_withdrawal_step s

private theorem foldl_builder_balance_shift (bs : List Builder) (init : Nat) :
    bs.foldl (fun acc b => acc + b.balance) init =
      init + bs.foldl (fun acc b => acc + b.balance) 0 := by
  induction bs generalizing init with
  | nil => simp
  | cons b rest ih =>
    simp only [List.foldl]
    rw [ih (init + b.balance), ih (0 + b.balance)]
    omega

private theorem foldl_withdrawal_amount_shift (ws : List BuilderWithdrawal) (init : Nat) :
    ws.foldl (fun acc w => acc + w.amount) init =
      init + ws.foldl (fun acc w => acc + w.amount) 0 := by
  induction ws generalizing init with
  | nil => simp
  | cons w rest ih =>
    simp only [List.foldl]
    rw [ih (init + w.amount), ih (0 + w.amount)]
    omega

private theorem foldl_builder_withdrawn_shift
    (ws : List BuilderWithdrawal) (idx init : Nat) :
    ws.foldl (fun acc w => if w.builderIndex == idx then acc + w.amount else acc) init =
      init + ws.foldl (fun acc w => if w.builderIndex == idx then acc + w.amount else acc) 0 := by
  induction ws generalizing init with
  | nil => simp
  | cons w rest ih =>
    simp only [List.foldl]
    by_cases h_eq : (w.builderIndex == idx) = true
    · simp only [h_eq, ↓reduceIte]
      rw [ih (init + w.amount), ih (0 + w.amount)]
      omega
    · simp only [h_eq, Bool.false_eq_true, ↓reduceIte]
      exact ih init

private theorem debit_builder_at_index_length
    (bs : List Builder) (idx amt : Nat) :
    (debit_builder_at_index bs idx amt).length = bs.length := by
  induction bs generalizing idx with
  | nil => rfl
  | cons b rest ih =>
    cases idx with
    | zero => rfl
    | succ k =>
      dsimp [debit_builder_at_index]
      rw [ih k]

private theorem builder_balance_at_debit
    (bs : List Builder) (idx amt j : Nat)
    (h_solv : idx = j → amt ≤ builder_balance_at bs idx) :
    builder_balance_at (debit_builder_at_index bs idx amt) j =
      if j = idx then builder_balance_at bs j - amt else builder_balance_at bs j := by
  induction bs generalizing idx j with
  | nil =>
    dsimp [debit_builder_at_index, builder_balance_at]
    split <;> omega
  | cons b rest ih =>
    cases idx with
    | zero =>
      cases j with
      | zero =>
        have h_le : amt ≤ b.balance := h_solv rfl
        dsimp [debit_builder_at_index, builder_balance_at, saturatingSub]
        split <;> omega
      | succ j' =>
        simp [debit_builder_at_index, builder_balance_at]
    | succ idx' =>
      cases j with
      | zero =>
        simp [debit_builder_at_index, builder_balance_at]
      | succ j' =>
        dsimp [debit_builder_at_index, builder_balance_at]
        have h_sub : idx' = j' → amt ≤ builder_balance_at rest idx' := by
          intro h_eq
          exact h_solv (by omega)
        rw [ih idx' j' h_sub]
        by_cases h_eq : j' = idx' <;> simp [h_eq]

private theorem total_builders_balance_debit
    (bs : List Builder) (idx amt : Nat)
    (h_lt : idx < bs.length)
    (h_le : amt ≤ builder_balance_at bs idx) :
    total_builders_balance (debit_builder_at_index bs idx amt) + amt =
      total_builders_balance bs := by
  induction bs generalizing idx with
  | nil =>
    simp at h_lt
  | cons b rest ih =>
    cases idx with
    | zero =>
      dsimp [debit_builder_at_index, total_builders_balance, builder_balance_at, saturatingSub]
        at h_le ⊢
      rw [foldl_builder_balance_shift rest (0 + (if b.balance < amt then 0 else b.balance - amt)),
        foldl_builder_balance_shift rest (0 + b.balance)]
      split <;> omega
    | succ idx' =>
      have h_lt' : idx' < rest.length := by
        simpa using h_lt
      dsimp [builder_balance_at] at h_le
      have h_rec := ih idx' h_lt' h_le
      dsimp [debit_builder_at_index, total_builders_balance] at h_rec ⊢
      rw [foldl_builder_balance_shift (debit_builder_at_index rest idx' amt) (0 + b.balance),
        foldl_builder_balance_shift rest (0 + b.balance)]
      omega

private theorem builder_withdrawn_cons_eq (w : BuilderWithdrawal) (rest : List BuilderWithdrawal) :
    builder_withdrawn_in_batch (w :: rest) w.builderIndex =
      w.amount + builder_withdrawn_in_batch rest w.builderIndex := by
  dsimp [builder_withdrawn_in_batch]
  simp only [beq_self_eq_true, ↓reduceIte]
  rw [foldl_builder_withdrawn_shift rest w.builderIndex (0 + w.amount)]
  omega

private theorem builder_withdrawn_cons_ne
    (w : BuilderWithdrawal) (rest : List BuilderWithdrawal) (j : Nat)
    (h_ne : j ≠ w.builderIndex) :
    builder_withdrawn_in_batch (w :: rest) j =
      builder_withdrawn_in_batch rest j := by
  dsimp [builder_withdrawn_in_batch]
  have h_beq : (w.builderIndex == j) = false := by
    rw [beq_eq_false_iff_ne]
    exact Ne.symm h_ne
  simp only [h_beq, Bool.false_eq_true, ↓reduceIte]

/-- T-7732-MULTI-BUILDER-CL-EL-SUPPLY-CONSERVATION: For an arbitrary batch of builder withdrawals
across MULTIPLE builders, when the batch satisfies `builder_withdrawals_solvency_ok` (every
withdrawal targets an in-bounds builder whose initial balance covers its cumulative withdrawals in
the batch), applying `apply_withdrawals` (`beacon-chain.md:1997-2007`) to the builder registry
debits the exact Execution-Layer withdrawal credit:

  `total_builders_balance post + total_execution_withdrawal_credit ws = total_builders_balance pre`

with zero saturation inflation across any number of builders and multiple withdrawals per builder. -/
theorem t_7732_multi_builder_cl_el_supply_conservation
    (pre : GloasBeaconState) (ws : List BuilderWithdrawal)
    (h_solv : builder_withdrawals_solvency_ok pre.builders ws = true) :
    total_builders_balance (apply_builder_withdrawals_registry pre ws).builders +
        total_execution_withdrawal_credit ws =
      total_builders_balance pre.builders := by
  induction ws generalizing pre with
  | nil =>
    simp [apply_builder_withdrawals_registry, total_execution_withdrawal_credit]
  | cons w rest ih =>
    unfold builder_withdrawals_solvency_ok at h_solv
    rw [List.all_cons, Bool.and_eq_true] at h_solv
    rcases h_solv with ⟨h_head, h_tail⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h_head
    rcases h_head with ⟨h_w_lt, h_w_sum⟩
    have h_w_eq := builder_withdrawn_cons_eq w rest
    have h_w_amt : w.amount ≤ builder_balance_at pre.builders w.builderIndex := by
      omega
    have h_step_total :=
      total_builders_balance_debit pre.builders w.builderIndex w.amount h_w_lt h_w_amt
    have h_next_solv :
        builder_withdrawals_solvency_ok (apply_builder_withdrawal_step pre w).builders rest = true := by
      unfold builder_withdrawals_solvency_ok
      rw [List.all_eq_true] at h_tail ⊢
      intro w' h_in
      have h_orig := h_tail w' h_in
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h_orig ⊢
      rcases h_orig with ⟨h_lt', h_sum'⟩
      refine ⟨?_, ?_⟩
      · dsimp [apply_builder_withdrawal_step]
        rw [debit_builder_at_index_length]
        exact h_lt'
      · dsimp [apply_builder_withdrawal_step]
        have h_bal := builder_balance_at_debit pre.builders w.builderIndex w.amount w'.builderIndex
          (fun _ => h_w_amt)
        rw [h_bal]
        by_cases h_eq : w'.builderIndex = w.builderIndex
        · simp only [h_eq, ↓reduceIte]
          omega
        · simp only [h_eq, ↓reduceIte]
          have h_ne := builder_withdrawn_cons_ne w rest w'.builderIndex h_eq
          omega
    have h_rec := ih (apply_builder_withdrawal_step pre w) h_next_solv
    have h_cons : apply_builder_withdrawals_registry pre (w :: rest) =
        apply_builder_withdrawals_registry (apply_builder_withdrawal_step pre w) rest := rfl
    rw [h_cons]
    have h_credit : total_execution_withdrawal_credit (w :: rest) =
        w.amount + total_execution_withdrawal_credit rest := by
      dsimp [total_execution_withdrawal_credit]
      rw [foldl_withdrawal_amount_shift rest (0 + w.amount)]
      omega
    rw [h_credit]
    have h_step_eq : (apply_builder_withdrawal_step pre w).builders =
        debit_builder_at_index pre.builders w.builderIndex w.amount := rfl
    rw [h_step_eq] at h_rec
    omega

/-- Concrete `BeaconState` frame projection: builder payment/withdrawal processing touches ONLY
`builders` and `builder_pending_withdrawals`, leaving validator balances and all other CL fields
(`untouchedCl`) invariant across arbitrary transition traces. -/
def gloas_beacon_state_frame : FrameInvariant GloasBeaconState BuilderWithdrawal UntouchedClInvariants where
  project := fun s => s.untouchedCl
  step := apply_builder_withdrawal_step
  preserved := by
    intro s w
    rfl

/-- T-7732-CONCRETE-BEACON-STATE-FRAME: Across an arbitrary list of builder-withdrawal operations
(`apply_builder_withdrawals_registry`), the concrete `GloasBeaconState` projection preserves
`untouchedCl` (validator registry root, BLS-to-execution root, sync-committee root) AND
`validatorBalances`; only builder balances and the builder-withdrawal queue are written. -/
theorem t_7732_concrete_beacon_state_frame
    (s : GloasBeaconState) (steps : List BuilderWithdrawal) :
    (apply_builder_withdrawals_registry s steps).untouchedCl = s.untouchedCl ∧
    (apply_builder_withdrawals_registry s steps).validatorBalances = s.validatorBalances := by
  constructor
  · exact gloas_beacon_state_frame.preserved_list s steps
  · induction steps generalizing s with
    | nil => rfl
    | cons w rest ih =>
      exact ih (apply_builder_withdrawal_step s w)

@[inline, export glamsterdam_eip7732_pr5736_onboard_consumed_cabi]
def eip7732_pr5736_onboard_consumed_cabi
    (isBuilderCredential pubkeyIsExistingValidator pubkeyIsRegisteredBuilder : UInt64)
    (pubkeyIsPendingValidator signatureValid : UInt64)
    (currentBuilderBalance depositAmount : UInt64) : Bool :=
  (onboard_builders_pending_deposit_pr5736 {
    isBuilderCredential := isBuilderCredential != 0
    pubkeyIsExistingValidator := pubkeyIsExistingValidator != 0
    pubkeyIsRegisteredBuilder := pubkeyIsRegisteredBuilder != 0
    pubkeyIsPendingValidator := pubkeyIsPendingValidator != 0
    signatureValid := signatureValid != 0
    currentBuilderBalance := currentBuilderBalance.toNat
    depositAmount := depositAmount.toNat
  }).consumedFromPending

@[inline, export glamsterdam_eip7732_pr5736_onboard_builder_balance_cabi]
def eip7732_pr5736_onboard_builder_balance_cabi
    (isBuilderCredential pubkeyIsExistingValidator pubkeyIsRegisteredBuilder : UInt64)
    (pubkeyIsPendingValidator signatureValid : UInt64)
    (currentBuilderBalance depositAmount : UInt64) : UInt64 :=
  (onboard_builders_pending_deposit_pr5736 {
    isBuilderCredential := isBuilderCredential != 0
    pubkeyIsExistingValidator := pubkeyIsExistingValidator != 0
    pubkeyIsRegisteredBuilder := pubkeyIsRegisteredBuilder != 0
    pubkeyIsPendingValidator := pubkeyIsPendingValidator != 0
    signatureValid := signatureValid != 0
    currentBuilderBalance := currentBuilderBalance.toNat
    depositAmount := depositAmount.toNat
  }).builderBalanceAfter.toUInt64

@[inline, export glamsterdam_eip7732_pr5763_should_build_on_full_cabi]
def eip7732_pr5763_should_build_on_full_cabi
    (parentSlot proposalSlot ptcQuorumObservedAtSlot : UInt64) : Bool :=
  should_build_on_full parentSlot.toNat proposalSlot.toNat (ptcQuorumObservedAtSlot != 0)

@[inline, export glamsterdam_eip7732_validate_bid_aligned_cabi]
def eip7732_validate_bid_aligned_cabi
    (isActiveBuilder builderVersion canCoverBid signatureValid slotMatchesState : UInt64)
    (parentBlockHashMatches parentBlockRootMatches prevRandaoMatches gasLimitCompatible : UInt64)
    (feeRecipientMatchesProposer blockHash parentBlockHash : UInt64)
    (blobCommitmentCount maxBlobsPerBlock : UInt64) : Bool :=
  validate_bid_aligned {
    isActiveBuilder := isActiveBuilder != 0
    builderVersion := builderVersion.toNat
    bidValue := 1000000
    canCoverBid := canCoverBid != 0
    signatureValid := signatureValid != 0
    slotMatchesState := slotMatchesState != 0
    parentBlockHashMatches := parentBlockHashMatches != 0
    parentBlockRootMatches := parentBlockRootMatches != 0
    prevRandaoMatches := prevRandaoMatches != 0
    gasLimitCompatible := gasLimitCompatible != 0
    feeRecipientMatchesProposer := feeRecipientMatchesProposer != 0
    blockHash := blockHash.toNat
    parentBlockHash := parentBlockHash.toNat
    blobCommitmentCount := blobCommitmentCount.toNat
    maxBlobsPerBlock := maxBlobsPerBlock.toNat
  }

@[inline, export glamsterdam_eip7732_can_cover_bid_cabi]
def eip7732_can_cover_bid_cabi (builderBalance pendingToWithdraw bidAmount : UInt64) : Bool :=
  can_builder_cover_bid builderBalance.toNat pendingToWithdraw.toNat bidAmount.toNat

@[inline, export glamsterdam_eip7732_quorum_threshold_cabi]
def eip7732_quorum_threshold_cabi (totalActiveBalance slotsPerEpoch : UInt64) : UInt64 :=
  (get_builder_payment_quorum_threshold totalActiveBalance.toNat slotsPerEpoch.toNat).toUInt64

@[inline, export glamsterdam_eip7732_can_builder_exit_cabi]
def eip7732_can_builder_exit_cabi (isActive pendingToWithdraw : UInt64) : Bool :=
  can_builder_exit (isActive != 0) pendingToWithdraw.toNat

end Glamsterdam.Gloas7732.Spec
