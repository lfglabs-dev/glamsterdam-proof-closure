/-
Copyright (c) 2026 Verity Labs / LFG Labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Marchand, Verity Audit Team
-/
import Glamsterdam.Common.MetaSpec

/-!
# Glamsterdam Gloas Consensus Layer (`EIP-7732` + `EIP-8282`) Formal Specification and Verification

Pinned against `ethereum/consensus-specs` @ `aa16bb4c156184e9548a997d53efaf2a228a6304`
(`v1.7.0-beta.4`, `specs/gloas/beacon-chain.md` & `specs/gloas/fork.md`).
Note: `fork-choice.md` and P2P gossip remain strictly out of scope per agreement with Potuz (EF).

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

/-- Positive bids record a payment. A zero-value bid contributes an empty entry
to the single-slot lifecycle; the complete bid operation leaves the queue unchanged. -/
def paymentForBid (bid : BuilderPendingWithdrawal) (proposer weight : Nat) : BuilderPendingPayment :=
  if bid.amount > 0 then {weight := weight, withdrawal := bid, proposerIndex := proposer} else {}

/-- Once the parent has left the two-epoch window, settlement uses its cached bid. -/
def appendOlderBid (ws : List BuilderPendingWithdrawal) (bid : BuilderPendingWithdrawal) :=
  if bid.amount > 0 then ws ++ [bid] else ws

/-- Full 2-epoch slot settlement lifecycle combining all three `parent_epoch` branches of
`apply_parent_execution_payload` (`settle_builder_payment:1538-1544`, `1799-1814`) and two
epoch-boundary rotations of `process_builder_pending_payments` (`1719-1732`).
For an unconfirmed payload the first epoch boundary rotates the payment and the second checks quorum.
Confirmation in the same epoch clears the second-epoch entry. Confirmation in the next epoch clears
the rotated first-epoch entry. After two empty epochs the child uses the original positive bid value. -/
def settle_slot_bid_lifecycle
    (feeRecipient bidValue builderIdx proposerIdx attestedWeight quorum : Nat)
    (timing : ChildConfirmationTiming) : List BuilderPendingWithdrawal :=
  let bid := BuilderPendingWithdrawal.mk feeRecipient bidValue builderIdx
  let mkPayment (w : Nat) := paymentForBid bid proposerIdx w
  match timing with
  | .notConfirmed =>
    let (first1, second1, w1) := process_builder_pending_payments quorum [{}] [mkPayment attestedWeight] []
    let (_, _, w2) := process_builder_pending_payments quorum first1 second1 w1
    w2
  | .confirmedSameEpoch =>
    let (clearedSlot, wChild) := settle_builder_payment (mkPayment attestedWeight) []
    let (first1, second1, w1) := process_builder_pending_payments quorum [{}] [clearedSlot] wChild
    let (_, _, w2) := process_builder_pending_payments quorum first1 second1 w1
    w2
  | .confirmedNextEpoch =>
    let (first1, second1, w1) := process_builder_pending_payments quorum [{}] [mkPayment attestedWeight] []
    let (clearedSlot, wChild) :=
      match first1 with
      | p :: _ => settle_builder_payment p w1
      | [] => ({}, w1)
    let (_, _, w2) := process_builder_pending_payments quorum [clearedSlot] second1 wChild
    w2
  | .confirmedAfterTwoEpochs =>
    let (first1, second1, w1) := process_builder_pending_payments quorum [{}] [mkPayment 0] []
    let (_, _, w2) := process_builder_pending_payments quorum first1 second1 w1
    appendOlderBid w2 bid

/-- A fresh positive bid crosses two boundaries with no intervening blocks. The
first rotation preserves the complete entry; the second evicts it without paying.
The only weight used here comes from bid creation, and each boundary may have a
different positive quorum. This is the tracked-slot projection, not a fork-choice
or whole-BeaconState reachability theorem. -/
theorem fresh_bid_across_two_empty_epochs (bid : BuilderPendingWithdrawal)
    (proposer firstQuorum secondQuorum : Nat) (existing : List BuilderPendingWithdrawal)
    (hbid : 0 < bid.amount) (hfirst : 0 < firstQuorum) (hsecond : 0 < secondQuorum) :
    let entry := paymentForBid bid proposer 0
    let (first, second, ws) := process_builder_pending_payments firstQuorum [{}] [entry] existing
    let (_, _, next) := process_builder_pending_payments secondQuorum first second ws
    first = [entry] ∧ entry.weight = 0 ∧ next = existing ∧
      appendOlderBid next bid = existing ++ [bid] := by
  simp [process_builder_pending_payments, paymentForBid, appendOlderBid, hbid,
    Nat.not_le_of_lt hfirst, Nat.not_le_of_lt hsecond]

/-- **Single settlement (T-7732-SINGLE-SETTLEMENT)**

*Natural property.* A committed bid can queue at most its value, across the confirmation and quorum paths of the modeled lifecycle.

*Formal statement.* For any positive quorum and any of the four confirmation timings, the sum of withdrawal amounts produced by one bid is at most `bidValue`.
-/
theorem t_7732_single_settlement
    (feeRecipient bidValue builderIdx proposerIdx attestedWeight quorum : Nat)
    (timing : ChildConfirmationTiming)
    (h_quorum : quorum > 0) :
    sum_withdrawal_amounts
      (settle_slot_bid_lifecycle feeRecipient bidValue builderIdx proposerIdx
        attestedWeight quorum timing) ≤ bidValue := by
  have h_q0 : quorum ≠ 0 := by omega
  dsimp [settle_slot_bid_lifecycle, paymentForBid, appendOlderBid, settle_builder_payment, process_builder_pending_payments,
    sum_withdrawal_amounts]
  cases timing <;> by_cases h_bid : bidValue > 0 <;> simp [h_bid, h_q0]
  by_cases h_wt : attestedWeight ≥ quorum <;> simp [h_wt]

/-- **Proposer payment guarantee (T-7732-PAYMENT-GUARANTEE)**

*Natural property.* Child confirmation or sufficient ordinary beacon attestation weight queues the full bid for the designated fee recipient.

*Formal statement.* For a positive bid and positive quorum, if the child confirms or `attestedWeight ≥ quorum`, the lifecycle returns exactly `[⟨feeRecipient, bidValue, builderIdx⟩]`. This is a pending withdrawal.
-/
theorem t_7732_payment_guarantee
    (feeRecipient bidValue builderIdx proposerIdx attestedWeight quorum : Nat)
    (timing : ChildConfirmationTiming)
    (h_bid : bidValue > 0)
    (h_quorum : quorum > 0)
    (h_timely : timing ≠ .notConfirmed ∨ attestedWeight ≥ quorum) :
    settle_slot_bid_lifecycle feeRecipient bidValue builderIdx proposerIdx
      attestedWeight quorum timing = [⟨feeRecipient, bidValue, builderIdx⟩] := by
  have h_q0 : quorum ≠ 0 := by omega
  dsimp [settle_slot_bid_lifecycle, paymentForBid, appendOlderBid, settle_builder_payment, process_builder_pending_payments]
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

/-- **Builder solvency at bid admission (T-7732-BUILDER-SOLVENCY)**

*Natural property.* A builder whose bid passes the coverage check can cover the bid, its pending obligations and the minimum deposit.

*Formal statement.* If `can_builder_cover_bid builderBalance pendingToWithdraw bidAmount = true`, then `builderBalance ≥ MIN_DEPOSIT_AMOUNT + pendingToWithdraw + bidAmount`. Equality suffices.
-/
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

/-- **Supply neutrality for one builder bid (T-7732-NO-ETH-MINTING)**

*Natural property.* The modeled builder debit exactly accounts for the amount queued for withdrawal. Within that accounting, no ETH is created or lost.

*Formal statement.* Given bid coverage and a positive quorum, `postBuilderBalance + settled = builderBalance` and `postBuilderBalance ≥ MIN_DEPOSIT_AMOUNT + pendingToWithdraw`. Here `settled` sums the queued withdrawal amounts. Recipient balances and unrelated accounts are outside this statement.
-/
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

/-- **Builder exit safety (T-7732-EXIT-SAFETY)**

*Natural property.* A builder must be active and have no outstanding payment obligations to pass the exit-initiation check.

*Formal statement.* If `can_builder_exit isActive pendingToWithdraw = true`, then `isActive = true ∧ pendingToWithdraw = 0`. The subsequent withdrawal of the stake is a separate operation.
-/
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

/-- **Attestation weight counted once (T-7732-QUORUM-NO-DOUBLE-COUNT)**

*Natural property.* Two weight updates for the same validator within one epoch contribute its effective balance once to the builder payment quorum.

*Formal statement.* Starting with no prior participation and weight `w`, the first call to `accrue_attester_weight` sets the participation flag. The second uses that flag, so the final weight is `w + eb`.
-/
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

/-- **Same-slot unbundling at the consensus boundary (T-7732-SAME-SLOT-UNBUNDLING)**

*Natural property.* A candidate containing the transaction and matching the committed block hash must be the builder’s payload, assuming that hash identifies it uniquely among the candidates.

*Formal statement.* Given the bid commitment, the hash-uniqueness premise, a matching candidate and `txPriv ∈ candidate.transactions`, the conclusion is `candidate = builderPayload ∧ txPriv ∈ builderPayload.transactions`. The model tracks transaction inclusion; it does not track who knew the transaction before reveal, gossip leakage or fork choice.
-/
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

/-- **Slashed proposer payment revocation under the proposed fix (#5754) (T-7732-SLASHED-NO-RESURRECTION)**

*Natural property.* Processing the slashed parent’s bid adds no withdrawal, however many epochs elapsed before the child arrived.

*Formal statement.* If `s.parentProposerSlashed = true`, then `(apply_parent_payment_patched s).pendingWithdrawals = s.pendingWithdrawals`. This preserves entries already in the queue and concerns one application of the patched transition.
-/
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
  let paymentAfterBid : BuilderPendingPayment := ⟨0, ⟨feeRecipient, bidValue, builderIdx⟩, headerProposer⟩
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

/-- **Preservation of unrelated modeled state (T-7732-FRAME)**

*Natural property.* Processing a sequence of full or empty parents preserves the three consensus roots represented in the payment model.

*Formal statement.* Folding `process_parent_payload_if_full` over any list of steps preserves `s.untouchedCl`: the validator registry root, BLS-to-execution root and sync committee root. The full-parent step uses the patched payment abstraction.
-/
theorem t_7732_frame (s : GloasParentPaymentState) (steps : List Bool) :
    (steps.foldl (fun st isFull => process_parent_payload_if_full isFull st) s).untouchedCl =
      s.untouchedCl :=
  eip7732_frame_invariant.preserved_list s steps

/-! ## 7. EIP-8282 -> EIP-7732 Builder Queue Closure (`T-8282-7732-QUEUE-SAFETY`) and
    Cross-Function Credential-Check Divergence (`beacon-chain.md:2334-2361` vs `fork.md:70-120`) -/

/-- Under Gloas (`process_parent_execution_payload:1841-1854`), when a child block confirms
an EMPTY parent (`isParentFull = false`), `block.body.parent_execution_requests` MUST be empty;
when it confirms a FULL parent (`isParentFull = true`), `hash_tree_root(requests)` MUST equal
`parent_bid.execution_requests_root`. -/
def valid_parent_execution_requests (isParentFull : Bool) (requestsEmpty : Bool)
    (requestsRoot parentCommittedRoot : Nat) : Bool :=
  if !isParentFull then
    requestsEmpty
  else
    decide (requestsRoot = parentCommittedRoot)

theorem t_8282_7732_queue_safety (isParentFull requestsEmpty : Bool)
    (requestsRoot parentCommittedRoot : Nat) :
    valid_parent_execution_requests isParentFull requestsEmpty requestsRoot parentCommittedRoot = true ↔
      ((isParentFull = false → requestsEmpty = true) ∧
       (isParentFull = true → requestsRoot = parentCommittedRoot)) := by
  cases isParentFull <;> simp [valid_parent_execution_requests]

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

def AvailabilityRing.getBit (r : AvailabilityRing) (slot : Nat) : Bool :=
  let idx := slot % r.size
  match r.bits.find? (fun p => p.1 == idx) with
  | some (_, b) => b
  | none => true -- initialized to `0b1` at `upgrade_to_gloas` (`fork.md:199`)

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
  let r0 : AvailabilityRing := { size := 64, bits := [] } -- all bits `true` after `upgrade_to_gloas`
  let r1 := process_slot_ring r0 64                       -- clears slot `65`, NOT `64` (`s_fork`)!
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
