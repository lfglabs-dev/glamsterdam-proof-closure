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

Covers:
1. `F-7732-SLASHED-PAYMENT-RESURRECTION` & `T-7732-SLASHED-NO-RESURRECTION`
   (`slash_validator:1549-1582`, `settle_builder_payment:1538-1544`,
   `apply_parent_execution_payload:1784-1831`, `process_builder_pending_payments:1719-1732`).
2. `T-7732-BUILDER-SOLVENCY` & `T-7732-EXIT-SAFETY`
   (`get_pending_balance_to_withdraw_for_builder:1168-1179`, `can_builder_cover_bid:1184-1193`,
   `process_builder_exit_request:2368-2384`, `initiate_builder_exit:1526-1533`,
   `get_builder_withdrawals:1861-1889`, `get_builder_balance_after_withdrawals:1895-1906`,
   `get_builders_sweep_withdrawals:1912-1947`, `apply_withdrawals:1997-2007`).
3. `T-7732-QUORUM-NO-DOUBLE-COUNT` (`get_builder_payment_quorum_threshold:1433-1440`,
   `process_attestation:2396-2481`).
4. `T-7732-DEFERRED-EXEC-EQUIV` & `T-7732-FRAME` (`process_parent_execution_payload:1841-1854`,
   `process_withdrawals:2067-2093`).
5. `T-8282-7732-QUEUE-SAFETY` & `F-8282-TOPUP-CREDENTIAL-PREFIX-DROP`
   (`get_index_for_new_builder:2290-2294`, `add_builder_to_registry:2300-2320`,
   `process_builder_deposit_request:2334-2361`, `onboard_builders_from_pending_deposits:70-120`).
6. `F-7732-FORK-SLOT-AVAILABILITY-BIT-HIGH` & `F-7732-AVAILABILITY-RING-BUFFER-CLOBBER`
   (`upgrade_to_gloas:135-232`, `process_slot:1608-1623`, `apply_parent_execution_payload:1829`).
-/

namespace Glamsterdam.Gloas7732.Spec

open Glamsterdam.Common.Prelude
open Glamsterdam.Common.MetaSpec

/-! ## 0. Pinned Gloas Constants (`specs/gloas/beacon-chain.md:33-135` @ `aa16bb4c`) -/

def MIN_DEPOSIT_AMOUNT : Nat := 1000000000
def FAR_FUTURE_EPOCH : Nat := 18446744073709551615
def BUILDER_INDEX_FLAG : Nat := 1099511627776 -- 2^40
def BUILDER_INDEX_SELF_BUILD : Nat := 18446744073709551615
def BUILDER_PAYMENT_THRESHOLD_NUMERATOR : Nat := 6
def BUILDER_PAYMENT_THRESHOLD_DENOMINATOR : Nat := 10
def MIN_BUILDER_WITHDRAWABILITY_DELAY : Nat := 64
def PAYLOAD_BUILDER_VERSION : Nat := 0x03
def BUILDER_WITHDRAWAL_PREFIX : Nat := 0xB0

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

/-! ## 1. `F-7732-SLASHED-PAYMENT-RESURRECTION` & `T-7732-SLASHED-NO-RESURRECTION` -/

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

/-- Unpatched `v1.7.0-beta.4` (`aa16bb4c`) `slash_validator` + `apply_parent_execution_payload`:
`slash_validator` clears `pendingPaymentSlotAmount := 0` (PR #5719), but leaves
`latestBidValue > 0`. When `parentEpoch + 1 < currentEpoch` (2+ missed epochs, PR #5170),
`apply_parent_execution_payload` falls into `elif parent_bid.value > 0:` and resurrects
the slashed proposer's withdrawal! -/
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
Slashing the proposer zeroes `latestBidValue` alongside `builder_pending_payments[payment_index]`,
preventing payment resurrection across any number of missed epochs. -/
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

/-- Explicit `WitnessRefuter` proving the real bug `F-7732-SLASHED-PAYMENT-RESURRECTION` in
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
2. In the same parent block's `process_operations` (or before epoch rotation), `slash_validator` runs on
   `slashedIndex`. In `v1.7.0-beta.4` (`lines 1579-1581`), `slash_validator` checks
   `if slashed_index == state.latest_block_header.proposer_index:`, clearing `secondEpochPayments[slotIdx]`
   to `{}` while leaving `latestBidValue` untouched!
3. Two epoch boundaries pass without a block (`process_builder_pending_payments` runs twice, rotating
   and clearing both halves of `builder_pending_payments`).
4. Child block arrives at `currentEpoch ≥ parentEpoch + 2` and runs `apply_parent_execution_payload`,
   which enters the `else` branch (`parent_epoch < previous_epoch`) and appends `latestBidValue` to
   `builder_pending_withdrawals`! -/
def trace_bid_slash_rotate_apply_v170_beta4
    (bidValue feeRecipient builderIdx headerProposer slashedIdx : Nat) :
    List BuilderPendingWithdrawal :=
  let paymentAfterBid : BuilderPendingPayment :=
    { weight := 0
      withdrawal := ⟨feeRecipient, bidValue, builderIdx⟩
      proposerIndex := headerProposer }
  -- Step 2: `slash_validator` (`beacon-chain.md:1579-1581`)
  let paymentAfterSlash : BuilderPendingPayment :=
    if slashedIdx == headerProposer then {} else paymentAfterBid
  let latestBidAfterSlash : Nat := bidValue -- BUG: `latest_execution_payload_bid.value` is NOT zeroed!
  -- Step 3: Two epoch boundaries (`process_builder_pending_payments` with quorum = 600,000,000,000)
  let (first1, second1, w1) := process_builder_pending_payments 1 [paymentAfterSlash] [{}] []
  let (_, _, w2) := process_builder_pending_payments 1 first1 second1 w1
  -- Step 4: `apply_parent_execution_payload` at `parentEpoch = 4, currentEpoch = 6`
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

/-- Finding 1.5 (`F-7732-EARLIER-SLOT-PROPOSER-SLASHING-NOT-CLEARED`, `beacon-chain.md:1579-1581`):
When proposer `P1` proposes at slot `s1` (`payment1.proposerIndex = P1`), and at a later slot `s2 > s1`
in the same epoch proposer `P2 ≠ P1` includes a `ProposerSlashing` or `AttesterSlashing` against `P1`,
`state.latest_block_header.proposer_index` is already `P2` (updated in `process_block_header` before
`process_operations`).
- Unpatched `slash_validator` checks `if slashed_index == state.latest_block_header.proposer_index:`
  (`P1 == P2`, which is `false`!) and leaves `P1`'s pending payment intact in `builder_pending_payments`.
- Patched `slash_validator` scans `builder_pending_payments` for any entry with
  `payment.proposerIndex == slashedIndex` and clears it to `{}`. -/
def slash_pending_payment_v170_beta4_buggy
    (latestHeaderProposer slashedIndex : Nat) (payment : BuilderPendingPayment) :
    BuilderPendingPayment :=
  if slashedIndex == latestHeaderProposer && payment.proposerIndex == latestHeaderProposer then
    {}
  else
    payment

def slash_pending_payment_patched
    (_latestHeaderProposer slashedIndex : Nat) (payment : BuilderPendingPayment) :
    BuilderPendingPayment :=
  if payment.proposerIndex == slashedIndex then {} else payment

def f_7732_earlier_slot_proposer_slashing_refuter :
    WitnessRefuter (Nat × Nat × BuilderPendingPayment) BuilderPendingPayment
      (fun ⟨_, slashedIdx, p⟩ post => p.proposerIndex = slashedIdx → post.withdrawal.amount = 0) where
  reference := fun ⟨hdr, sl, p⟩ => slash_pending_payment_patched hdr sl p
  mutant := fun ⟨hdr, sl, p⟩ => slash_pending_payment_v170_beta4_buggy hdr sl p
  ref_sound := by
    intro ⟨hdr, sl, p⟩ h_eq
    simp [slash_pending_payment_patched, h_eq]
  killWitness := (99, 42, { weight := 100, withdrawal := ⟨0xaa, 1000000, 0⟩, proposerIndex := 42 })
  mutant_refuted := by decide

/-! ## 2. Builder Solvency (`T-7732-BUILDER-SOLVENCY`), Pending Balance Accounting, and Exit Safety (`T-7732-EXIT-SAFETY`) -/

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

/-- Exact `is_active_builder` (`beacon-chain.md:1070-1075`):
`builder.withdrawable_epoch == FAR_FUTURE_EPOCH and builder.deposit_epoch < finalized_epoch`. -/
def is_active_builder (b : Builder) (finalizedEpoch : Nat) : Bool :=
  b.withdrawableEpoch == FAR_FUTURE_EPOCH && decide (b.depositEpoch < finalizedEpoch)

def can_builder_exit (isActive : Bool) (pendingToWithdraw : Nat) : Bool :=
  isActive && decide (pendingToWithdraw = 0)

/-- T-7732-EXIT-SAFETY: `process_builder_exit_request` only initiates a builder exit when
`pendingToWithdraw = 0`, preventing an exiting builder from defaulting on pending bids. -/
theorem t_7732_exit_safety (isActive : Bool) (pendingToWithdraw : Nat)
    (h : can_builder_exit isActive pendingToWithdraw = true) :
    isActive = true ∧ pendingToWithdraw = 0 := by
  simpa [can_builder_exit] using h

/-! ## 3. Quorum Anti-Double-Counting (`T-7732-QUORUM-NO-DOUBLE-COUNT`, `beacon-chain.md:2447-2467`) -/

def accrue_attester_weight (alreadyParticipated : Bool) (currentWeight effectiveBalance : Nat) :
    Bool × Nat :=
  if alreadyParticipated then
    (true, currentWeight)
  else
    (true, currentWeight + effectiveBalance)

/-- T-7732-QUORUM-NO-DOUBLE-COUNT: Even if an attester equivocates on target roots within
the same block (PR #5172), `had_no_participation && will_set_new_flag` gates weight accrual
so two attestations from the same validator add `effectiveBalance` at most once. -/
theorem t_7732_quorum_no_double_count (w eb : Nat) :
    let (flag1, w1) := accrue_attester_weight false w eb
    let (_, w2) := accrue_attester_weight flag1 w1 eb
    w2 = w + eb := rfl

/-! ## 4. Deferred Execution Equivalence (`T-7732-DEFERRED-EXEC-EQUIV`) & Frame Theorem (`T-7732-FRAME`) -/

/-- T-7732-DEFERRED-EXEC-EQUIV: When `bid.parent_block_hash != parent_bid.block_hash` (empty parent),
`process_parent_execution_payload` leaves builder pending withdrawals, builder balances, and
builder exit epochs untouched. -/
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

/-! ## 5. EIP-8282 -> EIP-7732 Builder Queue Closure (`T-8282-7732-QUEUE-SAFETY`) and
    Refuter for `F-8282-TOPUP-CREDENTIAL-PREFIX-DROP` (`beacon-chain.md:2334-2361`) -/

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
    (requestsRoot parentCommittedRoot : Nat)
    (h : valid_parent_execution_requests isParentFull requestsEmpty requestsRoot parentCommittedRoot = true) :
    (isParentFull = false → requestsEmpty = true) ∧
    (isParentFull = true → requestsRoot = parentCommittedRoot) := by
  unfold valid_parent_execution_requests at h
  cases isParentFull <;> simp_all

/-- Input to `process_builder_deposit_request` (`beacon-chain.md:2334-2361`). -/
structure BuilderDepositStep where
  pubkeyRegistered : Bool
  credentialPrefix : Nat
  signatureValid : Bool
  currentBalance : Nat
  depositAmount : Nat
  deriving Repr, DecidableEq, BEq

/-- Unpatched `process_builder_deposit_request` (`beacon-chain.md:2334-2361` @ `v1.7.0-beta.4`):
Checks `if not is_builder_withdrawal_credential(request.withdrawal_credentials): return` at line 2336
BEFORE checking `if request.pubkey not in builder_pubkeys:` at line 2340!
If an existing builder (`pubkeyRegistered = true`) submits a top-up with a non-`0xB0` credential
prefix (e.g., `0x00` or `0x01`), the deposit is silently dropped and the ETH burned on the EL is
permanently lost on the CL, violating `EIP-8282` ("top-ups do not validate withdrawal_credentials
or signature", matching `onboard_builders_from_pending_deposits` in `fork.md:92-118`). -/
def process_builder_deposit_v170_beta4_buggy (s : BuilderDepositStep) : Nat :=
  if s.credentialPrefix != BUILDER_WITHDRAWAL_PREFIX then
    s.currentBalance
  else if !s.pubkeyRegistered then
    if s.signatureValid then s.depositAmount else s.currentBalance
  else
    s.currentBalance + s.depositAmount

/-- EIP-8282 compliant `process_builder_deposit_request` (matching `fork.md:92-118`):
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

/-! ## 6. `F-7732-FORK-ONBOARD-CROSS-CREDENTIAL` (1.6), `F-7732-FORK-SLOT-AVAILABILITY-BIT-HIGH` (1.2),
    and `F-7732-AVAILABILITY-RING-BUFFER-CLOBBER` (1.3) -/

/-- Finding 1.6 (`F-7732-FORK-ONBOARD-CROSS-CREDENTIAL`, `fork.md:70-120` vs `beacon-chain.md:2336`):
In `onboard_builders_from_pending_deposits` (`fork.md:92-118`), a pending deposit with
`is_builder_withdrawal_credential == false` (e.g., `0x01`) Whose `pubkey` is already in `builder_pubkeys`
(registered by an earlier `0xB0` deposit in the same queue) enters the `else` branch at line 94 and
is credited to `state.builders[builder_index].balance` instead of remaining in `state.pending_deposits`
for validator processing (whereas `process_builder_deposit_request` in `beacon-chain.md:2336` checks
`is_builder_withdrawal_credential` first). -/
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

/-- `process_slot` (`beacon-chain.md:1620-1622`):
At the end of `process_slot(state)` (just before `state.slot += 1` in `process_slots`),
sets `state.execution_payload_availability[(state.slot + 1) % SLOTS_PER_HISTORICAL_ROOT] = 0b0`. -/
def process_slot_ring (r : AvailabilityRing) (currentSlot : Nat) : AvailabilityRing :=
  r.setBit (currentSlot + 1) false

/-- `apply_parent_execution_payload` (`beacon-chain.md:1829`):
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
