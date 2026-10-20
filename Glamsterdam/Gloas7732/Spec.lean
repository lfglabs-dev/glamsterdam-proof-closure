/-
  Glamsterdam.Gloas7732.Spec: Formal Verification of EIP-7732 (ePBS Consensus Specs)
  and EIP-8282 -> EIP-7732 Builder Queue Closure.
  Pinned against `ethereum/consensus-specs` @ `aa16bb4c156184e9548a997d53efaf2a228a6304`
  (`v1.7.0-beta.4`, `specs/gloas/beacon-chain.md` & `specs/gloas/fork.md`).
  Note: `fork-choice.md` and P2P gossip remain strictly out of scope.
-/
import Glamsterdam.Common.MetaSpec

namespace Glamsterdam.Gloas7732.Spec

open Glamsterdam.Common.MetaSpec

def MIN_DEPOSIT_AMOUNT : Nat := 1000000000
def FAR_FUTURE_EPOCH : Nat := 18446744073709551615

structure BuilderPendingWithdrawal where
  feeRecipient : Nat
  amount : Nat
  builderIndex : Nat
  deriving Repr, DecidableEq, BEq

structure BuilderPendingPayment where
  weight : Nat := 0
  withdrawal : BuilderPendingWithdrawal := ⟨0, 0, 0⟩
  deriving Repr, DecidableEq, BEq

structure Builder where
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

/-! ### 1. `F-7732-SLASHED-PAYMENT-RESURRECTION` & `T-7732-SLASHED-NO-RESURRECTION` -/

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

/-! ### 2. Builder Solvency (`T-7732-BUILDER-SOLVENCY`) & Exit Safety (`T-7732-EXIT-SAFETY`) -/

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

def can_builder_exit (isActive : Bool) (pendingToWithdraw : Nat) : Bool :=
  isActive && decide (pendingToWithdraw = 0)

/-- T-7732-EXIT-SAFETY: `process_builder_exit_request` only initiates a builder exit when
    `pendingToWithdraw = 0`, preventing an exiting builder from defaulting on pending bids. -/
theorem t_7732_exit_safety (isActive : Bool) (pendingToWithdraw : Nat)
    (h : can_builder_exit isActive pendingToWithdraw = true) :
    isActive = true ∧ pendingToWithdraw = 0 := by
  simpa [can_builder_exit] using h

/-! ### 3. Quorum Anti-Double-Counting (`T-7732-QUORUM-NO-DOUBLE-COUNT`) -/

def accrue_attester_weight (alreadyParticipated : Bool) (currentWeight effectiveBalance : Nat) :
    Bool × Nat :=
  if alreadyParticipated then
    (true, currentWeight)
  else
    (true, currentWeight + effectiveBalance)

/-- T-7732-QUORUM-NO-DOUBLE-COUNT: Even if an attester equivocates on target roots within
    the same block (PR #5172), `will_participate` gates weight accrual so two attestations
    from the same validator add `effectiveBalance` at most once. -/
theorem t_7732_quorum_no_double_count (w eb : Nat) :
    let (flag1, w1) := accrue_attester_weight false w eb
    let (_, w2) := accrue_attester_weight flag1 w1 eb
    w2 = w + eb := rfl

/-! ### 4. Deferred Execution Equivalence (`T-7732-DEFERRED-EXEC-EQUIV`) & Frame Theorem (`T-7732-FRAME`) -/

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

/-! ### 5. EIP-8282 -> EIP-7732 Builder Queue Closure (`T-8282-7732-QUEUE-SAFETY`) -/

/-- Under Gloas (`process_parent_execution_payload:1857-1865`), when a child block confirms
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

/-! ### 6. `F-7732-FORK-SLOT-AVAILABILITY-BIT-HIGH` & `F-7732-AVAILABILITY-RING-BUFFER-CLOBBER` -/

/-- Unpatched `upgrade_to_gloas` (`specs/gloas/fork.md:198-200`): initializes all bits of
    `execution_payload_availability` to `true` (`0b1`), including `s_fork % SLOTS_PER_HISTORICAL_ROOT`.
    When `block_0` at `s_fork` has an EMPTY payload (`isForkBlockFull = false`), its availability
    bit remains `true` instead of `false`! -/
def fork_slot_availability_v170_beta4_buggy (isForkBlockFull : Bool) : Bool :=
  if isForkBlockFull then true else true

/-- Patched `upgrade_to_gloas`: clears `s_fork % SLOTS_PER_HISTORICAL_ROOT` to `false` at fork
    initialization so it only becomes `true` if `block_0`'s payload is confirmed. -/
def fork_slot_availability_patched (isForkBlockFull : Bool) : Bool :=
  isForkBlockFull

def f_7732_fork_slot_availability_refuter :
    WitnessRefuter Bool Bool (fun isFull bit => bit = isFull) where
  reference := fork_slot_availability_patched
  mutant := fork_slot_availability_v170_beta4_buggy
  ref_sound := fun _ => rfl
  killWitness := false
  mutant_refuted := by decide

@[inline, export glamsterdam_eip7732_can_cover_bid_cabi]
def eip7732_can_cover_bid_cabi (builderBalance pendingToWithdraw bidAmount : UInt64) : Bool :=
  can_builder_cover_bid builderBalance.toNat pendingToWithdraw.toNat bidAmount.toNat

end Glamsterdam.Gloas7732.Spec
