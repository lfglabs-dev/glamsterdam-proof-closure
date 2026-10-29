/-
Copyright (c) 2026 Verity Labs / LFG Labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Marchand, Verity Audit Team
-/
import Glamsterdam.Common.ElCore
import Glamsterdam.Gas.Spec
import Glamsterdam.Gas.CallTree
import Glamsterdam.Gas.Eip12582

/-!
# Decision Tree & Mitigation Matrix (`ethereum/8037-findings#307` vs `ethereum/EIPs#12581`)

This module formalizes:
1. **Decision tree** (`DECISION_MATRIX.md`, `INV-1..INV-5` in `ethereum/8037-findings#307`):
   `InvariantClass`, `DecisionInputs`, `ForkDecision`, `decide_fork_response`, and
   `t_decision_tree_partition_and_withdrawal_gate`.
2. **Parametric mitigation matrix** (`INV-1`, `INV-2`, `INV-3`, `INV-5` in
   `DECISION_MATRIX.md`):
   `MitigationConfig`, `DecisionMeter`, `charge_state_dm`, `refill_clear_dm`,
   `enter_call_with_new_account_dm`, `exit_child_dm`, `settle_pre_exec_oog_dm`, and `settle_tx_dm`.
3. **Comparison with `ethereum/EIPs#12581` (`2ba9176f`)**:
   `t_dm_pr12581_eight_normative_vectors_and_call_ordering` machine-checks the 8 normative test
   cases (`EIPS/eip-8037.md`, PR #12581 @ `2ba9176f`), the value-`CALL` 63/64 table, and the
   pre-execution OOG settlement `min(txGas, TX_MAX_GAS_LIMIT)` paid and `stateGasReservoir` returned.
-/

namespace Glamsterdam.Gas.DecisionMatrix

open Glamsterdam.Common.Prelude
open Glamsterdam.Common.MetaSpec
open Glamsterdam.Common.ElCore
open Glamsterdam.Gas.Spec
open Glamsterdam.Gas.CallTree
open Glamsterdam.Gas.Eip12582

/-! ## 1. Decision Tree (`DECISION_MATRIX.md`, `ethereum/8037-findings#307`) -/

/-- Invariant class (`DECISION_MATRIX.md` in `ethereum/8037-findings#307`):
- `inherent`: the break follows from changing gas costs (`INV-4`, `INV-6`, `INV-7`).
- `eipSpecific`: the break follows from the new gas accounting (`INV-1`, `INV-2`, `INV-3`, `INV-5`). -/
inductive InvariantClass where
  | inherent
  | eipSpecific
  deriving Repr, DecidableEq, BEq

/-- Inputs to the fork-response decision tree (`DECISION_MATRIX.md` in `ethereum/8037-findings#307`). -/
structure DecisionInputs where
  findingConfirmed : Bool
  teamCanFix : Bool
  waitingJustified : Bool
  invariantClass : InvariantClass
  candidateSpecFixExists : Bool
  specFixWorksWithoutNewBreaks : Bool
  narrowerRepricingResolves : Bool
  breakAcceptable : Bool
  deriving Repr, DecidableEq, BEq

/-- Fork-response outcomes (`DECISION_MATRIX.md` in `ethereum/8037-findings#307`). -/
inductive ForkDecision where
  | noAction
  | delayForkForTeamFix
  | acceptBreakOrChangeFork
  | adoptRevisedSpec
  | acceptBreak
  | withdrawEip
  deriving Repr, DecidableEq, BEq

/-- Validated projection of the decision-tree flowchart (`DECISION_MATRIX.md` in
`ethereum/8037-findings#307`):
- Confirmed finding with a team fix and justified wait -> `delayForkForTeamFix`.
- Confirmed finding with a team fix but unjustified wait -> `acceptBreakOrChangeFork`.
- No team fix + EIP-specific invariant with working spec fix -> `adoptRevisedSpec`.
- No team fix + inherent invariant resolved by narrower repricing + working spec fix -> `adoptRevisedSpec`.
- Otherwise, gates on `d.breakAcceptable` (`acceptBreak` vs `withdrawEip`). -/
def decide_fork_response (d : DecisionInputs) : ForkDecision :=
  if !d.findingConfirmed then
    .noAction
  else if d.teamCanFix then
    if d.waitingJustified then .delayForkForTeamFix else .acceptBreakOrChangeFork
  else
    let specFixApplicable :=
      match d.invariantClass with
      | .eipSpecific => d.candidateSpecFixExists
      | .inherent => d.narrowerRepricingResolves
    if specFixApplicable && d.specFixWorksWithoutNewBreaks then
      .adoptRevisedSpec
    else if d.breakAcceptable then
      .acceptBreak
    else
      .withdrawEip

/-- **Theorem (`t_decision_tree_partition_and_withdrawal_gate`)**:
`decide_fork_response` covers every branch of the `DECISION_MATRIX.md` flowchart, proving exact
necessary and sufficient conditions for `adoptRevisedSpec`, `acceptBreak`, and `withdrawEip`
(in particular, inherent `INV-4/6/7` findings with `narrowerRepricingResolves = false` cannot reach
`adoptRevisedSpec`). -/
theorem t_decision_tree_partition_and_withdrawal_gate (d : DecisionInputs) :
    (!d.findingConfirmed = true → decide_fork_response d = .noAction) ∧
    (d.findingConfirmed = true ∧ d.teamCanFix = true ∧ d.waitingJustified = true →
      decide_fork_response d = .delayForkForTeamFix) ∧
    (d.findingConfirmed = true ∧ d.teamCanFix = true ∧ d.waitingJustified = false →
      decide_fork_response d = .acceptBreakOrChangeFork) ∧
    (d.findingConfirmed = true ∧ d.teamCanFix = false ∧
      ((d.invariantClass = .eipSpecific ∧ d.candidateSpecFixExists = true) ∨
        (d.invariantClass = .inherent ∧ d.narrowerRepricingResolves = true)) ∧
      d.specFixWorksWithoutNewBreaks = true →
      decide_fork_response d = .adoptRevisedSpec) ∧
    (decide_fork_response d = .withdrawEip ↔
      (d.findingConfirmed = true ∧ d.teamCanFix = false ∧ d.breakAcceptable = false ∧
        ¬(((d.invariantClass = .eipSpecific ∧ d.candidateSpecFixExists = true) ∨
            (d.invariantClass = .inherent ∧ d.narrowerRepricingResolves = true)) ∧
          d.specFixWorksWithoutNewBreaks = true))) ∧
    (decide_fork_response d = .acceptBreak ↔
      (d.findingConfirmed = true ∧ d.teamCanFix = false ∧ d.breakAcceptable = true ∧
        ¬(((d.invariantClass = .eipSpecific ∧ d.candidateSpecFixExists = true) ∨
            (d.invariantClass = .inherent ∧ d.narrowerRepricingResolves = true)) ∧
          d.specFixWorksWithoutNewBreaks = true))) := by
  unfold decide_fork_response
  cases d with
  | mk findingConfirmed teamCanFix waitingJustified invariantClass candidateSpecFixExists
      specFixWorksWithoutNewBreaks narrowerRepricingResolves breakAcceptable =>
    cases findingConfirmed <;> cases teamCanFix
    all_goals cases waitingJustified <;> cases invariantClass
    all_goals cases candidateSpecFixExists <;> cases specFixWorksWithoutNewBreaks
    all_goals cases narrowerRepricingResolves <;> cases breakAcceptable
    all_goals decide

/-! ## 2. Parametric Mitigation Matrix (`INV-1`, `INV-2`, `INV-3`, `INV-5` in
    `DECISION_MATRIX.md`, `ethereum/8037-findings#307`) -/

/-- `INV-1` charge mode (`DECISION_MATRIX.md` in `ethereum/8037-findings#307`):
- `reservoirFirst`: EIP-8037 (`16898000`), reservoir first with no minimum execution payment.
- `legacyShareExecFirst`: minimum execution payment (legacy share) charged from `gasLeft` first,
  as in `ethereum/EIPs#12581` (`2ba9176f`).
- `codeDepositOnlyReservoir`: all state creation except code deposit charged to `gasLeft` first. -/
inductive Inv1ChargeMode where
  | reservoirFirst
  | legacyShareExecFirst
  | codeDepositOnlyReservoir
  deriving Repr, DecidableEq, BEq

/-- `INV-2` slot-clear refill mode (`DECISION_MATRIX.md` in `ethereum/8037-findings#307`):
- `lifoToGasLeft`: LIFO refill to `gasLeft` up to `stateGasSpilled` (`16898000`).
- `reservoirOnly`: refill only `stateGasReservoir`, never `gasLeft` (`ethereum/EIPs#12581`).
- `deferredUncappedCounter`: defer refills to settlement outside the ordinary refund cap.
- `cappedRefundCounter`: defer refills to settlement subject to the ordinary `1/5` refund cap. -/
inductive Inv2ClearMode where
  | lifoToGasLeft
  | reservoirOnly
  | deferredUncappedCounter
  | cappedRefundCounter
  deriving Repr, DecidableEq, BEq

/-- `INV-3` reverting-intermediary mode (`DECISION_MATRIX.md` in `ethereum/8037-findings#307`):
- `restoreSpillToGasLeft`: restore `stateGasSpilled` to `gasLeft` on revert (`16898000`).
- `restoreToReservoir`: restore net state gas to `stateGasReservoir`, never `gasLeft`
  (`ethereum/EIPs#12581`).
- `deferRevertToSettlement`: defer reverted state gas to end-of-transaction settlement.
- `consumeRevertStateGas`: consume all state gas charged by the failed call. -/
inductive Inv3RevertMode where
  | restoreSpillToGasLeft
  | restoreToReservoir
  | deferRevertToSettlement
  | consumeRevertStateGas
  deriving Repr, DecidableEq, BEq

/-- Full mitigation configuration for the decision matrix (`DECISION_MATRIX.md` in
`ethereum/8037-findings#307`). -/
structure MitigationConfig where
  inv1 : Inv1ChargeMode
  inv2 : Inv2ClearMode
  inv3 : Inv3RevertMode
  keepReservoirAcrossCalls : Bool := true
  deriving Repr, DecidableEq, BEq

/-- Gas meter for the decision matrix with deferred-refill and revert-deferral counters. -/
structure DecisionMeter where
  gasLeft : Nat
  stateGasReservoir : Nat
  stateGasSpilled : Nat
  evmStateGasUsed : Int
  reservoirSnapshot : Nat
  usedSnapshot : Int
  deferredRefill : Nat
  deferredRevert : Nat
  deriving Repr, DecidableEq, BEq

/-- Initialize a top-level `DecisionMeter` with the given execution grant and reservoir. -/
def init_decision_meter (gasLeft reservoir : Nat) : DecisionMeter :=
  { gasLeft := gasLeft
    stateGasReservoir := reservoir
    stateGasSpilled := 0
    evmStateGasUsed := 0
    reservoirSnapshot := reservoir
    usedSnapshot := 0
    deferredRefill := 0
    deferredRevert := 0 }

/-- Whether `amount` is a code-deposit state-gas charge (`legacyShare = 0` under all modes). -/
structure StateChargeParams where
  amount : Nat
  legacyShare : Nat
  isCodeDeposit : Bool
  deriving Repr, DecidableEq, BEq

/-- State-gas charge under `MitigationConfig` (`DECISION_MATRIX.md` `INV-1` and
`ethereum/EIPs#12581` `legacy_share` rule):
1. Compute the minimum execution payment `leg` according to `cfg.inv1`.
2. Draw the remainder from `stateGasReservoir` first, then spill to `gasLeft`.
3. Halt (`none`) if `gasLeft` cannot pay `leg + spill`. -/
def charge_state_dm (cfg : MitigationConfig) (m : DecisionMeter) (p : StateChargeParams) :
    Option DecisionMeter :=
  let leg :=
    match cfg.inv1 with
    | .reservoirFirst => 0
    | .legacyShareExecFirst => min p.amount p.legacyShare
    | .codeDepositOnlyReservoir => if p.isCodeDeposit then 0 else p.amount
  let rest := p.amount - leg
  let fromReservoir := min rest m.stateGasReservoir
  let spill := rest - fromReservoir
  let fromGasLeft := leg + spill
  if m.gasLeft < fromGasLeft then
    none
  else
    some { m with
      gasLeft := m.gasLeft - fromGasLeft
      stateGasReservoir := m.stateGasReservoir - fromReservoir
      stateGasSpilled := m.stateGasSpilled + fromGasLeft
      evmStateGasUsed := m.evmStateGasUsed + (p.amount : Int) }

/-- Slot-clear refill under `MitigationConfig` (`DECISION_MATRIX.md` `INV-2`):
- `lifoToGasLeft`: credits `gasLeft` up to `stateGasSpilled` first, then `stateGasReservoir`.
- `reservoirOnly`: credits `stateGasReservoir` only.
- `deferredUncappedCounter` / `cappedRefundCounter`: withhold the amount in `deferredRefill`
  until settlement. -/
def refill_clear_dm (cfg : MitigationConfig) (m : DecisionMeter) (amount : Nat) : DecisionMeter :=
  match cfg.inv2 with
  | .lifoToGasLeft =>
    let toGasLeft := min amount m.stateGasSpilled
    { m with
      gasLeft := m.gasLeft + toGasLeft
      stateGasSpilled := m.stateGasSpilled - toGasLeft
      stateGasReservoir := m.stateGasReservoir + (amount - toGasLeft)
      evmStateGasUsed := m.evmStateGasUsed - (amount : Int) }
  | .reservoirOnly =>
    { m with
      stateGasReservoir := m.stateGasReservoir + amount
      evmStateGasUsed := m.evmStateGasUsed - (amount : Int) }
  | .deferredUncappedCounter | .cappedRefundCounter =>
    { m with
      deferredRefill := m.deferredRefill + amount
      evmStateGasUsed := m.evmStateGasUsed - (amount : Int) }

/-- Charge execution gas only (`gasLeft`). -/
def charge_exec_dm (m : DecisionMeter) (amount : Nat) : Option DecisionMeter :=
  if m.gasLeft < amount then
    none
  else
    some { m with gasLeft := m.gasLeft - amount }

/-- Value-`CALL` to a cold non-existent account under `MitigationConfig`:
charges `GAS_COLD_ACCOUNT_ACCESS + GAS_CALL_VALUE` execution gas and then the new-account state
charge BEFORE computing `63/64` forwarding (`ethereum/EIPs#12581` ordering rule).
Returns `(forwardedGas, retainedGas, updatedParentMeter)`. -/
def enter_call_with_new_account_dm (cfg : MitigationConfig) (m : DecisionMeter) :
    Option (Nat × Nat × DecisionMeter) :=
  match charge_exec_dm m (GAS_COLD_ACCOUNT_ACCESS + GAS_CALL_VALUE) with
  | none => none
  | some m1 =>
    let p : StateChargeParams :=
      { amount := STATE_GAS_NEW_ACCOUNT
        legacyShare := LEGACY_SHARE_NEW_ACCOUNT
        isCodeDeposit := false }
    match charge_state_dm cfg m1 p with
    | none => none
    | some m2 =>
      let forwarded := max_message_call_gas m2.gasLeft
      let retained := m2.gasLeft - forwarded
      some (forwarded, retained, { m2 with gasLeft := retained })

/-- Child frame exit under `MitigationConfig` (`DECISION_MATRIX.md` `INV-3` and
`ethereum/EIPs#12581` rollback/child-return rules).
When `cfg.keepReservoirAcrossCalls = false` (`16898000` merge-refill behavior), a successful child
exit moves up to `min(child.stateGasReservoir, parentSpilledMerged)` back to `gasLeft`; when `true`
(`ethereum/EIPs#12581`), no gas moves from `stateGasReservoir` to `gasLeft` on return.
Under `.restoreToReservoir` (`ethereum/EIPs#12581`), `netUsed = child.evmStateGasUsed - child.usedSnapshot`
can be negative when a reverting child refilled more slots than it allocated; on reachable `#12581`
frames `child.stateGasReservoir + netUsed = child.reservoirSnapshot + nonHaltedChildSpill ≥ 0`
(proved in `t_dm_inv3_options_comparison`), so `Int.toNat` is exact and never clamps. -/
def exit_child_dm (cfg : MitigationConfig) (parentWithheld child : DecisionMeter)
    (status : ChildStatus) : DecisionMeter :=
  match status with
  | .success =>
    let mergedSpill := parentWithheld.stateGasSpilled + child.stateGasSpilled
    let d := if cfg.keepReservoirAcrossCalls then 0 else min child.stateGasReservoir mergedSpill
    { parentWithheld with
      gasLeft := parentWithheld.gasLeft + child.gasLeft + d
      stateGasReservoir := child.stateGasReservoir - d
      stateGasSpilled := mergedSpill - d
      evmStateGasUsed := child.evmStateGasUsed
      deferredRefill := child.deferredRefill
      deferredRevert := child.deferredRevert }
  | .revert =>
    match cfg.inv3 with
    | .restoreSpillToGasLeft =>
      { parentWithheld with
        gasLeft := parentWithheld.gasLeft + child.gasLeft + child.stateGasSpilled
        stateGasReservoir := child.reservoirSnapshot
        stateGasSpilled := parentWithheld.stateGasSpilled
        evmStateGasUsed := child.usedSnapshot
        deferredRefill := child.deferredRefill
        deferredRevert := child.deferredRevert }
    | .restoreToReservoir =>
      let netUsed := child.evmStateGasUsed - child.usedSnapshot
      let restoredReservoir := Int.toNat ((child.stateGasReservoir : Int) + netUsed)
      { parentWithheld with
        gasLeft := parentWithheld.gasLeft + child.gasLeft
        stateGasReservoir := restoredReservoir
        stateGasSpilled := parentWithheld.stateGasSpilled
        evmStateGasUsed := child.usedSnapshot
        deferredRefill := child.deferredRefill
        deferredRevert := child.deferredRevert }
    | .deferRevertToSettlement =>
      { parentWithheld with
        gasLeft := parentWithheld.gasLeft + child.gasLeft
        stateGasReservoir := child.reservoirSnapshot
        stateGasSpilled := parentWithheld.stateGasSpilled
        evmStateGasUsed := child.usedSnapshot
        deferredRefill := child.deferredRefill
        deferredRevert := child.deferredRevert + child.stateGasSpilled }
    | .consumeRevertStateGas =>
      { parentWithheld with
        gasLeft := parentWithheld.gasLeft + child.gasLeft
        stateGasReservoir := child.reservoirSnapshot
        stateGasSpilled := parentWithheld.stateGasSpilled
        evmStateGasUsed := child.usedSnapshot
        deferredRefill := child.deferredRefill
        deferredRevert := child.deferredRevert }
  | .halt =>
    { parentWithheld with
      gasLeft := parentWithheld.gasLeft
      stateGasReservoir := child.reservoirSnapshot
      stateGasSpilled := parentWithheld.stateGasSpilled
      evmStateGasUsed := child.usedSnapshot
      deferredRefill := child.deferredRefill
      deferredRevert := child.deferredRevert }

/-- Pre-execution OOG settlement (`ethereum/EIPs#12581` `EIPS/eip-2780.md` @ `2ba9176f`):
`gasLeft` is consumed and the state gas that came from `stateGasReservoir` returns to it, so the
sender pays `min(txGas, TX_MAX_GAS_LIMIT)` and `reservoirAtStart` returns to the sender. -/
def settle_pre_exec_oog_dm (txGas intrinsicExec reservoirAtStart : Nat) : Nat × Nat :=
  let initialGasLeft := min (TX_MAX_GAS_LIMIT - intrinsicExec) (txGas - intrinsicExec)
  let executionPaid := intrinsicExec + initialGasLeft
  (executionPaid, reservoirAtStart)

/-- End-of-transaction settlement under `MitigationConfig` (`DECISION_MATRIX.md` `INV-2`/`INV-3`
deferred-refill options and `ethereum/EIPs#12581` reservoir return):
- `deferredUncappedCounter`: `deferredRefill + deferredRevert` are repaid outside the ordinary cap.
- `cappedRefundCounter` (`INV-2` Option 3): slot-clear amounts (`deferredRefill`) are clamped to
  `min(gasUsedBeforeRefund / 5, deferredRefill)`, while `INV-3` Option 1 (`deferredRevert`) is repaid
  outside the ordinary refund cap (`DECISION_MATRIX.md`). -/
def settle_tx_dm (cfg : MitigationConfig) (txGas intrinsicExec : Nat) (m : DecisionMeter) :
    Nat × Nat × Nat :=
  let gasUsedBeforeRefund := txGas - intrinsicExec - m.gasLeft - m.stateGasReservoir
  let clearRepaid :=
    match cfg.inv2 with
    | .cappedRefundCounter => min (gasUsedBeforeRefund / 5) m.deferredRefill
    | _ => m.deferredRefill
  let deferredRepaid := clearRepaid + m.deferredRevert
  let senderPaid := gasUsedBeforeRefund - deferredRepaid
  let unusedReturned := m.gasLeft + m.stateGasReservoir
  (senderPaid, unusedReturned, deferredRepaid)

/-! ## 3. Mitigation Comparison Theorems -/

/-- **Theorem (`t_dm_inv1_options_and_code_deposit_gap`)**:
Compares `INV-1` Options 1 (`legacyShareExecFirst`, `ethereum/EIPs#12581`) and 2 (`codeDepositOnlyReservoir`)
against `D0` (`reservoirFirst`):
1. Component legacy-share split on `(m0 = (1,000,000, 1,000,000))`: slot `(10,000, 87,920)`, new account
   `(25,000, 158,600)`, `CREATE` `(20,000, 163,600)`, and 1 KiB code deposit `(566,720, 1,000,000)`.
2. Low-gas failure-handler SSTORE gate (`gasLeft = 15,000`, `reservoir = 1,000,000`): after charging
   `COLD_STORAGE_ACCESS + STORAGE_WRITE = 12,100` (`gasLeft = 2,900 > 2,300` sentry), `D0` (`reservoirFirst`)
   ALLOWS a fresh cold `SSTORE` (`charge_state_dm = some ...`), whereas BOTH Option 1 (`legacyShareExecFirst`,
   needing `10,000 > 2,900` from `gasLeft`) and Option 2 (`codeDepositOnlyReservoir`, needing `97,920 > 2,900`)
   REJECT it (`none`).
3. Code-deposit failure-handler gap: with `gasLeft = 5,000` and `reservoir = 2,000,000`, Option 1 still
   funds a `1024`-byte code deposit (`1,566,720` from reservoir, `0` from `gasLeft`), leaving code-deploying
   low-gas handlers open (`DECISION_MATRIX.md` `INV-1` Option 1 drawback).
4. `TX_MAX_GAS_LIMIT` (`2^24 = 16,777,216`) wall under Option 2 (`pr12581` rationale): each fresh cold `SSTORE`
   consumes `12,100 + 97,920 = 110,020` from `gasLeft`; after `21,000` intrinsic gas, `152` fresh cold `SSTORE`s
   fit below `TX_MAX_GAS_LIMIT` (`21,000 + 152 * 110,020 = 16,744,040 ≤ 16,777,216`) while the `153`rd exceeds
   `TX_MAX_GAS_LIMIT` (`21,000 + 153 * 110,020 = 16,854,060 > 16,777,216`), whereas Option 1 fits `757` slots! -/
theorem t_dm_inv1_options_and_code_deposit_gap :
    let cfgD0 : MitigationConfig := ⟨.reservoirFirst, .lifoToGasLeft, .restoreSpillToGasLeft, false⟩
    let cfg : MitigationConfig := ⟨.legacyShareExecFirst, .reservoirOnly, .restoreToReservoir, true⟩
    let cfgCdOnly : MitigationConfig :=
      ⟨.codeDepositOnlyReservoir, .reservoirOnly, .restoreToReservoir, true⟩
    let m0 := init_decision_meter 1000000 1000000
    let mLowSstore := init_decision_meter 2900 1000000
    let mLowDeploy := init_decision_meter 5000 2000000
    let slotP : StateChargeParams :=
      { amount := STATE_GAS_STORAGE_SET
        legacyShare := LEGACY_SHARE_STORAGE_SET
        isCodeDeposit := false }
    let acctP : StateChargeParams :=
      { amount := STATE_GAS_NEW_ACCOUNT
        legacyShare := LEGACY_SHARE_NEW_ACCOUNT
        isCodeDeposit := false }
    let createP : StateChargeParams :=
      { amount := STATE_GAS_NEW_ACCOUNT
        legacyShare := LEGACY_SHARE_CREATE
        isCodeDeposit := false }
    let depositP : StateChargeParams :=
      { amount := 1024 * COST_PER_STATE_BYTE, legacyShare := 0, isCodeDeposit := true }
    let opt2PerColdSlot := GAS_COLD_STORAGE_ACCESS + GAS_STORAGE_WRITE + STATE_GAS_STORAGE_SET
    let opt1ExecPerColdSlot := GAS_COLD_STORAGE_ACCESS + GAS_STORAGE_WRITE + LEGACY_SHARE_STORAGE_SET
    (charge_state_dm cfg m0 slotP).map
      (fun m => (m0.gasLeft - m.gasLeft, m0.stateGasReservoir - m.stateGasReservoir)) =
      some (10000, 87920) ∧
    (charge_state_dm cfg m0 acctP).map
      (fun m => (m0.gasLeft - m.gasLeft, m0.stateGasReservoir - m.stateGasReservoir)) =
      some (25000, 158600) ∧
    (charge_state_dm cfg m0 createP).map
      (fun m => (m0.gasLeft - m.gasLeft, m0.stateGasReservoir - m.stateGasReservoir)) =
      some (20000, 163600) ∧
    (charge_state_dm cfg m0 depositP).map
      (fun m => (m0.gasLeft - m.gasLeft, m0.stateGasReservoir - m.stateGasReservoir)) =
      some (566720, 1000000) ∧
    (charge_state_dm cfgCdOnly m0 slotP).map
      (fun m => (m0.gasLeft - m.gasLeft, m0.stateGasReservoir - m.stateGasReservoir)) =
      some (97920, 0) ∧
    (charge_state_dm cfgD0 mLowSstore slotP).isSome = true ∧
    charge_state_dm cfg mLowSstore slotP = none ∧
    charge_state_dm cfgCdOnly mLowSstore slotP = none ∧
    (charge_state_dm cfg mLowDeploy depositP).map (fun m => m.gasLeft) = some 5000 ∧
    21000 + 152 * opt2PerColdSlot ≤ TX_MAX_GAS_LIMIT ∧
    TX_MAX_GAS_LIMIT < 21000 + 153 * opt2PerColdSlot ∧
    21000 + 757 * opt1ExecPerColdSlot ≤ TX_MAX_GAS_LIMIT := by
  decide

/-- **Theorem (`t_dm_inv2_options_comparison`)**:
Slot-clear refill options compared universally and on `0 → 1 → 0 → 1` reuse + settlement:
1. Universal mid-frame `gasLeft` non-refill: for ALL meters `m` and clear amounts `amt`, ALL THREE
   `INV-2` options (`reservoirOnly`, `deferredUncappedCounter`, `cappedRefundCounter`) preserve
   `(refill_clear_dm cfg m amt).gasLeft = m.gasLeft`, whereas `lifoToGasLeft` refills `gasLeft`.
2. Mid-tx `0 → 1 → 0 → 1` state reuse separation: after clearing a spilled slot (`97,920`) with
   `gasLeft = 2,080`, a second `0 → 1` slot write (`97,920`) SUCCEEDS from the refilled reservoir under
   `reservoirOnly` (`some`), whereas BOTH deferred-counter options (`deferredUncappedCounter` and
   `cappedRefundCounter`) OOG (`none`) because `deferredRefill` is withheld until settlement.
3. Settlement `20%` refund-cap separation: `deferredUncappedCounter` repays the full `97,920` (`senderPaid = 0`),
   whereas `cappedRefundCounter` clamps slot-clear repayment to `19,584` (`senderPaid = 78,336`) while
   still repaying `INV-3` `deferredRevert` uncapped (`DECISION_MATRIX.md`). -/
theorem t_dm_inv2_options_comparison :
    (∀ (cfg : MitigationConfig) (m : DecisionMeter) (amt : Nat),
      cfg.inv2 ≠ .lifoToGasLeft → (refill_clear_dm cfg m amt).gasLeft = m.gasLeft) ∧
    (let m0 := init_decision_meter 100000 0
     let mCharged : DecisionMeter :=
       { m0 with gasLeft := 2080, stateGasSpilled := 97920, evmStateGasUsed := 97920 }
     let slotD0 : StateChargeParams := { amount := 97920, legacyShare := 0, isCodeDeposit := false }
     let cfgLifo : MitigationConfig := ⟨.reservoirFirst, .lifoToGasLeft, .restoreSpillToGasLeft, false⟩
     let cfgRes : MitigationConfig := ⟨.reservoirFirst, .reservoirOnly, .restoreToReservoir, true⟩
     let cfgUncapped : MitigationConfig :=
       ⟨.reservoirFirst, .deferredUncappedCounter, .restoreToReservoir, true⟩
     let cfgCapped : MitigationConfig :=
       ⟨.reservoirFirst, .cappedRefundCounter, .restoreToReservoir, true⟩
     let cfgMixed : MitigationConfig :=
       ⟨.reservoirFirst, .cappedRefundCounter, .deferRevertToSettlement, true⟩
     let lifo := refill_clear_dm cfgLifo mCharged 97920
     let resOnly := refill_clear_dm cfgRes mCharged 97920
     let deferred := refill_clear_dm cfgUncapped mCharged 97920
     let capped := refill_clear_dm cfgCapped mCharged 97920
     let mixedWithRevert := { capped with deferredRevert := 50000 }
     lifo.gasLeft = 100000 ∧ lifo.stateGasReservoir = 0 ∧
     resOnly.gasLeft = 2080 ∧ resOnly.stateGasReservoir = 97920 ∧
     (charge_state_dm cfgRes resOnly slotD0).isSome = true ∧
     deferred.gasLeft = 2080 ∧ deferred.stateGasReservoir = 0 ∧ deferred.deferredRefill = 97920 ∧
     charge_state_dm cfgUncapped deferred slotD0 = none ∧
     capped.gasLeft = 2080 ∧ capped.stateGasReservoir = 0 ∧ capped.deferredRefill = 97920 ∧
     charge_state_dm cfgCapped capped slotD0 = none ∧
     settle_tx_dm cfgUncapped 121000 21000 deferred = (0, 2080, 97920) ∧
     settle_tx_dm cfgCapped 121000 21000 capped = (78336, 2080, 19584) ∧
     settle_tx_dm cfgMixed 171000 21000 mixedWithRevert = (68336, 2080, 79584)) := by
  refine ⟨?_, by decide⟩
  intro cfg m amt h_ne
  unfold refill_clear_dm
  cases h : cfg.inv2 <;> simp_all

/-- **Theorem (`t_dm_inv3_options_comparison`)**:
Reverting-intermediary options compared universally and on sibling state reuse, negative-credit
rollback (`ethereum/EIPs#12581`), and fee retention:
1. Universal parent `try/catch` spill-funding block: for ALL parent/child meters and ALL `cfg` with
   `cfg.inv3 ≠ .restoreSpillToGasLeft`, `(exit_child_dm cfg parent child .revert).gasLeft = parent.gasLeft + child.gasLeft`
   (zero spilled state gas returns to parent `gasLeft`).
2. Negative-credit rollback exactness (`#12581`): for ANY child meter satisfying the `#12581` frame
   accounting identity `(child.stateGasReservoir : Int) + (child.evmStateGasUsed - child.usedSnapshot) =
   (child.reservoirSnapshot + nonHaltedSpill : Nat)` (even when `child.evmStateGasUsed - child.usedSnapshot < 0`
   because the child cleared an earlier frame's slot before reverting), `.restoreToReservoir` restores
   `stateGasReservoir = child.reservoirSnapshot + nonHaltedSpill ≥ 0` without `toNat` clamping.
3. Sibling state-reuse & settlement separation: after a reverting child spills `50,000` state gas
   (`reservoirSnapshot = 0`, parent `gasLeft = 5,000`, `child.gasLeft = 0`), `restoreToReservoir`
   restores `50,000` to `stateGasReservoir` so a sibling write SUCCEEDS (`some`), whereas BOTH
   `deferRevertToSettlement` (`INV-3` Opt 1) and `consumeRevertStateGas` (`INV-3` Opt 2) OOG (`none`);
   at settlement Opt 1 repays `50,000` (`senderPaid = 0`) while Opt 2 retains it (`senderPaid = 50,000`). -/
theorem t_dm_inv3_options_comparison :
    (∀ (cfg : MitigationConfig) (parent child : DecisionMeter),
      cfg.inv3 ≠ .restoreSpillToGasLeft →
      (exit_child_dm cfg parent child .revert).gasLeft = parent.gasLeft + child.gasLeft) ∧
    (∀ (cfg : MitigationConfig) (parent child : DecisionMeter) (nonHaltedSpill : Nat),
      cfg.inv3 = .restoreToReservoir →
      (child.stateGasReservoir : Int) + (child.evmStateGasUsed - child.usedSnapshot) =
        ((child.reservoirSnapshot + nonHaltedSpill : Nat) : Int) →
      (exit_child_dm cfg parent child .revert).stateGasReservoir =
        child.reservoirSnapshot + nonHaltedSpill) ∧
    (let parent := init_decision_meter 50000 950000
     let child : DecisionMeter :=
       { gasLeft := 10000
         stateGasReservoir := 850000
         stateGasSpilled := 50000
         evmStateGasUsed := 150000
         reservoirSnapshot := 950000
         usedSnapshot := 0
         deferredRefill := 0
         deferredRevert := 0 }
     let cfgA : MitigationConfig := ⟨.reservoirFirst, .lifoToGasLeft, .restoreSpillToGasLeft, false⟩
     let cfgB : MitigationConfig := ⟨.reservoirFirst, .reservoirOnly, .restoreToReservoir, true⟩
     let cfgC : MitigationConfig := ⟨.reservoirFirst, .reservoirOnly, .deferRevertToSettlement, true⟩
     let cfgD : MitigationConfig := ⟨.reservoirFirst, .reservoirOnly, .consumeRevertStateGas, true⟩
     let a := exit_child_dm cfgA parent child .revert
     let b := exit_child_dm cfgB parent child .revert
     let c := exit_child_dm cfgC parent child .revert
     let d := exit_child_dm cfgD parent child .revert
     let negChild := refill_clear_dm cfgB
       { (init_decision_meter 10000 20000) with evmStateGasUsed := 97920, usedSnapshot := 97920 }
       97920
     let negRev := exit_child_dm cfgB parent negChild .revert
     let tightParent := init_decision_meter 5000 0
     let tightChild : DecisionMeter :=
       { gasLeft := 0, stateGasReservoir := 0, stateGasSpilled := 50000, evmStateGasUsed := 50000,
         reservoirSnapshot := 0, usedSnapshot := 0, deferredRefill := 0, deferredRevert := 0 }
     let sibP : StateChargeParams := { amount := 50000, legacyShare := 0, isCodeDeposit := false }
     let tb := exit_child_dm cfgB tightParent tightChild .revert
     let tc := exit_child_dm cfgC tightParent tightChild .revert
     let td := exit_child_dm cfgD tightParent tightChild .revert
     a.gasLeft = 110000 ∧ a.stateGasReservoir = 950000 ∧
     b.gasLeft = 60000 ∧ b.stateGasReservoir = 1000000 ∧
     c.gasLeft = 60000 ∧ c.stateGasReservoir = 950000 ∧ c.deferredRevert = 50000 ∧
     d.gasLeft = 60000 ∧ d.stateGasReservoir = 950000 ∧ d.deferredRevert = 0 ∧
     negChild.evmStateGasUsed - negChild.usedSnapshot = -97920 ∧
     negRev.stateGasReservoir = 20000 ∧ negRev.evmStateGasUsed = 97920 ∧
     (charge_state_dm cfgB tb sibP).isSome = true ∧
     charge_state_dm cfgC tc sibP = none ∧
     charge_state_dm cfgD td sibP = none ∧
     settle_tx_dm cfgC 76000 21000 tc = (0, 5000, 50000) ∧
     settle_tx_dm cfgD 76000 21000 td = (50000, 5000, 0)) := by
  refine ⟨?_, ?_, by decide⟩
  · intro cfg parent child h_ne
    unfold exit_child_dm
    cases h_k : cfg.keepReservoirAcrossCalls <;> cases h_m : cfg.inv3 <;> simp_all
  · intro cfg parent child nonHaltedSpill h_m h_id
    unfold exit_child_dm
    simp only [h_m]
    omega

/-- **Theorem (`t_dm_inv5_frame_gasleft_monotonicity`)**:
Universal `INV-5` monotonicity theorem across ALL non-`gasLeft` `INV-2`/`INV-3` mitigation combinations:
1. For ANY `MitigationConfig`, execution charges and state charges never increase `gasLeft`.
2. For ANY non-`lifoToGasLeft` `INV-2` mode (`reservoirOnly`, `deferredUncappedCounter`, or
   `cappedRefundCounter`), slot-clear refills leave `gasLeft` strictly unchanged.
3. For `keepReservoirAcrossCalls = true` and ANY non-`restoreSpillToGasLeft` `INV-3` mode
   (`restoreToReservoir`, `deferRevertToSettlement`, or `consumeRevertStateGas`), a child frame returns
   at most its unused `child.gasLeft` (`(exit_child_dm cfg parent child st).gasLeft ≤ parent.gasLeft + child.gasLeft`). -/
theorem t_dm_inv5_frame_gasleft_monotonicity
    (cfg : MitigationConfig) (m parent child post : DecisionMeter)
    (execAmount : Nat) (p : StateChargeParams) (st : ChildStatus) :
    (charge_exec_dm m execAmount = some post → post.gasLeft ≤ m.gasLeft) ∧
    (charge_state_dm cfg m p = some post → post.gasLeft ≤ m.gasLeft) ∧
    (cfg.inv2 ≠ .lifoToGasLeft →
      (refill_clear_dm cfg m p.amount).gasLeft = m.gasLeft) ∧
    (cfg.keepReservoirAcrossCalls = true ∧ cfg.inv3 ≠ .restoreSpillToGasLeft →
      (exit_child_dm cfg parent child st).gasLeft ≤ parent.gasLeft + child.gasLeft) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    unfold charge_exec_dm at h
    by_cases h_lt : m.gasLeft < execAmount
    · simp [h_lt] at h
    · simp [h_lt] at h
      subst h
      exact Nat.sub_le m.gasLeft execAmount
  · intro h
    unfold charge_state_dm at h
    dsimp only at h
    by_cases h_lt :
        m.gasLeft <
          (match cfg.inv1 with
            | .reservoirFirst => 0
            | .legacyShareExecFirst => min p.amount p.legacyShare
            | .codeDepositOnlyReservoir => if p.isCodeDeposit then 0 else p.amount) +
            (p.amount -
              (match cfg.inv1 with
                | .reservoirFirst => 0
                | .legacyShareExecFirst => min p.amount p.legacyShare
                | .codeDepositOnlyReservoir => if p.isCodeDeposit then 0 else p.amount) -
              min
                (p.amount -
                  (match cfg.inv1 with
                    | .reservoirFirst => 0
                    | .legacyShareExecFirst => min p.amount p.legacyShare
                    | .codeDepositOnlyReservoir => if p.isCodeDeposit then 0 else p.amount))
                m.stateGasReservoir)
    · simp [h_lt] at h
    · simp [h_lt] at h
      subst h
      exact Nat.sub_le m.gasLeft _
  · intro h_cfg
    unfold refill_clear_dm
    cases h_m : cfg.inv2 <;> simp_all
  · rintro ⟨h_keep, h_inv3⟩
    unfold exit_child_dm
    cases st with
    | success =>
      simp [h_keep]
    | halt =>
      dsimp only
      omega
    | revert =>
      cases h_m : cfg.inv3 <;> simp_all <;> omega

/-! ## 4. `ethereum/EIPs#12581` (`2ba9176f`) Normative Vectors & CALL Ordering -/

/-- Signed meter delta `(gasLeft_after - gasLeft_before, reservoir_after - reservoir_before, evmStateGasUsed)`. -/
def meter_delta_dm (g0 r0 : Nat) (m : DecisionMeter) : Int × Int × Int :=
  ((m.gasLeft : Int) - (g0 : Int), (m.stateGasReservoir : Int) - (r0 : Int), m.evmStateGasUsed)

/-- **Theorem (`t_dm_pr12581_eight_normative_vectors_and_call_ordering`)**:
Machine-checks the 8 normative test cases of `EIPS/eip-8037.md` (PR #12581 @ `2ba9176f`), the
value-`CALL` 63/64 table for `reservoir = 1,000,000` and `reservoir = 0`, the buggy post-63/64
spurious OOG, and the pre-execution OOG boundary `min(txGas, TX_MAX_GAS_LIMIT)`.
Signed deltas are `(gasLeft_after - gasLeft_before, reservoir_after - reservoir_before, evmStateGasUsed)`. -/
theorem t_dm_pr12581_eight_normative_vectors_and_call_ordering :
    let cfg : MitigationConfig := ⟨.legacyShareExecFirst, .reservoirOnly, .restoreToReservoir, true⟩
    let slotP : StateChargeParams :=
      { amount := STATE_GAS_STORAGE_SET
        legacyShare := LEGACY_SHARE_STORAGE_SET
        isCodeDeposit := false }
    let createP : StateChargeParams :=
      { amount := STATE_GAS_NEW_ACCOUNT
        legacyShare := LEGACY_SHARE_CREATE
        isCodeDeposit := false }
    let case1 :=
      match charge_exec_dm (init_decision_meter 1000000 1000000)
          (GAS_COLD_STORAGE_ACCESS + GAS_STORAGE_WRITE) with
      | none => none
      | some m1 => (charge_state_dm cfg m1 slotP).map (meter_delta_dm 1000000 1000000)
    let case2 :=
      match charge_exec_dm (init_decision_meter 1000000 50000)
          (GAS_COLD_STORAGE_ACCESS + GAS_STORAGE_WRITE) with
      | none => none
      | some m1 => (charge_state_dm cfg m1 slotP).map (meter_delta_dm 1000000 50000)
    let case3 :=
      match charge_exec_dm (init_decision_meter 1000000 0)
          (GAS_COLD_STORAGE_ACCESS + GAS_STORAGE_WRITE) with
      | none => none
      | some m1 => (charge_state_dm cfg m1 slotP).map (meter_delta_dm 1000000 0)
    let case4 :=
      match charge_exec_dm (init_decision_meter 1000000 1000000)
          (GAS_WARM_ACCESS + GAS_STORAGE_WRITE) with
      | none => none
      | some m1 => (charge_state_dm cfg m1 slotP).map (meter_delta_dm 1000000 1000000)
    let case5 :=
      match charge_exec_dm (init_decision_meter 1000000 1000000)
          (GAS_COLD_STORAGE_ACCESS + GAS_STORAGE_WRITE) with
      | none => none
      | some m1 =>
        match charge_state_dm cfg m1 slotP with
        | none => none
        | some m2 =>
          match charge_exec_dm m2 GAS_WARM_ACCESS with
          | none => none
          | some m3 =>
            let m4 := refill_clear_dm cfg m3 STATE_GAS_STORAGE_SET
            some (meter_delta_dm 1000000 1000000 m4)
    let case6 :=
      match charge_exec_dm (init_decision_meter 1000000 1000000) Spec.GAS_CREATE_ACCESS with
      | none => none
      | some m1 => (charge_state_dm cfg m1 createP).map (meter_delta_dm 1000000 1000000)
    let case7 :=
      let parentWithheld := init_decision_meter 900000 1000000
      let child0 : DecisionMeter :=
        { parentWithheld with gasLeft := 100000, reservoirSnapshot := 1000000, usedSnapshot := 0 }
      match charge_exec_dm child0 (GAS_COLD_STORAGE_ACCESS + GAS_STORAGE_WRITE) with
      | none => none
      | some c1 =>
        match charge_state_dm cfg c1 slotP with
        | none => none
        | some c2 =>
          let merged := exit_child_dm cfg parentWithheld c2 .revert
          some (meter_delta_dm 1000000 1000000 merged)
    let case8 :=
      let parentWithheld := init_decision_meter 900000 1000000
      let child0 : DecisionMeter :=
        { parentWithheld with gasLeft := 100000, reservoirSnapshot := 1000000, usedSnapshot := 0 }
      match charge_exec_dm child0 (GAS_COLD_STORAGE_ACCESS + GAS_STORAGE_WRITE) with
      | none => none
      | some c1 =>
        match charge_state_dm cfg c1 slotP with
        | none => none
        | some c2 =>
          let merged := exit_child_dm cfg parentWithheld c2 .halt
          some (meter_delta_dm 1000000 1000000 merged)
    let valueCallFunded := enter_call_with_new_account_dm cfg (init_decision_meter 1000000 1000000)
    let valueCallEmpty := enter_call_with_new_account_dm cfg (init_decision_meter 1000000 0)
    let buggyPost63_64 : Option DecisionMeter :=
      let m0 := init_decision_meter 1000000 1000000
      match charge_exec_dm m0 (GAS_COLD_ACCOUNT_ACCESS + GAS_CALL_VALUE) with
      | none => none
      | some m1 =>
        let forwarded := max_message_call_gas m1.gasLeft
        let retained := m1.gasLeft - forwarded
        let p : StateChargeParams :=
          { amount := STATE_GAS_NEW_ACCOUNT
            legacyShare := LEGACY_SHARE_NEW_ACCOUNT
            isCodeDeposit := false }
        charge_state_dm cfg { m1 with gasLeft := retained } p
    case1 = some (-22100, -87920, 97920) ∧
    case2 = some (-60020, -50000, 97920) ∧
    case3 = some (-110020, 0, 97920) ∧
    case4 = some (-20100, -87920, 97920) ∧
    case5 = some (-22200, 10000, 0) ∧
    case6 = some (-32000, -163600, 183600) ∧
    case7 = some (-22100, 10000, 0) ∧
    case8 = some (-100000, 0, 0) ∧
    valueCallFunded =
      some (945690, 15010, { init_decision_meter 15010 841400 with
        stateGasSpilled := 25000, evmStateGasUsed := 183600, reservoirSnapshot := 1000000 }) ∧
    valueCallEmpty =
      some (789568, 12532, { init_decision_meter 12532 0 with
        stateGasSpilled := 183600, evmStateGasUsed := 183600, reservoirSnapshot := 0 }) ∧
    buggyPost63_64 = none ∧
    settle_pre_exec_oog_dm 20000000 21000 3222784 = (16777216, 3222784) := by
  decide

/-! ## 5. C-ABI Exports -/

@[inline, export glamsterdam_dm_legacy_share_cabi]
def glamsterdam_dm_legacy_share_cabi (stateGasCharge preForkCost execGasCharge : UInt64) : UInt64 :=
  (compute_legacy_share stateGasCharge.toNat preForkCost.toNat execGasCharge.toNat).toUInt64

@[inline, export glamsterdam_dm_value_call_forwarded_cabi]
def glamsterdam_dm_value_call_forwarded_cabi (gasLeft reservoir : UInt64) : UInt64 :=
  let cfg : MitigationConfig := ⟨.legacyShareExecFirst, .reservoirOnly, .restoreToReservoir, true⟩
  match enter_call_with_new_account_dm cfg (init_decision_meter gasLeft.toNat reservoir.toNat) with
  | some (forwarded, _, _) => forwarded.toUInt64
  | none => 0

@[inline, export glamsterdam_dm_pre_exec_oog_paid_cabi]
def glamsterdam_dm_pre_exec_oog_paid_cabi (txGas intrinsicExec reservoir : UInt64) : UInt64 :=
  (settle_pre_exec_oog_dm txGas.toNat intrinsicExec.toNat reservoir.toNat).1.toUInt64

@[inline, export glamsterdam_dm_settle_capped_repaid_cabi]
def glamsterdam_dm_settle_capped_repaid_cabi
    (txGas intrinsicExec gasLeft reservoir deferredRefill deferredRevert : UInt64) : UInt64 :=
  let cfg : MitigationConfig :=
    ⟨.legacyShareExecFirst, .cappedRefundCounter, .deferRevertToSettlement, true⟩
  let m : DecisionMeter :=
    { init_decision_meter gasLeft.toNat reservoir.toNat with
      deferredRefill := deferredRefill.toNat
      deferredRevert := deferredRevert.toNat }
  (settle_tx_dm cfg txGas.toNat intrinsicExec.toNat m).2.2.toUInt64

end Glamsterdam.Gas.DecisionMatrix
