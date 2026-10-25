/-
Copyright (c) 2026 Verity Labs / LFG Labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Marchand, Verity Audit Team
-/
import Glamsterdam.Common.ElCore
import Glamsterdam.Gas.Spec

/-!
# Glamsterdam Multi-Frame Call-Tree Gas Transition Core (`FV-CORE`)

Fork-parameterized multi-frame gas-meter transition model and machine-checked theorems
for abstract multi-frame trace patterns across:
- `Osaka` (pre-EIP-8037/8038 baseline),
- `Amsterdam D0` (normative `ethereum/execution-specs` @ `16898000911c1e3caa57be08509536c10ae92d3e`:
  `src/ethereum/forks/amsterdam/vm/gas.py:260-883`, `src/ethereum/forks/amsterdam/vm/__init__.py:188-245`,
  `src/ethereum/forks/amsterdam/vm/instructions/storage.py:68-162`,
  `src/ethereum/forks/amsterdam/vm/instructions/system.py:59-186`,
  `src/ethereum/forks/amsterdam/vm/instructions/system.py:369-590`), and
- State-gas refill design variants (`D1`, `D3`, `D4`, `D13`, `D13R`, `D13S`).

Scope note: This module proves properties of the abstract multi-frame gas-meter transition
system defined below (built directly on `GasMeter` primitives from `Glamsterdam.Common.ElCore`
and `price_sstore` / `max_message_call_gas` from `Glamsterdam.Gas.Spec`), rather than full
bytecode-level execution of specific deployed contracts.
-/

namespace Glamsterdam.Gas.CallTree

open Glamsterdam.Common.Prelude
open Glamsterdam.Common.MetaSpec
open Glamsterdam.Common.ElCore
open Glamsterdam.Gas.Spec

/-! ## 1. Fork Schedule & Refill Design Variants (`R1`, `R3`, `R4`, `R5`) -/

/-- Fork and state-gas refill rule selector:
- `osaka`: Pre-8037/8038 schedule (`tx.gas ≤ 2^24`, no state-gas reservoir, `SSTORE` set = `20,000`
  execution gas, `SSTORE` reset = `2,900`, `NEW_ACCOUNT` = `25,000` execution gas).
- `amsterdamD0`: Normative EIP-8037/8038 (`16898000`) with LIFO `credit_state_gas_refund`,
  `repay_state_gas_spill` on child success, and `restore_state_gas` returning spill to `gasLeft` on revert.
- `amsterdamD1`: Refills credit `stateGasLeft` only; no `repay_state_gas_spill` on child merge.
- `amsterdamD3`: LIFO `credit_state_gas_refund` and `repay_state_gas_spill` as in `D0`, but a reverting
  child defers its `stateGasSpilled` (`deferredSpill`) to transaction settlement instead of returning it to `gasLeft`.
- `amsterdamD4`: Same as `D0` except `repay_state_gas_spill` on child merge is disabled.
- `amsterdamD13`: Combines `D1` reservoir-only refills (no merge repayment) with `D3` failed-child
  spill deferral.
- `amsterdamD13R`: `D13` plus returning failed-child reservoir draw and running `repay_state_gas_spill`
  after every child exit (both success and failure) and at top-frame exit (`settle_top_frame`).
- `amsterdamD13S`: `D13R` narrowed so child-exit spill repayment runs only on child success and is
  capped by `childExcess = child.stateGasLeft - child.stateGasBaseline`, while retaining uncapped
  `repay_state_gas_spill` at top-frame exit (`settle_top_frame`). -/
inductive ForkSchedule where
  | osaka
  | amsterdamD0
  | amsterdamD1
  | amsterdamD3
  | amsterdamD4
  | amsterdamD13
  | amsterdamD13R
  | amsterdamD13S
  deriving Repr, DecidableEq, BEq

/-- Pinned `GasCosts.CALL_STIPEND = 2300` (`src/ethereum/forks/amsterdam/vm/gas.py:84`), used as the
`SSTORE` sentry threshold in `check_gas(evm, max(gas_cost, GasCosts.CALL_STIPEND + 1))`
(`src/ethereum/forks/amsterdam/vm/instructions/storage.py:100-105`). -/
@[inline] def GAS_SSTORE_SENTRY : Nat := 2300

/-- Osaka `SSTORE` fresh-slot set cost (`20,000` execution gas, warm). -/
@[inline] def OSAKA_GAS_SSTORE_SET : Nat := 20000

/-- Osaka `SSTORE` dirty-reset refund (`19,900` added to `refund_counter` on warm `0 -> X -> 0`). -/
@[inline] def OSAKA_GAS_SSTORE_RESET_REFUND : Int := 19900

/-- Osaka `NEW_ACCOUNT` execution gas cost (`25,000`). -/
@[inline] def OSAKA_GAS_NEW_ACCOUNT : Nat := 25000

/-- Extended frame gas state pairing the 6-field `GasMeter` (`src/ethereum/forks/amsterdam/vm/gas.py:260-325`)
with `deferredSpill` (spilled execution gas from reverted children held until end-of-tx settlement
under `D3`, `D13`, `D13R`, and `D13S`). -/
structure CallFrameMeter where
  meter : GasMeter
  deferredSpill : Nat := 0
  deriving Repr, DecidableEq, BEq

/-- Child frame termination status (`src/ethereum/forks/amsterdam/vm/__init__.py:188-245`
and `src/ethereum/forks/amsterdam/vm/interpreter.py:380-388, 450-466`):
- `success`: normal return (`child.error is None`).
- `revert`: `Revert` exception (`restore_state_gas` without `forfeit_remaining_gas`).
- `halt`: `ExceptionalHalt` (`restore_state_gas` followed by `forfeit_remaining_gas`, burning
  all remaining child execution gas and restoring the child's `stateGasBaseline`). -/
inductive ChildStatus where
  | success
  | revert
  | halt
  deriving Repr, DecidableEq, BEq

/-- Charge execution gas from `CallFrameMeter` (`src/ethereum/forks/amsterdam/vm/gas.py:379-394`). -/
@[simp]
def frame_charge_exec (fm : CallFrameMeter) (amount : Nat) : Option CallFrameMeter :=
  match charge_gas_from_meter fm.meter amount with
  | none => none
  | some m' => some { fm with meter := m' }

/-- Charge state gas from `CallFrameMeter` (`src/ethereum/forks/amsterdam/vm/gas.py:413-436`). -/
@[simp]
def frame_charge_state (sched : ForkSchedule) (fm : CallFrameMeter) (stateAmount osakaExecAmount : Nat) :
    Option CallFrameMeter :=
  match sched with
  | .osaka => frame_charge_exec fm osakaExecAmount
  | _ =>
    match charge_state_gas_from_meter fm.meter stateAmount with
    | none => none
    | some m' => some { fm with meter := m' }

/-- Schedule-parameterized state-gas refill (`src/ethereum/forks/amsterdam/vm/gas.py:594-616`):
- Under `amsterdamD0`, `amsterdamD3`, `amsterdamD4`: LIFO `credit_state_gas_refund` (credits `gasLeft`
  up to `stateGasSpilled` first, then `stateGasLeft`).
- Under `amsterdamD1`, `amsterdamD13`, `amsterdamD13R`, `amsterdamD13S`: credits `stateGasLeft` only. -/
@[simp]
def frame_credit_state_refund (sched : ForkSchedule) (fm : CallFrameMeter) (amount : Nat) : CallFrameMeter :=
  match sched with
  | .osaka => fm
  | .amsterdamD0 | .amsterdamD3 | .amsterdamD4 =>
    { fm with meter := credit_state_gas_refund fm.meter amount }
  | .amsterdamD1 | .amsterdamD13 | .amsterdamD13R | .amsterdamD13S =>
    { fm with meter := { fm.meter with stateGasLeft := fm.meter.stateGasLeft + amount } }

/-- Capped spill repayment (`min cap (min stateGasLeft stateGasSpilled)`) used by `amsterdamD13S`
on successful child exit. -/
@[simp]
def repay_state_gas_spill_capped (m : GasMeter) (cap : Nat) : GasMeter :=
  let repayment := min cap (min m.stateGasLeft m.stateGasSpilled)
  { m with
    gasLeft := m.gasLeft + repayment
    stateGasLeft := m.stateGasLeft - repayment
    stateGasSpilled := m.stateGasSpilled - repayment }

/-- Spawn a child `CallFrameMeter` by deducting `childCost` execution gas from the parent,
granting `childGas` execution gas to the child, and draining 100% of the parent's `stateGasLeft`
reservoir (`src/ethereum/forks/amsterdam/vm/gas.py:689-710`), returning `(childFrame, parentWithheld)`. -/
@[simp]
def enter_child_frame (parent : CallFrameMeter) (childCost childGas : Nat) :
    Option (CallFrameMeter × CallFrameMeter) :=
  if parent.meter.gasLeft < childCost then
    none
  else
    let afterCost := parent.meter.gasLeft - childCost
    let reservoir := parent.meter.stateGasLeft
    let parentWithheld : CallFrameMeter :=
      { parent with
        meter := { parent.meter with gasLeft := afterCost, stateGasLeft := 0 } }
    let childInit : CallFrameMeter :=
      { meter := { gasLeft := childGas, stateGasLeft := reservoir, stateGasBaseline := reservoir }
        deferredSpill := 0 }
    some (childInit, parentWithheld)

/-- Incorporate a returning child `CallFrameMeter` into `parentWithheld` according to `sched` and `status`
(`src/ethereum/forks/amsterdam/vm/__init__.py:188-245`, `src/ethereum/forks/amsterdam/vm/interpreter.py:380-388, 450-466`,
and `src/ethereum/forks/amsterdam/vm/gas.py:493-517, 619-647`):
- On `.success`: merges `gasLeft`, `stateGasLeft`, `stateGasSpilled`, and `refundCounter`; then runs
  `repay_state_gas_spill` (for `D0`, `D3`, `D13R`) or `repay_state_gas_spill_capped` with
  `childExcess = c.stateGasLeft - c.stateGasBaseline` (for `D13S`).
- On `.revert`: under `osaka`, `D0`, `D1`, `D4`, runs `restore_state_gas c` followed by
  `incorporate_child_meter p cRestored true` (returning `c.stateGasSpilled` to `p.gasLeft`);
  under `D3`, `D13`, `D13R`, `D13S`, returns `c.gasLeft` to `p.gasLeft` and `c.stateGasBaseline` to
  `p.stateGasLeft` while deferring `c.stateGasSpilled + child.deferredSpill` into `deferredSpill`
  (and under `D13R`, runs `repay_state_gas_spill` on `p`).
- On `.halt` (`ExceptionalHalt`): runs `forfeit_remaining_gas (restore_state_gas c)` followed by
  `incorporate_child_meter p cHalted true` (which zeroes `c`'s execution gas and returns `c.stateGasBaseline`
  to `p.stateGasLeft`, discarding `child.deferredSpill`), plus `repay_state_gas_spill` under `D13R`. -/
def exit_child_frame (sched : ForkSchedule) (parentWithheld child : CallFrameMeter) (status : ChildStatus) :
    CallFrameMeter :=
  let p := parentWithheld.meter
  let c := child.meter
  match status with
  | .success =>
    let mergedMeter : GasMeter :=
      { p with
        gasLeft := p.gasLeft + c.gasLeft
        stateGasLeft := p.stateGasLeft + c.stateGasLeft
        stateGasSpilled := p.stateGasSpilled + c.stateGasSpilled
        refundCounter := p.refundCounter + c.refundCounter }
    let postMeter : GasMeter :=
      match sched with
      | .osaka | .amsterdamD1 | .amsterdamD4 | .amsterdamD13 => mergedMeter
      | .amsterdamD0 | .amsterdamD3 | .amsterdamD13R => repay_state_gas_spill mergedMeter
      | .amsterdamD13S =>
        let childExcess := c.stateGasLeft - c.stateGasBaseline
        repay_state_gas_spill_capped mergedMeter childExcess
    { meter := postMeter, deferredSpill := parentWithheld.deferredSpill + child.deferredSpill }
  | .revert =>
    match sched with
    | .osaka | .amsterdamD0 | .amsterdamD1 | .amsterdamD4 =>
      let cRestored := restore_state_gas c
      let mergedMeter := incorporate_child_meter p cRestored true
      { meter := mergedMeter, deferredSpill := parentWithheld.deferredSpill }
    | .amsterdamD3 | .amsterdamD13 | .amsterdamD13S =>
      let mergedMeter : GasMeter :=
        { p with
          gasLeft := p.gasLeft + c.gasLeft
          stateGasLeft := p.stateGasLeft + c.stateGasBaseline }
      { meter := mergedMeter
        deferredSpill := parentWithheld.deferredSpill + c.stateGasSpilled + child.deferredSpill }
    | .amsterdamD13R =>
      let mergedMeter : GasMeter :=
        { p with
          gasLeft := p.gasLeft + c.gasLeft
          stateGasLeft := p.stateGasLeft + c.stateGasBaseline }
      { meter := repay_state_gas_spill mergedMeter
        deferredSpill := parentWithheld.deferredSpill + c.stateGasSpilled + child.deferredSpill }
  | .halt =>
    let cHalted := forfeit_remaining_gas (restore_state_gas c)
    let mergedMeter := incorporate_child_meter p cHalted true
    let postMeter : GasMeter :=
      match sched with
      | .amsterdamD13R => repay_state_gas_spill mergedMeter
      | _ => mergedMeter
    { meter := postMeter, deferredSpill := parentWithheld.deferredSpill }

/-- Top-frame exit settlement (`process_top_level` in `D13R` and `D13S`):
At the end of top-level frame execution (when the top-level frame itself finishes without
reverting/halting), `amsterdamD13R` and `amsterdamD13S` run uncapped `repay_state_gas_spill`
(`_settle(meter, "top-exit")`) before transaction-level gas settlement. -/
@[simp]
def settle_top_frame (sched : ForkSchedule) (top : CallFrameMeter) : CallFrameMeter :=
  match sched with
  | .amsterdamD13R | .amsterdamD13S =>
    { top with meter := repay_state_gas_spill top.meter }
  | _ => top

/-! ## 2. `SSTORE` With Sentry (`R3`) and Single-Frame Invariant (`A1`) -/

/-- Execute `SSTORE` with the mandatory `gas_left <= 2300` sentry check
(`check_gas(evm, max(gas_cost, GasCosts.CALL_STIPEND + 1))` at
`src/ethereum/forks/amsterdam/vm/instructions/storage.py:100-105, 126-157`).
Crucially, `check_gas` checks ONLY `gasLeft` (ignoring `stateGasLeft`), and then follows the exact
EELS operation order at `src/ethereum/forks/amsterdam/vm/instructions/storage.py:126-157`:
1. `evm.gas_meter.refund_counter += refund` (`refundDelta`, lines 126-139),
2. `credit_state_gas_refund(evm.gas_meter, state_gas_refund)` (`stateGasRefundCredited`, lines 148-151),
3. `charge_gas(evm, gas_cost)` (`execGasCost`, line 156),
4. `charge_state_gas(evm, state_gas_cost)` (`stateGasCost`, line 157). -/
def exec_sstore_frame (sched : ForkSchedule) (fm : CallFrameMeter)
    (isCold : Bool) (origVal currVal newVal : Nat) : Option CallFrameMeter :=
  if fm.meter.gasLeft ≤ GAS_SSTORE_SENTRY then
    none
  else
    match sched with
    | .osaka =>
      let accessCost := if isCold then GAS_COLD_STORAGE_ACCESS else GAS_WARM_ACCESS
      let writeCost :=
        if currVal == newVal then 0
        else if origVal == currVal then
          if origVal == 0 then OSAKA_GAS_SSTORE_SET else 2900
        else 0
      let refundDelta : Int :=
        if currVal != newVal && origVal == newVal && origVal == 0 then
          OSAKA_GAS_SSTORE_RESET_REFUND
        else 0
      let fm0 : CallFrameMeter :=
        { fm with meter := { fm.meter with refundCounter := fm.meter.refundCounter + refundDelta } }
      frame_charge_exec fm0 (accessCost + writeCost)
    | _ =>
      let p := price_sstore isCold origVal currVal newVal
      let fm0 : CallFrameMeter :=
        { fm with meter := { fm.meter with refundCounter := fm.meter.refundCounter + p.refundDelta } }
      let fm1 : CallFrameMeter :=
        if p.stateGasRefundCredited > 0 then
          frame_credit_state_refund sched fm0 p.stateGasRefundCredited
        else
          fm0
      match frame_charge_exec fm1 p.execGasCost with
      | none => none
      | some fm2 =>
        frame_charge_state sched fm2 p.stateGasCost 0

/-- Theorem (`t_calltree_sstore_sentry_excludes_reservoir`, see `src/ethereum/forks/amsterdam/vm/instructions/storage.py:100-105`):
Whenever `fm.meter.gasLeft ≤ 2300` (such as inside a 2,300-stipend value call), `exec_sstore_frame`
halts with `none` (`OutOfGasError`) under every schedule and for every reservoir size `fm.meter.stateGasLeft`. -/
theorem t_calltree_sstore_sentry_excludes_reservoir
    (sched : ForkSchedule) (fm : CallFrameMeter) (isCold : Bool) (origVal currVal newVal : Nat)
    (h_sentry : fm.meter.gasLeft ≤ GAS_SSTORE_SENTRY) :
    exec_sstore_frame sched fm isCold origVal currVal newVal = none := by
  unfold exec_sstore_frame
  simp [h_sentry]

/-- Theorem (`t_calltree_a1_frame_bound`, see `src/ethereum/forks/amsterdam/vm/gas.py:379-616`):
Within a single frame under `amsterdamD0`, every execution charge (`charge_gas_from_meter`),
state charge (`charge_state_gas_from_meter`), and in-frame state-gas refill (`credit_state_gas_refund`)
preserves the upper bound `post.gasLeft + post.stateGasSpilled ≤ m.gasLeft + m.stateGasSpilled`. -/
theorem t_calltree_a1_frame_bound (m post : GasMeter) (amount : Nat) :
    (charge_gas_from_meter m amount = some post →
      post.gasLeft + post.stateGasSpilled ≤ m.gasLeft + m.stateGasSpilled) ∧
    (charge_state_gas_from_meter m amount = some post →
      post.gasLeft + post.stateGasSpilled ≤ m.gasLeft + m.stateGasSpilled) ∧
    ((credit_state_gas_refund m amount).gasLeft + (credit_state_gas_refund m amount).stateGasSpilled =
      m.gasLeft + m.stateGasSpilled) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    unfold charge_gas_from_meter at h
    split at h
    · contradiction
    · simp only [Option.some.injEq] at h
      subst h
      dsimp only
      omega
  · intro h
    unfold charge_state_gas_from_meter at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      dsimp only
      omega
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        dsimp only
        omega
      · contradiction
  · unfold credit_state_gas_refund
    simp only
    omega

/-! ## 3. Multi-Frame Trace Models & Refill-Variant Theorems (`E1`, `M2`, `M3`, `M4`, `D13R`, `D13S`) -/

/-- Theorem 1 (`t_calltree_e1_fixed_grant_starvation`):
When `stateGasLeft = 0` (`tx.gas ≤ 2^24`), a fixed-grant child frame with `gasLeft = 50000`
(above the `2300` sentry) that writes one warm fresh storage slot (`0 -> 1`, costing `20,100` on
Osaka and `10,100 + 97,920 = 108,020` on Amsterdam) succeeds on `osaka` (`gasLeft = 29,900`) and
deterministically runs out of gas (`none`) on EVERY Amsterdam refill variant (`D0`, `D1`, `D3`,
`D4`, `D13`, `D13R`, `D13S`). -/
theorem t_calltree_e1_fixed_grant_starvation :
    let childInit : CallFrameMeter := { meter := { gasLeft := 50000, stateGasLeft := 0, stateGasBaseline := 0 } }
    (exec_sstore_frame .osaka childInit false 0 0 1).isSome = true ∧
    exec_sstore_frame .amsterdamD0 childInit false 0 0 1 = none ∧
    exec_sstore_frame .amsterdamD1 childInit false 0 0 1 = none ∧
    exec_sstore_frame .amsterdamD3 childInit false 0 0 1 = none ∧
    exec_sstore_frame .amsterdamD4 childInit false 0 0 1 = none ∧
    exec_sstore_frame .amsterdamD13 childInit false 0 0 1 = none ∧
    exec_sstore_frame .amsterdamD13R childInit false 0 0 1 = none ∧
    exec_sstore_frame .amsterdamD13S childInit false 0 0 1 = none := by
  decide

/-- Outcome record for two-level (`parent -> child`) trace models. -/
structure M2TraceOutcome where
  outerSuccess : Bool
  childSuccess : Bool
  finalGasLeft : Nat
  finalStateGasLeft : Nat
  deriving Repr, DecidableEq, BEq

/-- Multi-frame trace model for the `T2` (`M2` set-call-clear) pattern:
1. Parent `P` starts with `entryGas` execution gas and `0` reservoir (`tx.gas ≤ 2^24`).
2. `P` writes `k` warm fresh slots (`0 -> 1`), charging `k * 10,100` execution gas and `k * 97,920` state gas.
3. `P` calls child `C` forwarding `63/64` of remaining `gasLeft` (`max_message_call_gas`); `C` needs
   `childExecNeed` execution gas and halts (`ChildStatus.halt`) if its grant is `< childExecNeed`.
4. `P` catches/ignores `C`'s return value and clears the `k` slots (`1 -> 0`), charging `k * 100`
   execution gas and crediting `k * 97,920` state-gas refill according to `sched`.
5. Optionally (`flushCall = true`, corresponding to `T2f`), `P` executes a warm `STATICCALL`
   (charging `GAS_WARM_ACCESS = 100` execution gas with `0` child execution grant) that succeeds.
6. Finally, `P` executes `postWorkExec` execution gas and runs `settle_top_frame`. -/
def run_m2_set_call_clear_trace
    (sched : ForkSchedule) (entryGas k childExecNeed postWorkExec : Nat) (flushCall : Bool) :
    M2TraceOutcome :=
  let fm0 : CallFrameMeter := { meter := { gasLeft := entryGas, stateGasLeft := 0, stateGasBaseline := 0 } }
  let setExec := if sched == .osaka then k * (GAS_WARM_ACCESS + OSAKA_GAS_SSTORE_SET) else k * (GAS_WARM_ACCESS + GAS_STORAGE_WRITE)
  let setState := if sched == .osaka then 0 else k * STATE_GAS_STORAGE_SET
  match frame_charge_exec fm0 setExec with
  | none => ⟨false, false, 0, 0⟩
  | some fm1 =>
    match frame_charge_state sched fm1 setState 0 with
    | none => ⟨false, false, 0, 0⟩
    | some fm2 =>
      let childGrant := max_message_call_gas fm2.meter.gasLeft
      match enter_child_frame fm2 childGrant childGrant with
      | none => ⟨false, false, 0, 0⟩
      | some (cInit, pWithheld) =>
        let (cFinal, cStatus, cOk) :=
          match frame_charge_exec cInit childExecNeed with
          | some cDone => (cDone, ChildStatus.success, true)
          | none => (cInit, ChildStatus.halt, false)
        let fmAfterCall := exit_child_frame sched pWithheld cFinal cStatus
        let clearExec := k * GAS_WARM_ACCESS
        match frame_charge_exec fmAfterCall clearExec with
        | none => ⟨false, cOk, 0, 0⟩
        | some fmBeforeRefill =>
          let fmAfterClear := frame_credit_state_refund sched fmBeforeRefill setState
          let fmAfterFlushOpt : Option CallFrameMeter :=
            if flushCall then
              match frame_charge_exec fmAfterClear GAS_WARM_ACCESS with
              | none => none
              | some fmWarm =>
                match enter_child_frame fmWarm 0 0 with
                | none => none
                | some (flInit, pFl) => some (exit_child_frame sched pFl flInit .success)
            else
              some fmAfterClear
          match fmAfterFlushOpt with
          | none => ⟨false, cOk, 0, 0⟩
          | some fmAfterFlush =>
            match frame_charge_exec fmAfterFlush postWorkExec with
            | none => ⟨false, cOk, 0, 0⟩
            | some fmDone =>
              let fmTop := settle_top_frame sched fmDone
              ⟨true, cOk, fmTop.meter.gasLeft, fmTop.meter.stateGasLeft⟩

/-- Theorem 2 (`t_calltree_e3_m2_dirty_clear_band_and_d13r_break`):
On the `T2` (`M2` set-call-clear) trace model (`k = 3` slots, `entryGas = 550000`,
`childExecNeed = 240000`, `postWorkExec = 50000`):
1. Under `osaka`, the parent has `489,700` gas after setting the 3 slots, grants `482,049 ≥ 240,000`
   to the child (`childSuccess = true`), and finishes with `outerSuccess = true`.
2. Under `amsterdamD0`, setting the 3 slots spills `293,760` state gas from `gasLeft`, leaving only
   `225,940` gas before the call; the child receives `222,410 < 240,000` and halts (`childSuccess = false`),
   while clearing the 3 slots refills `293,760` into `gasLeft` so the parent's `50,000` post-call work
   succeeds (`outerSuccess = true`).
3. Under `amsterdamD1` and `amsterdamD13` (`flushCall = false`), the clear credits `stateGasLeft`
   instead of `gasLeft`, so the parent only has `3,230 < 50,000` execution gas after the clear and
   halts (`outerSuccess = false`).
4. Under `amsterdamD13R` with a warm post-clear `STATICCALL` (`flushCall = true`, `T2f`), the flush
   call triggers `repay_state_gas_spill` and moves `293,760` back into `gasLeft`, re-opening the
   `outerSuccess = true ∧ childSuccess = false` outcome. -/
theorem t_calltree_e3_m2_dirty_clear_band_and_d13r_break :
    let o := run_m2_set_call_clear_trace .osaka 550000 3 240000 50000 false
    let d0 := run_m2_set_call_clear_trace .amsterdamD0 550000 3 240000 50000 false
    let d1 := run_m2_set_call_clear_trace .amsterdamD1 550000 3 240000 50000 false
    let d13 := run_m2_set_call_clear_trace .amsterdamD13 550000 3 240000 50000 false
    let d13r_noflush := run_m2_set_call_clear_trace .amsterdamD13R 550000 3 240000 50000 false
    let d13r_flush := run_m2_set_call_clear_trace .amsterdamD13R 550000 3 240000 50000 true
    (o.outerSuccess = true ∧ o.childSuccess = true) ∧
    (d0.outerSuccess = true ∧ d0.childSuccess = false) ∧
    (d1.outerSuccess = false ∧ d1.childSuccess = false) ∧
    (d13.outerSuccess = false ∧ d13.childSuccess = false) ∧
    (d13r_noflush.outerSuccess = false ∧ d13r_noflush.childSuccess = false) ∧
    (d13r_flush.outerSuccess = true ∧ d13r_flush.childSuccess = false) := by
  decide

/-- Multi-frame trace model for the `T1` pattern where a parent sets and clears `1` slot
(`0 -> 1 -> 0`) BEFORE calling `CALL(GAS)` and then executing `postWorkExec` execution gas:
- Under `amsterdamD0`, the clear before `CALL` immediately restores `97,920` to `gasLeft`, so the
  child receives `63/64` of the restored `gasLeft` and succeeds.
- Under `amsterdamD13R`, the clear before `CALL` stays in `stateGasLeft` (so the child receives
  `60,914 < 100,000` and halts), and then `D13R`'s child-exit settlement moves `97,920` from
  `stateGasLeft` into `gasLeft` upon the halted child's exit, funding `postWorkExec`. -/
def run_t1_pre_call_set_clear_trace
    (sched : ForkSchedule) (entryGas childExecNeed postWorkExec : Nat) : M2TraceOutcome :=
  let fm0 : CallFrameMeter := { meter := { gasLeft := entryGas, stateGasLeft := 0, stateGasBaseline := 0 } }
  match exec_sstore_frame sched fm0 false 0 0 1 with
  | none => ⟨false, false, 0, 0⟩
  | some fm1 =>
    match exec_sstore_frame sched fm1 false 0 1 0 with
    | none => ⟨false, false, 0, 0⟩
    | some fm2 =>
      let childGrant := max_message_call_gas fm2.meter.gasLeft
      match enter_child_frame fm2 childGrant childGrant with
      | none => ⟨false, false, 0, 0⟩
      | some (cInit, pWithheld) =>
        let (cFinal, cStatus, cOk) :=
          match frame_charge_exec cInit childExecNeed with
          | some cDone => (cDone, ChildStatus.success, true)
          | none => (cInit, ChildStatus.halt, false)
        let fmAfterCall := exit_child_frame sched pWithheld cFinal cStatus
        match frame_charge_exec fmAfterCall postWorkExec with
        | none => ⟨false, cOk, 0, 0⟩
        | some fmDone =>
          let fmTop := settle_top_frame sched fmDone
          ⟨true, cOk, fmTop.meter.gasLeft, fmTop.meter.stateGasLeft⟩

/-- Theorem 2b (`t_calltree_d13r_introduces_new_t1_band`):
At `entryGas = 170000`, `childExecNeed = 100000`, `postWorkExec = 50000`:
- `amsterdamD0` succeeds in both child and parent (`outerSuccess = true ∧ childSuccess = true`).
- `amsterdamD13R` starves the child (`childSuccess = false`) while the parent still succeeds
  (`outerSuccess = true`) because `D13R` moves `97,920` into `gasLeft` upon the failed child's exit.
- `amsterdamD13S` does not repay on failed child exit (`outerSuccess = false ∧ childSuccess = false`). -/
theorem t_calltree_d13r_introduces_new_t1_band :
    let d0 := run_t1_pre_call_set_clear_trace .amsterdamD0 170000 100000 50000
    let d13r := run_t1_pre_call_set_clear_trace .amsterdamD13R 170000 100000 50000
    let d13s := run_t1_pre_call_set_clear_trace .amsterdamD13S 170000 100000 50000
    (d0.outerSuccess = true ∧ d0.childSuccess = true) ∧
    (d13r.outerSuccess = true ∧ d13r.childSuccess = false) ∧
    (d13s.outerSuccess = false ∧ d13s.childSuccess = false) := by
  decide

/-- Multi-frame trace model for the `M3` revert-restore pattern:
1. Parent `P` starts with `entryGas` and `0` reservoir (`tx.gas ≤ 2^24`).
2. `P` calls child `C` forwarding `63/64` of `entryGas`.
3. `C` writes `k` fresh slots (`0 -> 1`, spilling `k * 97,920` state gas) plus `childOtherExec`
   execution gas, and then `REVERT`s.
4. `P` catches the revert and executes `catchWorkExec` execution gas before `settle_top_frame`. -/
def run_m3_revert_restore_trace
    (sched : ForkSchedule) (entryGas k childOtherExec catchWorkExec : Nat) : M2TraceOutcome :=
  let fm0 : CallFrameMeter := { meter := { gasLeft := entryGas, stateGasLeft := 0, stateGasBaseline := 0 } }
  let childGrant := max_message_call_gas fm0.meter.gasLeft
  match enter_child_frame fm0 childGrant childGrant with
  | none => ⟨false, false, 0, 0⟩
  | some (cInit, pWithheld) =>
    let slotExec := if sched == .osaka then k * (GAS_WARM_ACCESS + OSAKA_GAS_SSTORE_SET) else k * (GAS_WARM_ACCESS + GAS_STORAGE_WRITE)
    let slotState := if sched == .osaka then 0 else k * STATE_GAS_STORAGE_SET
    match frame_charge_exec cInit (slotExec + childOtherExec) with
    | none =>
      let fmHalt := exit_child_frame sched pWithheld cInit .halt
      match frame_charge_exec fmHalt catchWorkExec with
      | none => ⟨false, false, fmHalt.meter.gasLeft, fmHalt.meter.stateGasLeft⟩
      | some fmDone =>
        let fmTop := settle_top_frame sched fmDone
        ⟨true, false, fmTop.meter.gasLeft, fmTop.meter.stateGasLeft⟩
    | some cAfterExec =>
      match frame_charge_state sched cAfterExec slotState 0 with
      | none =>
        let fmHalt := exit_child_frame sched pWithheld cAfterExec .halt
        match frame_charge_exec fmHalt catchWorkExec with
        | none => ⟨false, false, fmHalt.meter.gasLeft, fmHalt.meter.stateGasLeft⟩
        | some fmDone =>
          let fmTop := settle_top_frame sched fmDone
          ⟨true, false, fmTop.meter.gasLeft, fmTop.meter.stateGasLeft⟩
      | some cBeforeRevert =>
        let fmAfterRevert := exit_child_frame sched pWithheld cBeforeRevert .revert
        match frame_charge_exec fmAfterRevert catchWorkExec with
        | none => ⟨false, false, fmAfterRevert.meter.gasLeft, fmAfterRevert.meter.stateGasLeft⟩
        | some fmDone =>
          let fmTop := settle_top_frame sched fmDone
          ⟨true, false, fmTop.meter.gasLeft, fmTop.meter.stateGasLeft⟩

/-- Theorem 3 (`t_calltree_e3_m3_revert_restore_catch_band`):
When `entryGas = 400000`, `k = 3` slots (`293,760` state gas), `childOtherExec = 60000`, and
`catchWorkExec = 50000`:
- Under `amsterdamD0`, `amsterdamD1`, and `amsterdamD4`, `C` receives `393,750` (`6,250` withheld),
  spends `30,300 + 60,000 = 90,300` execution gas, spills `293,760` state gas (leaving `9,690` in `C.gasLeft`),
  and `REVERT`s; `restore_state_gas` returns `293,760` to `C.gasLeft`, so `P` has `6,250 + 9,690 + 293,760 = 309,700`
  execution gas in the `catch` block and finishes `catchWorkExec = 50,000` with `finalGasLeft = 259,700`
  (`outerSuccess = true`).
- Under `amsterdamD3`, `amsterdamD13`, `amsterdamD13R`, and `amsterdamD13S`, `C`'s `293,760` spill
  is deferred to end-of-transaction settlement (`deferredSpill = 293,760`), so `P` only has
  `6,250 + 9,690 = 15,940 < 50,000` execution gas in the `catch` block (`finalGasLeft = 15940`,
  `outerSuccess = false`). -/
theorem t_calltree_e3_m3_revert_restore_catch_band :
    run_m3_revert_restore_trace .amsterdamD0 400000 3 60000 50000 = ⟨true, false, 259700, 0⟩ ∧
    run_m3_revert_restore_trace .amsterdamD1 400000 3 60000 50000 = ⟨true, false, 259700, 0⟩ ∧
    run_m3_revert_restore_trace .amsterdamD4 400000 3 60000 50000 = ⟨true, false, 259700, 0⟩ ∧
    run_m3_revert_restore_trace .amsterdamD3 400000 3 60000 50000 = ⟨false, false, 15940, 0⟩ ∧
    run_m3_revert_restore_trace .amsterdamD13 400000 3 60000 50000 = ⟨false, false, 15940, 0⟩ ∧
    run_m3_revert_restore_trace .amsterdamD13R 400000 3 60000 50000 = ⟨false, false, 15940, 0⟩ ∧
    run_m3_revert_restore_trace .amsterdamD13S 400000 3 60000 50000 = ⟨false, false, 15940, 0⟩ := by
  decide

/-- Cross-sibling `M4` trace model with a `g1 - g2` gas-measurement window around Child 2:
1. Parent `P` starts with `entryGas` and `0` reservoir (`tx.gas ≤ 2^24`).
2. Child 1 (`C1`) writes `1` fresh slot (`0 -> 1`, spilling `97,920` state gas) and returns `success`
   (so `P` inherits `stateGasSpilled = 97,920`).
3. `P` records `g1 = P.meter.gasLeft` before Child 2.
4. `P` calls Child 2 (`C2`), which clears that slot (`1 -> 0`, crediting `97,920` state gas) and
   spends `c2Exec` execution gas before returning `success`.
5. `P` records `g2 = P.meter.gasLeft` after Child 2 merges and checks whether `g2 > g1`
   (`underflowPanic = true`, where checked unsigned subtraction `g1 - g2` underflows). -/
structure M4SiblingDeltaOutcome where
  g1 : Nat
  g2 : Nat
  underflowPanic : Bool
  deriving Repr, DecidableEq, BEq

def run_m4_sibling_delta_trace (sched : ForkSchedule) (entryGas c2Exec : Nat) : Option M4SiblingDeltaOutcome :=
  let fm0 : CallFrameMeter := { meter := { gasLeft := entryGas, stateGasLeft := 0, stateGasBaseline := 0 } }
  let gC1 := max_message_call_gas fm0.meter.gasLeft
  match enter_child_frame fm0 gC1 gC1 with
  | none => none
  | some (c1Init, pWithheld1) =>
    match exec_sstore_frame sched c1Init false 0 0 1 with
    | none => none
    | some c1Done =>
      let pAfterC1 := exit_child_frame sched pWithheld1 c1Done .success
      let g1 := pAfterC1.meter.gasLeft
      let gC2 := max_message_call_gas pAfterC1.meter.gasLeft
      match enter_child_frame pAfterC1 gC2 gC2 with
      | none => none
      | some (c2Init, pWithheld2) =>
        match exec_sstore_frame sched c2Init false 0 1 0 with
        | none => none
        | some c2AfterClear =>
          match frame_charge_exec c2AfterClear c2Exec with
          | none => none
          | some c2Done =>
            let pAfterC2 := exit_child_frame sched pWithheld2 c2Done .success
            let g2 := pAfterC2.meter.gasLeft
            some ⟨g1, g2, decide (g2 > g1)⟩

/-- Theorem 4 (`t_calltree_e3_m4_sibling_underflow_and_d13s_break`):
On the `M4` cross-sibling trace (`entryGas = 500000`, `c2Exec = 20000`):
1. Under `osaka`, `amsterdamD1`, `amsterdamD4`, and `amsterdamD13`, `g2 ≤ g1` (`underflowPanic = false`).
2. Under `amsterdamD0`, `amsterdamD3`, `amsterdamD13R`, **and `amsterdamD13S`**, Child 2's `1 -> 0`
   clear yields `childExcess = 97,920 > 0`, which is moved into `P.gasLeft` upon Child 2's merge,
   causing `g2 = 469,800 > g1 = 391,980` (`underflowPanic = true`). -/
theorem t_calltree_e3_m4_sibling_underflow_and_d13s_break :
    (run_m4_sibling_delta_trace .osaka 500000 20000).map M4SiblingDeltaOutcome.underflowPanic = some false ∧
    (run_m4_sibling_delta_trace .amsterdamD1 500000 20000).map M4SiblingDeltaOutcome.underflowPanic = some false ∧
    (run_m4_sibling_delta_trace .amsterdamD4 500000 20000).map M4SiblingDeltaOutcome.underflowPanic = some false ∧
    (run_m4_sibling_delta_trace .amsterdamD13 500000 20000).map M4SiblingDeltaOutcome.underflowPanic = some false ∧
    (run_m4_sibling_delta_trace .amsterdamD0 500000 20000).map M4SiblingDeltaOutcome.underflowPanic = some true ∧
    (run_m4_sibling_delta_trace .amsterdamD3 500000 20000).map M4SiblingDeltaOutcome.underflowPanic = some true ∧
    (run_m4_sibling_delta_trace .amsterdamD13R 500000 20000).map M4SiblingDeltaOutcome.underflowPanic = some true ∧
    (run_m4_sibling_delta_trace .amsterdamD13S 500000 20000).map M4SiblingDeltaOutcome.underflowPanic = some true := by
  decide

/-- Multi-frame trace model for `T2_child_clear` (where the `k` slots are cleared inside a helper
subcall `Helper` after the main child call `C` fails):
Under `amsterdamD13S`, because `Helper` enters with `stateGasBaseline = 0` and clears `k` slots
(`Helper.stateGasLeft = k * 97,920`), `childExcess = k * 97,920 > 0`, so `D13S` moves `k * 97,920`
into `P.gasLeft` on `Helper` exit — re-opening the `T2` (`outerSuccess = true ∧ childSuccess = false`) band. -/
def run_t2_child_clear_trace
    (sched : ForkSchedule) (entryGas k childExecNeed postWorkExec : Nat) : M2TraceOutcome :=
  let fm0 : CallFrameMeter := { meter := { gasLeft := entryGas, stateGasLeft := 0, stateGasBaseline := 0 } }
  let setExec := if sched == .osaka then k * (GAS_WARM_ACCESS + OSAKA_GAS_SSTORE_SET) else k * (GAS_WARM_ACCESS + GAS_STORAGE_WRITE)
  let setState := if sched == .osaka then 0 else k * STATE_GAS_STORAGE_SET
  match frame_charge_exec fm0 setExec with
  | none => ⟨false, false, 0, 0⟩
  | some fm1 =>
    match frame_charge_state sched fm1 setState 0 with
    | none => ⟨false, false, 0, 0⟩
    | some fm2 =>
      let childGrant := max_message_call_gas fm2.meter.gasLeft
      match enter_child_frame fm2 childGrant childGrant with
      | none => ⟨false, false, 0, 0⟩
      | some (cInit, pWithheld) =>
        let (cFinal, cStatus, cOk) :=
          match frame_charge_exec cInit childExecNeed with
          | some cDone => (cDone, ChildStatus.success, true)
          | none => (cInit, ChildStatus.halt, false)
        let fmAfterCall := exit_child_frame sched pWithheld cFinal cStatus
        let helperGrant := max_message_call_gas fmAfterCall.meter.gasLeft
        match enter_child_frame fmAfterCall helperGrant helperGrant with
        | none => ⟨false, cOk, 0, 0⟩
        | some (hInit, pHelperWithheld) =>
          match frame_charge_exec hInit (k * GAS_WARM_ACCESS) with
          | none => ⟨false, cOk, 0, 0⟩
          | some hBeforeRefill =>
            let hAfterClear := frame_credit_state_refund sched hBeforeRefill setState
            let fmAfterHelper := exit_child_frame sched pHelperWithheld hAfterClear .success
            match frame_charge_exec fmAfterHelper postWorkExec with
            | none => ⟨false, cOk, 0, 0⟩
            | some fmDone =>
              let fmTop := settle_top_frame sched fmDone
              ⟨true, cOk, fmTop.meter.gasLeft, fmTop.meter.stateGasLeft⟩

/-- Theorem 4b (`t_calltree_d13s_reopens_t2_on_child_clear`):
When the 3 slots in `T2` are cleared by a helper subcall (`entryGas = 550000`, `k = 3`,
`childExecNeed = 240000`, `postWorkExec = 50000`):
- `amsterdamD1` and `amsterdamD13` remain safe (`outerSuccess = false ∧ childSuccess = false`).
- `amsterdamD13S` re-opens the `outerSuccess = true ∧ childSuccess = false` band. -/
theorem t_calltree_d13s_reopens_t2_on_child_clear :
    let d1 := run_t2_child_clear_trace .amsterdamD1 550000 3 240000 50000
    let d13 := run_t2_child_clear_trace .amsterdamD13 550000 3 240000 50000
    let d13s := run_t2_child_clear_trace .amsterdamD13S 550000 3 240000 50000
    (d1.outerSuccess = false ∧ d1.childSuccess = false) ∧
    (d13.outerSuccess = false ∧ d13.childSuccess = false) ∧
    (d13s.outerSuccess = true ∧ d13s.childSuccess = false) := by
  decide

/-- Exact `GasCosts.CREATE_ACCESS` (`ACCOUNT_WRITE + COLD_ACCOUNT_ACCESS = 9000 + 3000 = 12,000`
at `src/ethereum/forks/amsterdam/vm/gas.py:90`, charged by `create` at
`src/ethereum/forks/amsterdam/vm/instructions/system.py:215-218` @ `16898000`). -/
def GAS_CREATE_ACCESS : Nat := 12000

/-- Validated gas-schedule projection (`mapping_kind: projection`) of `T6`
(`src/ethereum/forks/amsterdam/vm/instructions/system.py:107-180` and
`src/ethereum/forks/amsterdam/vm/instructions/system.py:215-218` @ `16898000`): a failed `CREATE`
where the parent frame charges `GAS_CREATE_ACCESS = 12,000` execution gas (`src/ethereum/forks/amsterdam/vm/gas.py:90`,
`src/ethereum/forks/amsterdam/vm/instructions/system.py:215-218`, isolating the fixed base access charge of `create`)
and `STATE_GAS_NEW_ACCOUNT = 183,600` (`120 * 1530`, `src/ethereum/forks/amsterdam/vm/gas.py:54-56`,
`src/ethereum/forks/amsterdam/vm/instructions/system.py:109`) before `withhold_create_gas`
(`src/ethereum/forks/amsterdam/vm/instructions/system.py:113`), the child `init_code` immediately `REVERT`s (`0` gas spent), and
the parent receives `credit_state_gas_refund` for `STATE_GAS_NEW_ACCOUNT` (`src/ethereum/forks/amsterdam/vm/instructions/system.py:180`) AFTER
`incorporate_child` (`src/ethereum/forks/amsterdam/vm/instructions/system.py:177`), followed by a warm `STATICCALL` costing
`GAS_WARM_ACCESS = 100` execution gas and `postCreateExec` parent execution work before `settle_top_frame`:
- Under `amsterdamD0`, `credit_state_gas_refund` immediately returns `183,600` to `P.gasLeft`.
- Under `amsterdamD13R`, the subsequent `STATICCALL` exit triggers `repay_state_gas_spill`, returning
  `183,600` to `P.gasLeft` mid-frame so `postCreateExec` can spend it.
- Under `amsterdamD13S`, `credit_state_gas_refund` runs AFTER `incorporate_child` and puts `183,600`
  into `P.stateGasLeft` while `P.stateGasSpilled = 183,600`; furthermore, even after the subsequent
  successful `STATICCALL`, `childExcess = 0` (`sInit.stateGasLeft = 183,600 <= sInit.stateGasBaseline = 183,600`),
  so the subsequent child exit cannot flush the `183,600` refund into `P.gasLeft` either. Thus `183,600`
  execution gas remains stranded in `stateGasLeft` throughout the remainder of `P`'s execution (starving
  `postCreateExec = 850,000` so `P` halts mid-frame with `none` before `settle_top_frame` is ever reached,
  whereas if `postCreateExec = 0`, `settle_top_frame` recovers `183,600` at top-frame exit). -/
def run_t6_failed_create_trace (sched : ForkSchedule) (entryGas postCreateExec : Nat) (applyTopExit : Bool) :
    Option CallFrameMeter :=
  let fm0 : CallFrameMeter := { meter := { gasLeft := entryGas, stateGasLeft := 0, stateGasBaseline := 0 } }
  match frame_charge_exec fm0 GAS_CREATE_ACCESS with
  | none => none
  | some fm1 =>
    match frame_charge_state sched fm1 STATE_GAS_NEW_ACCOUNT 0 with
    | none => none
    | some fm2 =>
      let childGrant := max_message_call_gas fm2.meter.gasLeft
      match enter_child_frame fm2 childGrant childGrant with
      | none => none
      | some (cInit, pWithheld) =>
        let fmAfterMerge := exit_child_frame sched pWithheld cInit .revert
        let fmAfterRefill := frame_credit_state_refund sched fmAfterMerge STATE_GAS_NEW_ACCOUNT
        match frame_charge_exec fmAfterRefill GAS_WARM_ACCESS with
        | none => none
        | some fmBeforeStatic =>
          match enter_child_frame fmBeforeStatic 0 0 with
          | none => none
          | some (sInit, pStaticWithheld) =>
            let fmMidFrame := exit_child_frame sched pStaticWithheld sInit .success
            match frame_charge_exec fmMidFrame postCreateExec with
            | none => none
            | some fmAfterPost =>
              some (if applyTopExit then settle_top_frame sched fmAfterPost else fmAfterPost)

/-- Theorem 4c (`t_calltree_d13s_failed_create_strands_gas`):
On `entryGas = 1000000`, after a `CREATE` (`GAS_CREATE_ACCESS = 12,000`, `STATE_GAS_NEW_ACCOUNT = 183,600`)
whose `init_code` immediately `REVERT`s (`0` gas spent in child) followed by a warm `STATICCALL` (`100` gas):
1. Mid-frame (`postCreateExec = 0, applyTopExit = false`): `amsterdamD0` and `amsterdamD13R` have
   `(gasLeft, stateGasLeft) = (987900, 0)`, whereas `amsterdamD13S` strands `183,600` in `stateGasLeft`
   mid-frame (`(804300, 183600)`), which is only returned at `settle_top_frame` (`applyTopExit = true` -> `(987900, 0)`)
   if the parent frame survives to top-exit without needing that gas.
2. When the parent frame requires `postCreateExec = 850000` execution gas (`850,000 ∈ (804,300, 987,900]`)
   after the `STATICCALL` (`applyTopExit = true`), `amsterdamD0` and `amsterdamD13R` succeed (`some (137900, 0)`),
   whereas `amsterdamD13S` halts mid-frame with `OutOfGasError` (`none`) before `settle_top_frame` is reached! -/
theorem t_calltree_d13s_failed_create_strands_gas :
    (run_t6_failed_create_trace .amsterdamD0 1000000 0 false).map (fun fm => (fm.meter.gasLeft, fm.meter.stateGasLeft)) =
      some (987900, 0) ∧
    (run_t6_failed_create_trace .amsterdamD13R 1000000 0 false).map (fun fm => (fm.meter.gasLeft, fm.meter.stateGasLeft)) =
      some (987900, 0) ∧
    (run_t6_failed_create_trace .amsterdamD13S 1000000 0 false).map (fun fm => (fm.meter.gasLeft, fm.meter.stateGasLeft)) =
      some (804300, 183600) ∧
    (run_t6_failed_create_trace .amsterdamD13S 1000000 0 true).map (fun fm => (fm.meter.gasLeft, fm.meter.stateGasLeft)) =
      some (987900, 0) ∧
    (run_t6_failed_create_trace .amsterdamD0 1000000 850000 true).map (fun fm => (fm.meter.gasLeft, fm.meter.stateGasLeft)) =
      some (137900, 0) ∧
    (run_t6_failed_create_trace .amsterdamD13R 1000000 850000 true).map (fun fm => (fm.meter.gasLeft, fm.meter.stateGasLeft)) =
      some (137900, 0) ∧
    run_t6_failed_create_trace .amsterdamD13S 1000000 850000 true = none := by
  decide

/-- Theorem 4d (`t_calltree_d13s_child_excess_repays_parent_spill_symbolic`):
Universal symbolic (`∀`) characterization of `amsterdamD13S` vs `amsterdamD13` on cross-frame
state-gas credits (`F-D13S-1` / `F-D13S-2` mechanism): for ANY parent frame `pWithheld` with drained
reservoir (`stateGasLeft = 0`) and `refund ≤ pWithheld.meter.stateGasSpilled`, and ANY successful
child frame `c` that entered with `stateGasBaseline = 0` and exits with `stateGasLeft = refund` and
`stateGasSpilled = 0`, `exit_child_frame .amsterdamD13S` transfers `refund` into `gasLeft`
(`pWithheld.meter.gasLeft + c.meter.gasLeft + refund`), whereas `amsterdamD13` keeps `gasLeft` at
`pWithheld.meter.gasLeft + c.meter.gasLeft`. -/
theorem t_calltree_d13s_child_excess_repays_parent_spill_symbolic
    (pWithheld c : CallFrameMeter) (refund : Nat)
    (hp_res : pWithheld.meter.stateGasLeft = 0)
    (hp_spill : refund ≤ pWithheld.meter.stateGasSpilled)
    (hc_base : c.meter.stateGasBaseline = 0)
    (hc_left : c.meter.stateGasLeft = refund)
    (hc_spill : c.meter.stateGasSpilled = 0) :
    (exit_child_frame .amsterdamD13S pWithheld c .success).meter.gasLeft =
      pWithheld.meter.gasLeft + c.meter.gasLeft + refund ∧
    (exit_child_frame .amsterdamD13S pWithheld c .success).meter.stateGasSpilled =
      pWithheld.meter.stateGasSpilled - refund ∧
    (exit_child_frame .amsterdamD13 pWithheld c .success).meter.gasLeft =
      pWithheld.meter.gasLeft + c.meter.gasLeft := by
  dsimp [exit_child_frame, repay_state_gas_spill_capped]
  rw [hp_res, hc_base, hc_left, hc_spill]
  omega

/-- Theorem 4e (`t_calltree_d13s_post_merge_refund_stranded_symbolic`):
Universal symbolic (`∀`) characterization of `amsterdamD13S` on post-merge parent-frame state-gas
refunds (`F-D13S-3` mechanism): for ANY parent frame `pAfterMerge` that receives
`frame_credit_state_refund .amsterdamD13S pAfterMerge refund` after child merge (such as
`credit_state_gas_refund` after `incorporate_child` in `generic_create`), and ANY subsequent
subcall spawned via `enter_child_frame (frame_credit_state_refund .amsterdamD13S pAfterMerge refund) childCost childGas = some (sInit, pWithheld)`
that exits cleanly at `sExit` with preserved baseline (`sExit.meter.stateGasBaseline = sInit.meter.stateGasBaseline`)
and no net state-gas gain (`sExit.meter.stateGasLeft ≤ sInit.meter.stateGasBaseline`), `childExcess = 0`,
so `exit_child_frame .amsterdamD13S pWithheld sExit .success` transfers `0` gas from `stateGasLeft`
into `gasLeft` (`gasLeft = pWithheld.meter.gasLeft + sExit.meter.gasLeft`). -/
theorem t_calltree_d13s_post_merge_refund_stranded_symbolic
    (pAfterMerge sInit pWithheld sExit : CallFrameMeter) (refund childCost childGas : Nat)
    (h_enter : enter_child_frame (frame_credit_state_refund .amsterdamD13S pAfterMerge refund) childCost childGas =
      some (sInit, pWithheld))
    (hs_base : sExit.meter.stateGasBaseline = sInit.meter.stateGasBaseline)
    (hs_no_gain : sExit.meter.stateGasLeft ≤ sInit.meter.stateGasBaseline) :
    (exit_child_frame .amsterdamD13S pWithheld sExit .success).meter.gasLeft =
      pWithheld.meter.gasLeft + sExit.meter.gasLeft ∧
    pWithheld.meter.gasLeft = pAfterMerge.meter.gasLeft - childCost ∧
    sInit.meter.stateGasBaseline = pAfterMerge.meter.stateGasLeft + refund := by
  dsimp only [enter_child_frame, frame_credit_state_refund] at h_enter
  split at h_enter
  · contradiction
  · injection h_enter with h_pair
    injection h_pair with h_sInit h_pWithheld
    subst h_sInit h_pWithheld
    dsimp only [exit_child_frame, repay_state_gas_spill_capped] at *
    omega

/-! ## 4. C-ABI Exports for Multi-Frame Differential Testing (`tests/differential/test_glamsterdam_differential.py`) -/

@[inline, export glamsterdam_calltree_m2_d0_silent_flip_cabi]
def calltree_m2_d0_silent_flip_cabi (entryGas k childNeed postWork : UInt64) : Bool :=
  let r := run_m2_set_call_clear_trace .amsterdamD0 entryGas.toNat k.toNat childNeed.toNat postWork.toNat false
  r.outerSuccess && !r.childSuccess

@[inline, export glamsterdam_calltree_m3_d0_outer_ok_cabi]
def calltree_m3_d0_outer_ok_cabi (entryGas k childExec catchWork : UInt64) : Bool :=
  (run_m3_revert_restore_trace .amsterdamD0 entryGas.toNat k.toNat childExec.toNat catchWork.toNat).outerSuccess

@[inline, export glamsterdam_calltree_m4_sibling_underflow_cabi]
def calltree_m4_sibling_underflow_cabi (schedId entryGas c2Exec : UInt64) : Bool :=
  let sched : ForkSchedule :=
    if schedId == 0 then .osaka
    else if schedId == 1 then .amsterdamD0
    else if schedId == 2 then .amsterdamD1
    else if schedId == 3 then .amsterdamD3
    else if schedId == 4 then .amsterdamD4
    else if schedId == 5 then .amsterdamD13
    else if schedId == 6 then .amsterdamD13R
    else .amsterdamD13S
  match run_m4_sibling_delta_trace sched entryGas.toNat c2Exec.toNat with
  | some out => out.underflowPanic
  | none => false

@[inline, export glamsterdam_calltree_t6_midframe_gas_cabi]
def calltree_t6_midframe_gas_cabi (schedId entryGas postCreateExec : UInt64) (applyTopExit : Bool) : UInt64 :=
  let sched : ForkSchedule :=
    if schedId == 0 then .osaka
    else if schedId == 1 then .amsterdamD0
    else if schedId == 2 then .amsterdamD1
    else if schedId == 3 then .amsterdamD3
    else if schedId == 4 then .amsterdamD4
    else if schedId == 5 then .amsterdamD13
    else if schedId == 6 then .amsterdamD13R
    else .amsterdamD13S
  match run_t6_failed_create_trace sched entryGas.toNat postCreateExec.toNat applyTopExit with
  | some fm => fm.meter.gasLeft.toUInt64
  | none => 0

end Glamsterdam.Gas.CallTree
