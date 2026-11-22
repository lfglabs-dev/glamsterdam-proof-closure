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

/--
**SSTORE 2,300-gas sentry excludes the state-gas reservoir (T-CALLTREE-SSTORE-SENTRY-EXCLUDES-RESERVOIR)**
- *Natural property:* Whenever a frame's execution `gasLeft` is at or below the `2,300` call stipend (`GAS_SSTORE_SENTRY`), `SSTORE` halts with `OutOfGasError` regardless of fork schedule or how much state gas sits in `stateGasLeft`.
- *Formal statement:* `fm.meter.gasLeft ≤ GAS_SSTORE_SENTRY → exec_sstore_frame sched fm isCold origVal currVal newVal = none`.
- *Scope note:* Single-step `exec_sstore_frame` across all eight `ForkSchedule` variants (`osaka`, `D0..D13S`), matching `src/ethereum/forks/amsterdam/vm/instructions/storage.py:100-105`.
-/
theorem t_calltree_sstore_sentry_excludes_reservoir
    (sched : ForkSchedule) (fm : CallFrameMeter) (isCold : Bool) (origVal currVal newVal : Nat)
    (h_sentry : fm.meter.gasLeft ≤ GAS_SSTORE_SENTRY) :
    exec_sstore_frame sched fm isCold origVal currVal newVal = none := by
  unfold exec_sstore_frame
  simp [h_sentry]

/--
**Single-frame upper bound on gasLeft + stateGasSpilled (T-CALLTREE-A1-FRAME-BOUND)**
- *Natural property:* Within a single frame under normative Amsterdam (`D0`), execution charges and state charges never increase `gasLeft + stateGasSpilled`, and LIFO state-gas refills preserve `gasLeft + stateGasSpilled` exactly.
- *Formal statement:* `post.gasLeft + post.stateGasSpilled ≤ m.gasLeft + m.stateGasSpilled` across `charge_gas_from_meter` and `charge_state_gas_from_meter`, and `(credit_state_gas_refund m amount).gasLeft + (credit_state_gas_refund m amount).stateGasSpilled = m.gasLeft + m.stateGasSpilled`.
- *Scope note:* Intra-frame `GasMeter` transitions (`src/ethereum/forks/amsterdam/vm/gas.py:379-616`); cross-frame child merges can still increase parent `gasLeft` as proved in `t_calltree_e3_m4_sibling_underflow_and_d13s_break`.
-/
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

/--
**Fixed 50,000-gas child starvation on fresh SSTORE when reservoir is empty (T-CALLTREE-E1-FIXED-GRANT-STARVATION)**
- *Natural property:* With an empty reservoir (`tx.gas ≤ 2^24`), a `50,000`-gas child frame writing one warm fresh storage slot (`0 -> 1`) succeeds under Osaka (`20,100` gas) but runs out of gas (`108,020` needed) under every Amsterdam refill variant (`D0` through `D13S`).
- *Formal statement:* On `childInit := { meter := { gasLeft := 50000, stateGasLeft := 0, stateGasBaseline := 0 } }`, `(exec_sstore_frame .osaka childInit false 0 0 1).isSome = true` while `exec_sstore_frame sched childInit false 0 0 1 = none` for `D0, D1, D3, D4, D13, D13R, D13S`.
- *Scope note:* Multi-schedule single-frame check at `stateGasLeft = 0` (`INV-4` fixed-budget pattern); `#12582` (`D13A`) with a non-empty reservoir is modeled in `Glamsterdam.Gas.Eip12582`.
-/
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

/--
**Set-call-clear silent child failure across Osaka, D0, D1/D13, and D13R (T-CALLTREE-E3-M2-DIRTY-CLEAR-AND-D13R-BREAK)**
- *Natural property:* When a parent sets `3` fresh slots before `CALL(63/64)` and clears them afterward (`M2`/`T2`), `D0` starves the child yet refills `gasLeft` on clear so the parent finishes (`outerSuccess = true, childSuccess = false`); reservoir-only refills (`D1`, `D13`) close that silent-failure band, whereas `D13R` re-opens it whenever a post-clear subcall (`flushCall = true`) flushes the reservoir.
- *Formal statement:* At `(550000, 3, 240000, 50000)`, `run_m2_set_call_clear_trace` returns `(true, true)` on `osaka`, `(true, false)` on `amsterdamD0`, `(false, false)` on `D1`, `D13`, and `D13R` without flush, and `(true, false)` on `D13R` with flush.
- *Scope note:* Abstract two-frame `run_m2_set_call_clear_trace` trace at `stateGasLeft = 0`.
-/
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

/--
**Pre-call set-and-clear silent child failure under D13R (T-CALLTREE-D13R-NEW-T1-BAND)**
- *Natural property:* If a parent sets and clears a fresh slot (`0 -> 1 -> 0`) before `CALL(63/64)`, `D0` restores `97,920` to `gasLeft` before the call so both child and parent succeed, whereas `D13R` holds the refill in `stateGasLeft` across the call (starving the child) and flushes it into `gasLeft` upon the failed child's exit so the parent succeeds.
- *Formal statement:* On `run_t1_pre_call_set_clear_trace _ 170000 100000 50000`, `amsterdamD0` returns `(true, true)`, `amsterdamD13R` returns `(true, false)`, and `amsterdamD13S` returns `(false, false)`.
- *Scope note:* Abstract two-frame `T1` comparison trace across refill variants (`D0`, `D13R`, `D13S`).
-/
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

/--
**Revert-restore catch-block funding across D0/D1/D4 vs. deferred-spill D3/D13/D13R/D13S (T-CALLTREE-E3-M3-REVERT-RESTORE-BAND)**
- *Natural property:* When a child writes `3` fresh slots (`293,760` spilled state gas) and `REVERT`s, `D0`, `D1`, and `D4` return the spilled gas to `parent.gasLeft` (funding a `50,000`-gas `catch` block), whereas `D3`, `D13`, `D13R`, and `D13S` defer the reverted child's spill to transaction settlement so the `catch` block runs out of gas.
- *Formal statement:* At `(400000, 3, 60000, 50000)`, `run_m3_revert_restore_trace` returns `⟨true, false, 259700, 0⟩` on `D0, D1, D4` and `⟨false, false, 15940, 0⟩` on `D3, D13, D13R, D13S`.
- *Scope note:* Abstract two-frame `M3` revert-catch trace at `stateGasLeft = 0`.
-/
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

/--
**Cross-sibling gasleft() rise and D13S regression on sibling clear (T-CALLTREE-E3-M4-SIBLING-AND-D13S-BREAK)**
- *Natural property:* If Child 1 writes `0 -> 1` (leaving parent `stateGasSpilled = 97,920`) and sibling Child 2 clears `1 -> 0` while spending `20,000` execution gas, parent `gasLeft` after Child 2 (`g2 = 469,800`) exceeds parent `gasLeft` before Child 2 (`g1 = 391,980`) under `D0`, `D3`, `D13R`, and `D13S`, causing `g1 - g2` gas-delta checks to underflow.
- *Formal statement:* On `run_m4_sibling_delta_trace _ 500000 20000`, `underflowPanic = false` (`g2 ≤ g1`) for `osaka, D1, D4, D13`, and `underflowPanic = true` (`g2 > g1`) for `D0, D3, D13R, D13S`.
- *Scope note:* Three-frame (`Parent -> Child 1, Child 2`) `M4` regression trace; first of the three `D13S` comparison regressions.
-/
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

/--
**D13S regression: clearing slots in a helper subcall re-opens silent child failure (T-CALLTREE-D13S-REOPENS-T2-CHILD-CLEAR)**
- *Natural property:* Under `D13S`, if a parent clears `3` previously set slots inside a helper subcall after the main child call OOGs, the helper exits with positive `childExcess = 293,760` and flushes that credit into `parent.gasLeft`, re-opening the `outerSuccess = true, childSuccess = false` silent-failure band that `D1` and `D13` close.
- *Formal statement:* On `run_t2_child_clear_trace _ 550000 3 240000 50000`, `D1` and `D13` return `(false, false)` while `D13S` returns `(true, false)`.
- *Scope note:* Three-frame (`Parent -> Child, Helper`) `T2_child_clear` regression trace; second of the three `D13S` comparison regressions.
-/
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

/--
**D13S regression: failed CREATE strands 183,600 execution gas mid-frame (T-CALLTREE-D13S-FAILED-CREATE-STRANDS-GAS)**
- *Natural property:* Because `generic_create` credits `183,600` `NEW_ACCOUNT` state gas back to the parent *after* `incorporate_child`, `D13S` parks that `183,600` in `stateGasLeft` alongside `stateGasSpilled = 183,600`; even a subsequent `STATICCALL` has `childExcess = 0` and cannot flush it, starving `850,000`-gas mid-frame parent work that succeeds under `D0` and `D13R`.
- *Formal statement:* On `run_t6_failed_create_trace`, mid-frame `(gasLeft, stateGasLeft)` is `(987900, 0)` on `D0` and `D13R` vs `(804300, 183600)` on `D13S`, and with `postCreateExec = 850000`, `D0` and `D13R` finish at `some (137900, 0)` while `D13S` returns `none`.
- *Scope note:* Gas-schedule projection of `generic_create` (`src/ethereum/forks/amsterdam/vm/instructions/system.py:107-180`); third of the three `D13S` comparison regressions.
-/
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

/--
**Symbolic characterization of cross-frame spill repayment under D13S vs. D13**
- *Natural property:* Whenever a parent frame has `stateGasLeft = 0` and `refund ≤ stateGasSpilled`, and a successful child enters with `stateGasBaseline = 0` and exits with `stateGasLeft = refund`, `D13S` flushes `refund` into `parent.gasLeft`, whereas `D13` keeps `gasLeft` at `pWithheld.gasLeft + c.gasLeft`.
- *Formal statement:* Under those hypotheses, `(exit_child_frame .amsterdamD13S pWithheld c .success).meter.gasLeft = pWithheld.meter.gasLeft + c.meter.gasLeft + refund`, whereas `(exit_child_frame .amsterdamD13 pWithheld c .success).meter.gasLeft = pWithheld.meter.gasLeft + c.meter.gasLeft`.
- *Scope note:* Universal symbolic mechanism underlying `t_calltree_e3_m4_sibling_underflow_and_d13s_break` and `t_calltree_d13s_reopens_t2_on_child_clear`.
-/
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

/--
**Symbolic characterization of stranded post-merge parent refunds under D13S**
- *Natural property:* Under `D13S`, a state-gas refund credited to a parent *after* child merge raises `sInit.stateGasBaseline` on every subsequent subcall, so any subcall exiting without net state-gas gain has `childExcess = 0` and transfers `0` gas from `stateGasLeft` back to `gasLeft`.
- *Formal statement:* Given `enter_child_frame (frame_credit_state_refund .amsterdamD13S pAfterMerge refund) childCost childGas = some (sInit, pWithheld)` and `sExit.meter.stateGasLeft ≤ sInit.meter.stateGasBaseline`, `(exit_child_frame .amsterdamD13S pWithheld sExit .success).meter.gasLeft = pWithheld.meter.gasLeft + sExit.meter.gasLeft`.
- *Scope note:* Universal symbolic mechanism underlying `t_calltree_d13s_failed_create_strands_gas`.
-/
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

/--
**Spill-invariant preservation on child merge under D0/D13R vs. violation under D13S**
- *Natural property:* Successful child merges under `D0` and `D13R` unconditionally establish `GasMeter.SpillInvariant` (`stateGasLeft = 0 ∨ stateGasSpilled = 0`), whereas `D13S` capped repayment leaves `stateGasLeft = 183,600` and `stateGasSpilled = 183,600` simultaneously after a failed `CREATE` and subsequent `STATICCALL`.
- *Formal statement:* `(exit_child_frame .amsterdamD0 pWithheld c .success).meter.SpillInvariant ∧ (exit_child_frame .amsterdamD13R pWithheld c .success).meter.SpillInvariant` while `run_t6_failed_create_trace .amsterdamD13S 1000000 0 false` yields `(stateGasLeft, stateGasSpilled) = (183600, 183600)`.
- *Scope note:* Relates `GasMeter.SpillInvariant` across `D0`, `D13R`, and `D13S` multi-frame exits.
-/
theorem t_calltree_d0_preserves_spill_invariant_and_d13s_violates
    (pWithheld c : CallFrameMeter) :
    (exit_child_frame .amsterdamD0 pWithheld c .success).meter.SpillInvariant ∧
    (exit_child_frame .amsterdamD13R pWithheld c .success).meter.SpillInvariant ∧
    (run_t6_failed_create_trace .amsterdamD13S 1000000 0 false).map
      (fun fm => (fm.meter.stateGasLeft, fm.meter.stateGasSpilled)) = some (183600, 183600) := by
  refine ⟨?_, ?_, by decide⟩
  · dsimp only [exit_child_frame]
    exact (repay_state_gas_spill_invariant _).2
  · dsimp only [exit_child_frame]
    exact (repay_state_gas_spill_invariant _).2

/-- Same-child `0 -> 1 -> 0` trace (`0x7cfb8909` pattern from `fradamt/8037-coordination#70`):
A child frame enters with `gasLeft = childEntryGas` and `stateGasLeft = 0` (`tx.gas ≤ 2^24`),
writes one warm slot `0 -> 1` (`10,100` execution gas + `97,920` state gas), and clears that
same slot `1 -> 0` (`100` execution gas, crediting `97,920` state gas) within the same child frame. -/
def run_same_child_set_clear_trace (sched : ForkSchedule) (childEntryGas : Nat) : Option CallFrameMeter :=
  let c0 : CallFrameMeter := { meter := { gasLeft := childEntryGas, stateGasLeft := 0, stateGasBaseline := 0 } }
  match exec_sstore_frame sched c0 false 0 0 1 with
  | none => none
  | some c1 => exec_sstore_frame sched c1 false 0 1 0

/--
**Same-frame 0 -> 1 -> 0 refill tradeoff between D0 and EIPs#12581 (D13)**
- *Natural property:* Within a `200,000`-gas frame starting with an empty reservoir, setting and clearing a warm fresh slot (`0 -> 1 -> 0`) restores `97,920` directly to `gasLeft` under `D0` (`gasLeft = 189,800`), whereas reservoir-only refills under `D13` (`EIPs#12581`) credit `stateGasLeft` (`gasLeft = 91,880, stateGasLeft = 97,920`).
- *Formal statement:* `run_same_child_set_clear_trace .amsterdamD0 200000` yields `(189800, 0, 0)` on `(gasLeft, stateGasLeft, stateGasSpilled)`, while `.amsterdamD13` yields `(91880, 97920, 97920)`.
- *Scope note:* Single-frame `SSTORE` set-and-clear trace comparing `D0` against `D13` (pre-legacy-share `#12581` Option C reservoir mechanics).
-/
theorem t_calltree_eip12581_same_child_clear_tradeoff :
    (run_same_child_set_clear_trace .amsterdamD0 200000).map
      (fun fm => (fm.meter.gasLeft, fm.meter.stateGasLeft, fm.meter.stateGasSpilled)) =
        some (189800, 0, 0) ∧
    (run_same_child_set_clear_trace .amsterdamD13 200000).map
      (fun fm => (fm.meter.gasLeft, fm.meter.stateGasLeft, fm.meter.stateGasSpilled)) =
        some (91880, 97920, 97920) := by
  decide

/--
**Correspondence of ForkSchedule.amsterdamD13 with EIPs#12581 reservoir-only transitions**
- *Natural property:* Under `amsterdamD13`, state-gas refills credit only `stateGasLeft`, successful child exits merge `gasLeft` and `stateGasLeft` without spill repayment, and reverting or halting child exits restore `stateGasLeft` to its entry snapshot without returning spilled gas to `gasLeft`.
- *Formal statement:* `refilled.meter = (fm.gasLeft, fm.stateGasLeft + amount, fm.stateGasSpilled)`, `onSucc.meter = (p + c)` without `repay_state_gas_spill`, and `onRev`/`onHalt` restore `pWithheld.stateGasLeft + c.stateGasBaseline`.
- *Scope note:* Transition-level equivalence for `(gasLeft, stateGasLeft)` with `ethereum/EIPs#12581` Option C (`b86de3f4`); `#12581` with `legacy_share` and `#12582` allowances are formalized in `Glamsterdam.Gas.Eip12582`.
-/
theorem t_calltree_d13_eq_eip12581_on_gas_and_reservoir
    (fm pWithheld c : CallFrameMeter) (amount : Nat) :
    let refilled := frame_credit_state_refund .amsterdamD13 fm amount
    let onSucc := exit_child_frame .amsterdamD13 pWithheld c .success
    let onRev := exit_child_frame .amsterdamD13 pWithheld c .revert
    let onHalt := exit_child_frame .amsterdamD13 pWithheld c .halt
    (refilled.meter.gasLeft = fm.meter.gasLeft ∧
      refilled.meter.stateGasLeft = fm.meter.stateGasLeft + amount ∧
      refilled.meter.stateGasSpilled = fm.meter.stateGasSpilled) ∧
    (onSucc.meter.gasLeft = pWithheld.meter.gasLeft + c.meter.gasLeft ∧
      onSucc.meter.stateGasLeft = pWithheld.meter.stateGasLeft + c.meter.stateGasLeft ∧
      onSucc.meter.stateGasSpilled = pWithheld.meter.stateGasSpilled + c.meter.stateGasSpilled) ∧
    (onRev.meter.gasLeft = pWithheld.meter.gasLeft + c.meter.gasLeft ∧
      onRev.meter.stateGasLeft = pWithheld.meter.stateGasLeft + c.meter.stateGasBaseline) ∧
    (onHalt.meter.gasLeft = pWithheld.meter.gasLeft ∧
      onHalt.meter.stateGasLeft = pWithheld.meter.stateGasLeft + c.meter.stateGasBaseline) := by
  dsimp [frame_credit_state_refund, exit_child_frame, incorporate_child_meter,
    forfeit_remaining_gas, restore_state_gas]
  refine ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨by omega, rfl⟩⟩

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

/-! ## 5. Dynamic EIP-8038 Warm-Set Tracking & Child-Revert Rollback (`vm/instructions/storage.py:37-66`) -/

/-- `CallFrameMeter` paired with dynamic EIP-2929 / EIP-8038 warm storage keys and addresses. -/
structure WarmCallFrame where
  fm : CallFrameMeter
  warmSlots : List StorageKey := []
  warmAddrs : List Address := []
  deriving Repr, DecidableEq, BEq

/-- Dynamic `SLOAD` charging `GAS_COLD_STORAGE_ACCESS` (`2,100`) on first access and
`GAS_WARM_ACCESS` (`100`) on subsequent accesses in the same frame, adding `key` to `warmSlots`. -/
def exec_sload_warm (wf : WarmCallFrame) (key : StorageKey) : Option WarmCallFrame :=
  let isCold := !(wf.warmSlots.contains key)
  let cost := if isCold then GAS_COLD_STORAGE_ACCESS else GAS_WARM_ACCESS
  match frame_charge_exec wf.fm cost with
  | none => none
  | some fm' =>
    let newWarm := if isCold then key :: wf.warmSlots else wf.warmSlots
    some { wf with fm := fm', warmSlots := newWarm }

/-- Merge a returning child `WarmCallFrame` into its parent:
- On `.success`, adopts `child.warmSlots` and `child.warmAddrs`.
- On `.revert` or `.halt`, rolls back the warm sets to `parentWithheld` (matching `restore_tx_state`). -/
def exit_child_warm (sched : ForkSchedule) (parentWithheld child : WarmCallFrame)
    (status : ChildStatus) : WarmCallFrame :=
  let mergedFm := exit_child_frame sched parentWithheld.fm child.fm status
  match status with
  | .success =>
    { fm := mergedFm, warmSlots := child.warmSlots, warmAddrs := child.warmAddrs }
  | .revert | .halt =>
    { fm := mergedFm, warmSlots := parentWithheld.warmSlots, warmAddrs := parentWithheld.warmAddrs }

/--
**Dynamic EIP-8038 warm/cold `SLOAD` pricing and revert isolation (T-8038-WARM-COLD-DYNAMIC)**
- *Natural property:* Reading a cold storage key twice in the same frame pays `GAS_COLD_STORAGE_ACCESS` (`2,100`) on the first `SLOAD` and `GAS_WARM_ACCESS` (`100`) on the second (`2,200 < 2 × 2,100`). If a child frame warms that key and reverts or halts, the key stays cold in the parent frame and the parent still pays `2,100`.
- *Formal statement:* When `key ∉ wf.warmSlots` and `wf.fm.meter.gasLeft ≥ 2200`, two consecutive `exec_sload_warm` calls succeed and reduce `gasLeft` by `2,200` (`2,100 + 100`). For any `status ∈ {.revert, .halt}`, `exit_child_warm sched parent childWarmed status` preserves `key ∉ warmSlots`, so the parent's subsequent `exec_sload_warm` charges `2,100`.
- *Scope note:* Dynamic `warmSlots` tracking over `CallFrameMeter` (`vm/instructions/storage.py:37-66`, `vm/__init__.py:188-245`).
-/
theorem t_8038_warm_cold_dynamic_and_revert_isolation
    (sched : ForkSchedule) (wf : WarmCallFrame) (key : StorageKey)
    (h_cold : wf.warmSlots.contains key = false)
    (h_gas : wf.fm.meter.gasLeft ≥ GAS_COLD_STORAGE_ACCESS + GAS_WARM_ACCESS) :
    (∃ wf1 wf2,
      exec_sload_warm wf key = some wf1 ∧
      exec_sload_warm wf1 key = some wf2 ∧
      wf1.fm.meter.gasLeft = wf.fm.meter.gasLeft - GAS_COLD_STORAGE_ACCESS ∧
      wf2.fm.meter.gasLeft = wf.fm.meter.gasLeft - (GAS_COLD_STORAGE_ACCESS + GAS_WARM_ACCESS) ∧
      wf2.warmSlots.contains key = true) ∧
    (∀ (childWarmed : WarmCallFrame) (status : ChildStatus),
      (status = .revert ∨ status = .halt) →
      let parentPost := exit_child_warm sched wf childWarmed status
      parentPost.warmSlots.contains key = false ∧
      (parentPost.fm.meter.gasLeft ≥ GAS_COLD_STORAGE_ACCESS →
        ∃ pAfter,
          exec_sload_warm parentPost key = some pAfter ∧
          pAfter.fm.meter.gasLeft = parentPost.fm.meter.gasLeft - GAS_COLD_STORAGE_ACCESS)) := by
  constructor
  · have h_ge1 : ¬ (wf.fm.meter.gasLeft < GAS_COLD_STORAGE_ACCESS) := by
      dsimp [GAS_COLD_STORAGE_ACCESS, GAS_WARM_ACCESS] at *; omega
    have h_ge2 : ¬ (wf.fm.meter.gasLeft - GAS_COLD_STORAGE_ACCESS < GAS_WARM_ACCESS) := by
      dsimp [GAS_COLD_STORAGE_ACCESS, GAS_WARM_ACCESS] at *; omega
    refine ⟨
      { wf with
        fm := { wf.fm with meter := { wf.fm.meter with gasLeft := wf.fm.meter.gasLeft - GAS_COLD_STORAGE_ACCESS } }
        warmSlots := key :: wf.warmSlots },
      { wf with
        fm := { wf.fm with meter := { wf.fm.meter with gasLeft := wf.fm.meter.gasLeft - GAS_COLD_STORAGE_ACCESS - GAS_WARM_ACCESS } }
        warmSlots := key :: wf.warmSlots },
      ?_, ?_, rfl, by dsimp only; omega, by simp⟩
    · simp only [exec_sload_warm, frame_charge_exec, charge_gas_from_meter,
        h_cold, Bool.not_false, ↓reduceIte, h_ge1]
    · simp only [exec_sload_warm, frame_charge_exec, charge_gas_from_meter,
        List.contains_cons, beq_self_eq_true, Bool.true_or, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte, h_ge2]
  · intro childWarmed status h_fail
    have h_post :
        exit_child_warm sched wf childWarmed status =
          { fm := exit_child_frame sched wf.fm childWarmed.fm status
            warmSlots := wf.warmSlots
            warmAddrs := wf.warmAddrs } := by
      rcases h_fail with rfl | rfl <;> rfl
    rw [h_post]
    refine ⟨h_cold, fun h_pg => ?_⟩
    have h_not_lt :
        ¬ ((exit_child_frame sched wf.fm childWarmed.fm status).meter.gasLeft < GAS_COLD_STORAGE_ACCESS) := by
      dsimp only at h_pg; omega
    refine ⟨
      { fm := { (exit_child_frame sched wf.fm childWarmed.fm status) with
                meter := { (exit_child_frame sched wf.fm childWarmed.fm status).meter with
                           gasLeft := (exit_child_frame sched wf.fm childWarmed.fm status).meter.gasLeft - GAS_COLD_STORAGE_ACCESS } }
        warmSlots := key :: wf.warmSlots
        warmAddrs := wf.warmAddrs },
      ?_, rfl⟩
    simp only [exec_sload_warm, frame_charge_exec, charge_gas_from_meter,
      h_cold, Bool.not_false, ↓reduceIte, h_not_lt]

end Glamsterdam.Gas.CallTree
