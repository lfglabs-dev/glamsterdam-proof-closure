/-
Copyright (c) 2026 Verity Labs / LFG Labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Marchand, Verity Audit Team
-/
import Glamsterdam.Common.ElCore
import Glamsterdam.Gas.Spec
import Glamsterdam.Gas.CallTree

/-!
# Formal Model & Verification of `ethereum/EIPs#12582` (`D13A` Per-Frame State-Gas Allowance)
vs `ethereum/EIPs#12581` (`D13R`) and Nethermind Prototypes (`#15186`, `#15187`, `#15203`)

This module formalizes the normative state-gas meter and call-frame transition rules of:
- **`D13R` (`ethereum/EIPs#12581` / `NethermindEth/nethermind#15186`)**:
  Reservoir-only state-gas refills and rollbacks, plus the per-component `legacy_share`
  (`SSTORE` new slot = `10,000`, `NEW_ACCOUNT` = `25,000`, `CREATE` account creation = `20,000`,
  code deposit = `0`), with no per-frame reservoir draw limit.
- **`D13A` (`ethereum/EIPs#12582` normative @ `19d788c896`)**:
  Extends `D13R` with `LEGACY_GAS_PER_STATE_BYTE = 200`, transaction-wide `state_gas_drawn`,
  frame-local `state_gas_drawn_snapshot`, and `state_gas_ceiling : Option Nat`:
  - `none` at the top-level frame,
  - inherited (`child.state_gas_ceiling = parent.state_gas_ceiling`) on `DELEGATECALL` and `CALLCODE`,
  - `min(parent.state_gas_ceiling, state_gas_drawn + child_gas * CPSB // 200)` on `CALL`, `STATICCALL`,
    `CREATE`, and `CREATE2`.
- **`D13A_Nethermind15187` (`NethermindEth/nethermind#15187` @ `76ce18c734`)**:
  Models Nethermind's prototype `EthereumGasPolicy.CreateChildFrameGas`, which applies
  `min(parent.ceiling, state_gas_drawn + child_gas * CPSB // 200)` to **all** call frames including
  `DELEGATECALL` and `CALLCODE`, plus `TryConsumeCodeDepositGas` and `RevertRefundToHalt`.

We machine-check the 4 core properties requested for Lukasz Rozmej, Maria Inês Silva, and
Francesco D'Amato, together with executable differential witnesses for Nethermind `#15186`,
`#15187`, and `#15203`:
1. **Property 1 (`DELEGATECALL` Frame-Invariance & Nethermind `#15187` Proxy Divergence)**:
   `t_12582_prop1_delegatecall_frame_invariance` and
   `t_12582_prop1b_nethermind15187_proxied_factory_divergence`.
2. **Property 2 (`gas_left` Non-Increasing Within Frame & Across Calls / No `T2` Bug)**:
   `t_12582_prop2_gas_left_non_increasing_in_frame` and
   `t_12582_prop2b_child_exit_bounded_by_child_gas_left`.
3. **Property 3 (Untrusted Callee Reservoir Drain Bound `Δ state_gas_drawn ≤ ⌊g × CPSB / 200⌋`)**:
   `t_12582_prop3_subcall_ceiling_bounded` and
   `t_12582_prop3b_untrusted_callee_reservoir_drain_bound`.
4. **Property 4 (Asymmetry of `revert` vs `SSTORE 1 -> 0` on `state_gas_drawn`, Clean-Trace
   Monotonicity, `#15203` `avoidNestedOutOfGas`, and `#15187`'s 6 Regression Cases)**:
   `t_12582_prop4_revert_vs_refill_drawn_asymmetry`,
   `t_12582_prop4b_clean_trace_single_charge_monotone`, and
   `t_12582_prop4c_nethermind_15187_six_regression_cases`.
-/

namespace Glamsterdam.Gas.Eip12582

open Glamsterdam.Common.Prelude
open Glamsterdam.Common.MetaSpec
open Glamsterdam.Common.ElCore
open Glamsterdam.Gas.Spec
open Glamsterdam.Gas.CallTree

/-! ## 1. Normative `#12581` / `#12582` Constants & Legacy Share Formula -/

/-- `LEGACY_GAS_PER_STATE_BYTE = 200` (`EIPS/eip-8037.md:41` in `ethereum/EIPs#12582`,
`Eip8037Constants.LegacyGasPerStateByte = 200` in `NethermindEth/nethermind#15187`). -/
@[inline] def LEGACY_GAS_PER_STATE_BYTE : Nat := 200

/-- Frozen pre-fork cost constants (`EIPS/eip-8037.md:42-44` in `ethereum/EIPs#12581` / `#12582`). -/
@[inline] def PRE_FORK_GAS_STORAGE_SET : Nat := 20000
@[inline] def PRE_FORK_GAS_NEW_ACCOUNT : Nat := 25000
@[inline] def PRE_FORK_GAS_CREATE : Nat := 32000

/-- Normative legacy share formula (`EIPS/eip-8037.md:85`):
`legacy_share = min(state_gas_charge, max(0, PRE_FORK_COST - execution_gas_charge))`. -/
@[simp]
def compute_legacy_share (stateGasCharge preForkCost execGasCharge : Nat) : Nat :=
  min stateGasCharge (preForkCost - execGasCharge)

/-- Derived legacy shares at the current EIP-8037 / EIP-8038 schedule (`CPSB = 1530`,
`STORAGE_WRITE = 10,000`, `CREATE_ACCESS = 12,000`):
- New storage slot (`SSTORE`): `10,000`
- New account (`CALL*` with value, `SELFDESTRUCT`): `25,000`
- Account creation of `CREATE`/`CREATE2`: `20,000`
- Code deposit (`L * CPSB`): `0`. -/
@[inline] def LEGACY_SHARE_STORAGE_SET : Nat :=
  compute_legacy_share STATE_GAS_STORAGE_SET PRE_FORK_GAS_STORAGE_SET GAS_STORAGE_WRITE

@[inline] def LEGACY_SHARE_NEW_ACCOUNT : Nat :=
  compute_legacy_share STATE_GAS_NEW_ACCOUNT PRE_FORK_GAS_NEW_ACCOUNT 0

@[inline] def LEGACY_SHARE_CREATE : Nat :=
  compute_legacy_share STATE_GAS_NEW_ACCOUNT PRE_FORK_GAS_CREATE Spec.GAS_CREATE_ACCESS

theorem t_12582_legacy_share_values :
    LEGACY_SHARE_STORAGE_SET = 10000 ∧
    LEGACY_SHARE_NEW_ACCOUNT = 25000 ∧
    LEGACY_SHARE_CREATE = 20000 := by
  decide

/-- Allowance derived from `childGas` execution gas forwarded to a call frame
(`child_gas * CPSB // LEGACY_GAS_PER_STATE_BYTE`, `EIPS/eip-8037.md:211`). -/
@[simp]
def allowance_from_gas (childGas : Nat) : Nat :=
  childGas * COST_PER_STATE_BYTE / LEGACY_GAS_PER_STATE_BYTE

/-- Call-frame opcode kind distinguishing frame-Boundary calls (`CALL`, `STATICCALL`, `CREATE`, `CREATE2`)
from context-preserving calls (`DELEGATECALL`, `CALLCODE`). -/
inductive CallFrameKind where
  | call
  | staticcall
  | delegatecall
  | callcode
  | create
  | create2
  deriving Repr, DecidableEq, BEq

/-- Whether `kind` inherits its parent's `state_gas_ceiling` under normative `ethereum/EIPs#12582`
(`EIPS/eip-8037.md:214`). -/
@[simp]
def CallFrameKind.inheritsCeiling : CallFrameKind → Bool
  | .delegatecall | .callcode => true
  | .call | .staticcall | .create | .create2 => false

/-- Ceiling-derivation mode:
- `d13r_unlimited`: `#12581` (`D13R`), no per-frame ceiling (`none` at all depths).
- `d13a_normative`: `#12582`, top-level `none`, `DELEGATECALL`/`CALLCODE` inherit `parent.ceiling`,
  and `CALL`/`STATICCALL`/`CREATE`/`CREATE2` cap at `drawn + childGas * CPSB // 200`.
- `d13a_nethermind15187`: `NethermindEth/nethermind#15187` (`76ce18c734`), where `CreateChildFrameGas`
  caps `DELEGATECALL` and `CALLCODE` by `drawn + childGas * CPSB // 200` as well. -/
inductive AllowanceMode where
  | d13r_unlimited
  | d13a_normative
  | d13a_nethermind15187
  deriving Repr, DecidableEq, BEq

/-! ## 2. Extended `#12582` Frame Meter (`D13AMeter`) & Core Operations -/

/-- Extended gas meter state for `#12581` (`D13R`) and `#12582` (`D13A`)
(`EIPS/eip-8037.md:57-64, 198-206`):
- `gasLeft`: execution gas remaining in the current frame (`gas_left`).
- `stateGasReservoir`: transaction-wide state-gas reservoir (`state_gas_reservoir`).
- `evmStateGasUsed`: transaction-wide net state gas used (`evm_state_gas_used : Int`).
- `stateGasDrawn`: transaction-wide state gas drawn from `state_gas_reservoir` (`state_gas_drawn`).
- `reservoirSnapshot`: frame-entry snapshot of `stateGasReservoir` (`state_gas_reservoir_snapshot`).
- `usedSnapshot`: frame-entry snapshot of `evmStateGasUsed` (`state_gas_used_snapshot`).
- `drawnSnapshot`: frame-entry snapshot of `stateGasDrawn` (`state_gas_drawn_snapshot`).
- `stateGasCeiling`: optional upper bound on `stateGasDrawn` (`none` at top-level or under `#12581`). -/
structure D13AMeter where
  gasLeft : Nat
  stateGasReservoir : Nat
  evmStateGasUsed : Int := 0
  stateGasDrawn : Nat := 0
  reservoirSnapshot : Nat := 0
  usedSnapshot : Int := 0
  drawnSnapshot : Nat := 0
  stateGasCeiling : Option Nat := none
  deriving Repr, DecidableEq, BEq

/-- Initialize a top-level `D13AMeter` after intrinsic gas deduction (`state_gas_ceiling = none`). -/
@[simp]
def init_top_meter (gasLeft reservoir : Nat) : D13AMeter :=
  { gasLeft := gasLeft
    stateGasReservoir := reservoir
    evmStateGasUsed := 0
    stateGasDrawn := 0
    reservoirSnapshot := reservoir
    usedSnapshot := 0
    drawnSnapshot := 0
    stateGasCeiling := none }

/-- Remaining reservoir draw allowance in `m` (`none` if `m.stateGasCeiling = none`,
or `some (ceiling - stateGasDrawn)` if `m.stateGasCeiling = some ceiling`). -/
@[simp]
def remaining_allowance (m : D13AMeter) : Option Nat :=
  match m.stateGasCeiling with
  | none => none
  | some ceiling => some (ceiling - m.stateGasDrawn)

/-- Cap a reservoir draw ` maxReservoir` by an optional ceiling `ceilingOpt` given `stateGasDrawn`. -/
@[simp]
def cap_by_ceiling (maxReservoir stateGasDrawn : Nat) (ceilingOpt : Option Nat) : Nat :=
  match ceilingOpt with
  | none => maxReservoir
  | some ceiling => min maxReservoir (ceiling - stateGasDrawn)

/-- Combine a parent's optional ceiling with a new child ceiling `newBound`. -/
@[simp]
def min_ceiling (parentCeiling : Option Nat) (newBound : Nat) : Option Nat :=
  match parentCeiling with
  | none => some newBound
  | some pCeil => some (min pCeil newBound)

/-- Derive the child frame's `state_gas_ceiling` upon spawning a child of `kind` with `childGas`
execution gas (`EIPS/eip-8037.md:206-215`):
- Under `.d13r_unlimited`: always `none`.
- Under `.d13a_normative`: if `kind.inheritsCeiling` (`DELEGATECALL`/`CALLCODE`), inherits
  `parent.stateGasCeiling`; otherwise `min_ceiling parent.stateGasCeiling (parent.stateGasDrawn + allowance_from_gas childGas)`.
- Under `.d13a_nethermind15187`: always `min_ceiling parent.stateGasCeiling (parent.stateGasDrawn + allowance_from_gas childGas)`. -/
@[simp]
def derive_child_ceiling (mode : AllowanceMode) (kind : CallFrameKind)
    (parent : D13AMeter) (childGas : Nat) : Option Nat :=
  match mode with
  | .d13r_unlimited => none
  | .d13a_normative =>
    if kind.inheritsCeiling then
      parent.stateGasCeiling
    else
      min_ceiling parent.stateGasCeiling (parent.stateGasDrawn + allowance_from_gas childGas)
  | .d13a_nethermind15187 =>
    min_ceiling parent.stateGasCeiling (parent.stateGasDrawn + allowance_from_gas childGas)

/-- Charge execution gas (`EIPS/eip-8037.md:67`). -/
@[simp]
def charge_exec_d13a (m : D13AMeter) (amount : Nat) : Option D13AMeter :=
  if m.gasLeft < amount then
    none
  else
    some { m with gasLeft := m.gasLeft - amount }

/-- Charge state gas with a given `legacyShare` and an optional explicit ceiling override
(`EIPS/eip-8037.md:71, 215-227` and `EthereumGasPolicy.TryConsumeStateGas` in `#15187`):
1. `leg = min amount legacyShare` is paid from `gasLeft`.
2. `rest = amount - leg`.
3. `fromReservoir = min(rest, stateGasReservoir, ceiling - stateGasDrawn)`.
4. `fromGasLeft = leg + (rest - fromReservoir) = amount - fromReservoir`.
5. If `gasLeft < fromGasLeft`, halts with `none`; otherwise deducts `fromGasLeft` from `gasLeft`,
   deducts `fromReservoir` from `stateGasReservoir`, increments `stateGasDrawn` by `fromReservoir`,
   and increments `evmStateGasUsed` by `amount`. -/
@[simp]
def charge_state_with_ceiling_d13a (m : D13AMeter) (amount legacyShare : Nat)
    (ceilingOverride : Option Nat) : Option D13AMeter :=
  let leg := min amount legacyShare
  let rest := amount - leg
  let maxFromRes := min rest m.stateGasReservoir
  let fromReservoir := cap_by_ceiling maxFromRes m.stateGasDrawn ceilingOverride
  let fromGasLeft := amount - fromReservoir
  if m.gasLeft < fromGasLeft then
    none
  else
    some { m with
      gasLeft := m.gasLeft - fromGasLeft
      stateGasReservoir := m.stateGasReservoir - fromReservoir
      evmStateGasUsed := m.evmStateGasUsed + (amount : Int)
      stateGasDrawn := m.stateGasDrawn + fromReservoir }

/-- Standard state-gas charge using the current frame's own `m.stateGasCeiling`. -/
@[simp]
def charge_state_d13a (m : D13AMeter) (amount legacyShare : Nat) : Option D13AMeter :=
  charge_state_with_ceiling_d13a m amount legacyShare m.stateGasCeiling

/-- Refill state gas (`EIPS/eip-8037.md:72, 229`):
Credits `stateGasReservoir` only, decrements `evmStateGasUsed`, NEVER credits `gasLeft`,
and NEVER changes `stateGasDrawn`. -/
@[simp]
def refill_state_d13a (m : D13AMeter) (amount : Nat) : D13AMeter :=
  { m with
    stateGasReservoir := m.stateGasReservoir + amount
    evmStateGasUsed := m.evmStateGasUsed - (amount : Int) }

/-- Spawn a child `D13AMeter` of `kind` by charging `callCost` (which includes `childGas` minus any
call stipend) from `parent.gasLeft` and granting `childGas` execution gas to the child
(`EIPS/eip-8037.md:73, 206-215`). Returns `(childInit, parentWithheld)`. -/
@[simp]
def enter_child_d13a (mode : AllowanceMode) (kind : CallFrameKind)
    (parent : D13AMeter) (callCost childGas : Nat) : Option (D13AMeter × D13AMeter) :=
  if parent.gasLeft < callCost then
    none
  else
    let parentWithheld : D13AMeter := { parent with gasLeft := parent.gasLeft - callCost }
    let childCeiling := derive_child_ceiling mode kind parentWithheld childGas
    let childInit : D13AMeter :=
      { gasLeft := childGas
        stateGasReservoir := parentWithheld.stateGasReservoir
        evmStateGasUsed := parentWithheld.evmStateGasUsed
        stateGasDrawn := parentWithheld.stateGasDrawn
        reservoirSnapshot := parentWithheld.stateGasReservoir
        usedSnapshot := parentWithheld.evmStateGasUsed
        drawnSnapshot := parentWithheld.stateGasDrawn
        stateGasCeiling := childCeiling }
    some (childInit, parentWithheld)

/-- Incorporate a returning child `D13AMeter` into `parentWithheld` (`EIPS/eip-8037.md:126-189, 229`):
- On `.success`: `gasLeft := parentWithheld.gasLeft + child.gasLeft`; `stateGasReservoir`,
  `evmStateGasUsed`, and `stateGasDrawn` are adopted from `child`.
- On `.revert`: `gasLeft := parentWithheld.gasLeft + child.gasLeft`,
  `stateGasReservoir := (child.stateGasReservoir : Int) + (child.evmStateGasUsed - child.usedSnapshot)`
  (which equals `child.reservoirSnapshot + childSpillFromGasLeft`),
  `evmStateGasUsed := child.usedSnapshot`, and `stateGasDrawn := child.drawnSnapshot`.
- On `.halt`: `gasLeft := parentWithheld.gasLeft` (`child.gasLeft` is forfeited),
  `stateGasReservoir := child.reservoirSnapshot`,
  `evmStateGasUsed := child.usedSnapshot`, and `stateGasDrawn := child.drawnSnapshot`. -/
@[simp]
def exit_child_d13a (parentWithheld child : D13AMeter) (status : ChildStatus) : D13AMeter :=
  match status with
  | .success =>
    { parentWithheld with
      gasLeft := parentWithheld.gasLeft + child.gasLeft
      stateGasReservoir := child.stateGasReservoir
      evmStateGasUsed := child.evmStateGasUsed
      stateGasDrawn := child.stateGasDrawn }
  | .revert =>
    let restoredReservoir : Nat :=
      Int.toNat ((child.stateGasReservoir : Int) + (child.evmStateGasUsed - child.usedSnapshot))
    { parentWithheld with
      gasLeft := parentWithheld.gasLeft + child.gasLeft
      stateGasReservoir := restoredReservoir
      evmStateGasUsed := child.usedSnapshot
      stateGasDrawn := child.drawnSnapshot }
  | .halt =>
    { parentWithheld with
      gasLeft := parentWithheld.gasLeft
      stateGasReservoir := child.reservoirSnapshot
      evmStateGasUsed := child.usedSnapshot
      stateGasDrawn := child.drawnSnapshot }

/-- Charge `CREATE`/`CREATE2` code deposit on the merged parent frame after `Refund`
(`EthereumGasPolicy.TryConsumeCodeDepositGas` and `RevertRefundToHalt` in `NethermindEth/nethermind#15187`,
matching `EIPS/eip-8037.md:228`):
- The code deposit (`codeBytes * COST_PER_STATE_BYTE` state gas, `legacyShare = 0`, plus `execDepositCost`
  execution gas) is charged using `childFinal.stateGasCeiling` (the create frame's ceiling!).
- If the code deposit succeeds, the updated parent frame is returned.
- If the code deposit fails OOG, the child create frame is converted from `.success` to `.halt`
  (`RevertRefundToHalt`), forfeiting `childFinal.gasLeft`, restoring `stateGasReservoir`,
  `evmStateGasUsed`, and `stateGasDrawn` to `childFinal`'s entry snapshots, and refilling the parent's
  `STATE_GAS_NEW_ACCOUNT` charge if `hadNewAccountCharge = true`. -/
def finish_create_code_deposit_d13a (parentWithheld childFinal : D13AMeter)
    (codeBytes execDepositCost : Nat) (hadNewAccountCharge : Bool) : D13AMeter × Bool :=
  let merged := exit_child_d13a parentWithheld childFinal .success
  let depositStateCost := codeBytes * COST_PER_STATE_BYTE
  let afterExecOpt := charge_exec_d13a merged execDepositCost
  let afterBothOpt :=
    match afterExecOpt with
    | none => none
    | some afterExec =>
      charge_state_with_ceiling_d13a afterExec depositStateCost 0 childFinal.stateGasCeiling
  match afterBothOpt with
  | some postDeposit => (postDeposit, true)
  | none =>
    let halted := exit_child_d13a parentWithheld childFinal .halt
    let postRefill := if hadNewAccountCharge then refill_state_d13a halted STATE_GAS_NEW_ACCOUNT else halted
    (postRefill, false)

/-! ## 3. Property 1: `DELEGATECALL` / `CALLCODE` Frame-Invariance (`#12582`) & Proxy Divergence in `#15187` -/

/-- Abstract intra-frame gas operation (execution charge, state charge with legacy share, or state refill). -/
inductive FrameGasOp where
  | exec (amount : Nat)
  | state (amount legacyShare : Nat)
  | refill (amount : Nat)
  deriving Repr, DecidableEq, BEq

/-- Apply a single `FrameGasOp` to `D13AMeter`. -/
@[simp]
def apply_frame_op (m : D13AMeter) (op : FrameGasOp) : Option D13AMeter :=
  match op with
  | .exec amount => charge_exec_d13a m amount
  | .state amount leg => charge_state_d13a m amount leg
  | .refill amount => some (refill_state_d13a m amount)

/-- Apply a list of `FrameGasOp`s sequentially to `D13AMeter`. -/
@[simp]
def apply_frame_ops (m : D13AMeter) : List FrameGasOp → Option D13AMeter
  | [] => some m
  | op :: rest =>
    match apply_frame_op m op with
    | none => none
    | some m' => apply_frame_ops m' rest

/-- Observational equivalence of two `D13AMeter` states on all active gas/reservoir/ceiling counters
(ignoring the frame-local entry snapshots of the parent vs child). -/
@[simp]
def ActiveCountersEq (a b : D13AMeter) : Prop :=
  a.gasLeft = b.gasLeft ∧
  a.stateGasReservoir = b.stateGasReservoir ∧
  a.evmStateGasUsed = b.evmStateGasUsed ∧
  a.stateGasDrawn = b.stateGasDrawn ∧
  a.stateGasCeiling = b.stateGasCeiling

theorem apply_frame_op_preserves_active_counters (a b : D13AMeter) (op : FrameGasOp)
    (h_eq : ActiveCountersEq a b) :
    match apply_frame_op a op, apply_frame_op b op with
    | none, none => True
    | some a', some b' => ActiveCountersEq a' b'
    | _, _ => False := by
  rcases h_eq with ⟨h1, h2, h3, h4, h5⟩
  cases op with
  | exec amount =>
    dsimp only [apply_frame_op, charge_exec_d13a]
    rw [h1]
    by_cases h_cond : b.gasLeft < amount
    · simp [h_cond]
    · simp [h_cond, ActiveCountersEq, h2, h3, h4, h5]
  | state amount leg =>
    dsimp only [apply_frame_op, charge_state_d13a, charge_state_with_ceiling_d13a]
    rw [h1, h2, h3, h4, h5]
    by_cases h_cond :
        b.gasLeft <
          amount -
            cap_by_ceiling (min (amount - min amount leg) b.stateGasReservoir)
              b.stateGasDrawn b.stateGasCeiling
    · simp only [h_cond, ↓reduceIte]
    · simp only [h_cond, ↓reduceIte, ActiveCountersEq, and_self]
  | refill amount =>
    dsimp only [apply_frame_op, refill_state_d13a]
    refine ⟨h1, by rw [h2], by rw [h3], h4, h5⟩

theorem apply_frame_ops_preserves_active_counters (ops : List FrameGasOp) :
    ∀ (a b : D13AMeter), ActiveCountersEq a b →
      match apply_frame_ops a ops, apply_frame_ops b ops with
      | none, none => True
      | some a', some b' => ActiveCountersEq a' b'
      | _, _ => False := by
  induction ops with
  | nil =>
    intro a b h_eq
    exact h_eq
  | cons op rest ih =>
    intro a b h_eq
    dsimp only [apply_frame_ops]
    have h_step := apply_frame_op_preserves_active_counters a b op h_eq
    cases ha : apply_frame_op a op <;> cases hb : apply_frame_op b op
    · trivial
    · rw [ha, hb] at h_step; exact False.elim h_step
    · rw [ha, hb] at h_step; exact False.elim h_step
    · rw [ha, hb] at h_step
      exact ih _ _ h_step

/-- **Property 1 (`t_12582_prop1_delegatecall_frame_invariance`)**:
Under normative `ethereum/EIPs#12582` (`.d13a_normative`), refactoring any sequence of execution
charges, state charges (storage sets, account creations, code deposits), and state refills into a
`DELEGATECALL` or `CALLCODE` library frame (when forwarding the parent's remaining `gasLeft` after
`callCost` and returning `.success`) produces the **exact same** `D13AMeter` as executing those
operations directly in the parent frame after `charge_exec_d13a parent callCost`! -/
theorem t_12582_prop1_delegatecall_frame_invariance
    (kind : CallFrameKind) (h_inh : kind.inheritsCeiling = true)
    (parentAfterCost parentWithheld childInit childDone inlineDone : D13AMeter)
    (ops : List FrameGasOp)
    (h_enter : enter_child_d13a .d13a_normative kind parentAfterCost
      parentAfterCost.gasLeft parentAfterCost.gasLeft = some (childInit, parentWithheld))
    (h_child : apply_frame_ops childInit ops = some childDone)
    (h_inline : apply_frame_ops parentAfterCost ops = some inlineDone) :
    exit_child_d13a parentWithheld childDone .success = inlineDone := by
  dsimp only [enter_child_d13a] at h_enter
  simp only [Nat.lt_irrefl, ↓reduceIte, Prod.mk.injEq, Option.some.injEq] at h_enter
  rcases h_enter with ⟨h_c, h_pw⟩
  have h_init_eq : ActiveCountersEq childInit parentAfterCost := by
    subst h_c
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    dsimp only [derive_child_ceiling]
    rw [h_inh]
    rfl
  have h_ops := apply_frame_ops_preserves_active_counters ops childInit parentAfterCost h_init_eq
  rw [h_child, h_inline] at h_ops
  rcases h_ops with ⟨hg, hr, hu, hd, _⟩
  have h_snap :
      inlineDone.reservoirSnapshot = parentAfterCost.reservoirSnapshot ∧
      inlineDone.usedSnapshot = parentAfterCost.usedSnapshot ∧
      inlineDone.drawnSnapshot = parentAfterCost.drawnSnapshot ∧
      inlineDone.stateGasCeiling = parentAfterCost.stateGasCeiling := by
    clear h_child h_init_eq h_c h_pw hg hr hu hd
    induction ops generalizing parentAfterCost with
    | nil =>
      simp only [apply_frame_ops, Option.some.injEq] at h_inline
      subst h_inline
      exact ⟨rfl, rfl, rfl, rfl⟩
    | cons op rest ih =>
      dsimp only [apply_frame_ops] at h_inline
      cases hop : apply_frame_op parentAfterCost op with
      | none => rw [hop] at h_inline; contradiction
      | some m' =>
        rw [hop] at h_inline
        have h_m' :
            m'.reservoirSnapshot = parentAfterCost.reservoirSnapshot ∧
            m'.usedSnapshot = parentAfterCost.usedSnapshot ∧
            m'.drawnSnapshot = parentAfterCost.drawnSnapshot ∧
            m'.stateGasCeiling = parentAfterCost.stateGasCeiling := by
          cases op <;> simp only [apply_frame_op, charge_exec_d13a, charge_state_d13a,
            charge_state_with_ceiling_d13a, refill_state_d13a] at hop
          · split at hop
            · contradiction
            · simp only [Option.some.injEq] at hop; subst hop; exact ⟨rfl, rfl, rfl, rfl⟩
          · split at hop
            · contradiction
            · simp only [Option.some.injEq] at hop; subst hop; exact ⟨rfl, rfl, rfl, rfl⟩
          · simp only [Option.some.injEq] at hop; subst hop; exact ⟨rfl, rfl, rfl, rfl⟩
        have h_rest := ih m' h_inline
        exact ⟨h_rest.1.trans h_m'.1, h_rest.2.1.trans h_m'.2.1,
          h_rest.2.2.1.trans h_m'.2.2.1, h_rest.2.2.2.trans h_m'.2.2.2⟩
  subst h_pw
  dsimp only [exit_child_d13a]
  cases inlineDone
  dsimp only at hg hr hu hd h_snap
  simp only [Nat.sub_self, Nat.zero_add, hg, hr, hu, hd, h_snap.1, h_snap.2.1, h_snap.2.2.1, h_snap.2.2.2]

/-- Simulate a top-level proxied factory where `tx.to` (`topGasLeft = 16,600,000`,
`reservoir = 160,000,000`) `DELEGATECALL`s its implementation forwarding `16,500,000` gas,
and the implementation executes `4` sequential `CREATE` deployments of `24,576`-byte contracts
(each `CREATE` charges `Spec.GAS_CREATE_ACCESS = 12,000` exec gas and `STATE_GAS_NEW_ACCOUNT = 183,600`
with `LEGACY_SHARE_CREATE = 20,000`, forwards `63/64` of remaining `gasLeft` to the create frame,
and deposits `24,576` bytes = `37,601,280` state gas). -/
def run_proxied_factory_four_max_creates (mode : AllowanceMode) : Option (D13AMeter × Nat) :=
  let top0 := init_top_meter 16600000 160000000
  match enter_child_d13a mode .delegatecall top0 16500100 16500000 with
  | none => none
  | some (impl0, topWithheld) =>
    let stepCreate (st : D13AMeter × Nat) : Option (D13AMeter × Nat) :=
      let (m, deployedCount) := st
      match charge_exec_d13a m Spec.GAS_CREATE_ACCESS with
      | none => none
      | some m1 =>
        match charge_state_d13a m1 STATE_GAS_NEW_ACCOUNT LEGACY_SHARE_CREATE with
        | none => none
        | some m2 =>
          let createGas := max_message_call_gas m2.gasLeft
          match enter_child_d13a mode .create m2 createGas createGas with
          | none => none
          | some (cInit, mWithheld) =>
            let (mAfterCreate, ok) := finish_create_code_deposit_d13a mWithheld cInit 24576 0 true
            some (mAfterCreate, if ok then deployedCount + 1 else deployedCount)
    match stepCreate (impl0, 0) >>= stepCreate >>= stepCreate >>= stepCreate with
    | none => none
    | some (implFinal, count) =>
      some (exit_child_d13a topWithheld implFinal .success, count)

/-- **Property 1b (`t_12582_prop1b_nethermind15187_proxied_factory_divergence`)**:
When a top-level proxy contract `DELEGATECALL`s a factory implementation (`16,500,000` forwarded gas,
`160,000,000` reservoir) to deploy four `24,576`-byte contracts (`4 × 37,784,880 = 151,139,520`
total state gas):
1. Under `#12581` (`.d13r_unlimited`) and normative `#12582` (`.d13a_normative`), the `DELEGATECALL`
   frame inherits `stateGasCeiling = none`, so all **4 out of 4** deployments succeed!
2. Under `NethermindEth/nethermind#15187` (`.d13a_nethermind15187`), because `CreateChildFrameGas`
   imposes `StateGasAllowance = 16,500,000 * 1530 / 200 = 126,225,000` on the `DELEGATECALL` frame,
   only **3 out of 4** deployments succeed (`113,174,640` drawn) and the 4th deployment (`37,601,280`
   code deposit) fails OOG because the `DELEGATECALL` ceiling caps the create frame's allowance! -/
theorem t_12582_prop1b_nethermind15187_proxied_factory_divergence :
    (run_proxied_factory_four_max_creates .d13r_unlimited).map Prod.snd = some 4 ∧
    (run_proxied_factory_four_max_creates .d13a_normative).map Prod.snd = some 4 ∧
    (run_proxied_factory_four_max_creates .d13a_nethermind15187).map Prod.snd = some 3 := by
  decide

/-! ## 4. Property 2: `gas_left` Non-Increasing Within a Frame & Across Calls (No `T2` Bug) -/

/-- **Property 2 (`t_12582_prop2_gas_left_non_increasing_in_frame`)**:
Within any frame under `#12582` (`D13AMeter`), execution charges, state charges (under any ceiling),
and state refills NEVER increase `gasLeft`; in particular, `refill_state_d13a` leaves `gasLeft`
strictly unchanged (`(refill_state_d13a m amount).gasLeft = m.gasLeft`). -/
theorem t_12582_prop2_gas_left_non_increasing_in_frame
    (m post : D13AMeter) (amount legacyShare : Nat) (ceilingOpt : Option Nat) :
    (charge_exec_d13a m amount = some post → post.gasLeft ≤ m.gasLeft) ∧
    (charge_state_with_ceiling_d13a m amount legacyShare ceilingOpt = some post → post.gasLeft ≤ m.gasLeft) ∧
    (refill_state_d13a m amount).gasLeft = m.gasLeft := by
  refine ⟨?_, ?_, rfl⟩
  · intro h
    dsimp only [charge_exec_d13a] at h
    split at h
    · contradiction
    · simp only [Option.some.injEq] at h
      subst h
      dsimp only
      omega
  · intro h
    dsimp only [charge_state_with_ceiling_d13a] at h
    split at h
    · contradiction
    · simp only [Option.some.injEq] at h
      subst h
      dsimp only
      omega

/-- **Property 2b (`t_12582_prop2b_child_exit_bounded_by_child_gas_left`)**:
Across any call boundary (`enter_child_d13a` followed by `exit_child_d13a` under `.success`,
`.revert`, or `.halt`), if the child frame's `gasLeft` never rose above its initial grant `childGas`
(`childDone.gasLeft ≤ childInit.gasLeft`) and `childGas ≤ callCost` (as holds for all call and create
opcodes where `callCost ≥ childGas - stipend`), then:
1. `(exit_child_d13a parentWithheld childDone status).gasLeft ≤ parentWithheld.gasLeft + childDone.gasLeft`, and
2. When `childGas ≤ callCost`, `(exit_child_d13a parentWithheld childDone status).gasLeft ≤ parent.gasLeft`
   (the parent's `gas_left` after the call is never larger than before the call!). -/
theorem t_12582_prop2b_child_exit_bounded_by_child_gas_left
    (mode : AllowanceMode) (kind : CallFrameKind)
    (parent childInit parentWithheld childDone : D13AMeter)
    (callCost childGas : Nat) (status : ChildStatus)
    (h_enter : enter_child_d13a mode kind parent callCost childGas = some (childInit, parentWithheld))
    (h_child_mono : childDone.gasLeft ≤ childInit.gasLeft) :
    (exit_child_d13a parentWithheld childDone status).gasLeft ≤
      parentWithheld.gasLeft + childDone.gasLeft ∧
    (childGas ≤ callCost →
      (exit_child_d13a parentWithheld childDone status).gasLeft ≤ parent.gasLeft) := by
  dsimp only [enter_child_d13a] at h_enter
  split at h_enter
  · contradiction
  · simp only [Prod.mk.injEq, Option.some.injEq] at h_enter
    rcases h_enter with ⟨h_c, h_p⟩
    subst h_c h_p
    dsimp only at h_child_mono
    cases status <;> simp only [exit_child_d13a] <;> refine ⟨by omega, fun _ => by omega⟩

/-! ## 5. Property 3: Untrusted Callee Reservoir Drain Bound (`Δ state_gas_drawn ≤ ⌊g × CPSB / 200⌋`) -/

/-- Well-formedness invariant on a frame's reservoir draw counter:
1. `m.drawnSnapshot ≤ m.stateGasDrawn` (draws only increase within a frame).
2. If `m.stateGasCeiling = some c`, then `m.stateGasDrawn ≤ c` (draws never exceed the active ceiling). -/
def DrawnWithinCeiling (m : D13AMeter) : Prop :=
  m.drawnSnapshot ≤ m.stateGasDrawn ∧
  match m.stateGasCeiling with
  | none => True
  | some c => m.stateGasDrawn ≤ c

/-- Every intra-frame operation (`charge_exec_d13a`, `charge_state_d13a`, `refill_state_d13a`)
preserves `DrawnWithinCeiling`. -/
theorem frame_op_preserves_drawn_within_ceiling (m post : D13AMeter) (op : FrameGasOp)
    (h_inv : DrawnWithinCeiling m)
    (h_step : apply_frame_op m op = some post) :
    DrawnWithinCeiling post := by
  rcases m with ⟨gasLeft, res, used, drawn, resSnap, usedSnap, snap, _ | c⟩
  · rcases h_inv with ⟨h_snap, _⟩
    dsimp only at h_snap
    cases op with
    | exec amount =>
      dsimp only [apply_frame_op, charge_exec_d13a] at h_step
      split at h_step
      · contradiction
      · simp only [Option.some.injEq] at h_step; subst h_step
        exact ⟨h_snap, trivial⟩
    | state amount leg =>
      dsimp only [apply_frame_op, charge_state_d13a, charge_state_with_ceiling_d13a] at h_step
      split at h_step
      · contradiction
      · simp only [Option.some.injEq] at h_step; subst h_step
        exact ⟨by dsimp only; omega, trivial⟩
    | refill amount =>
      simp only [apply_frame_op, refill_state_d13a, Option.some.injEq] at h_step
      subst h_step
      exact ⟨h_snap, trivial⟩
  · rcases h_inv with ⟨h_snap, h_ceil⟩
    dsimp only at h_snap h_ceil
    cases op with
    | exec amount =>
      dsimp only [apply_frame_op, charge_exec_d13a] at h_step
      split at h_step
      · contradiction
      · simp only [Option.some.injEq] at h_step; subst h_step
        exact ⟨h_snap, h_ceil⟩
    | state amount leg =>
      dsimp only [apply_frame_op, charge_state_d13a, charge_state_with_ceiling_d13a, cap_by_ceiling] at h_step
      split at h_step
      · contradiction
      · simp only [Option.some.injEq] at h_step; subst h_step
        refine ⟨by dsimp only; omega, by dsimp only; omega⟩
    | refill amount =>
      simp only [apply_frame_op, refill_state_d13a, Option.some.injEq] at h_step
      subst h_step
      exact ⟨h_snap, h_ceil⟩

theorem frame_ops_preserve_drawn_within_ceiling (ops : List FrameGasOp) :
    ∀ (m post : D13AMeter),
      DrawnWithinCeiling m →
      apply_frame_ops m ops = some post →
      DrawnWithinCeiling post := by
  induction ops with
  | nil =>
    intro m post h_inv h_step
    simp only [apply_frame_ops, Option.some.injEq] at h_step
    subst h_step
    exact h_inv
  | cons op rest ih =>
    intro m post h_inv h_step
    dsimp only [apply_frame_ops] at h_step
    cases hop : apply_frame_op m op with
    | none => rw [hop] at h_step; contradiction
    | some m' =>
      rw [hop] at h_step
      exact ih m' post (frame_op_preserves_drawn_within_ceiling m m' op h_inv hop) h_step

/-- **Property 3 (`t_12582_prop3_subcall_ceiling_bounded`)**:
When a non-inheriting subcall (`CALL`, `STATICCALL`, `CREATE`, `CREATE2`) is spawned under
normative `#12582` (`.d13a_normative`) with forwarded gas `childGas = g` from a parent satisfying
`DrawnWithinCeiling parent`, the child frame `childInit` has a concrete ceiling `some c` satisfying:
1. `DrawnWithinCeiling childInit`,
2. `c ≤ parent.stateGasDrawn + g * COST_PER_STATE_BYTE / LEGACY_GAS_PER_STATE_BYTE`, and
3. If `parent.stateGasCeiling = some pCeil`, then `c ≤ pCeil`. -/
theorem t_12582_prop3_subcall_ceiling_bounded
    (kind : CallFrameKind) (h_sub : kind.inheritsCeiling = false)
    (parent childInit parentWithheld : D13AMeter) (callCost g : Nat)
    (h_parent_inv : DrawnWithinCeiling parent)
    (h_enter : enter_child_d13a .d13a_normative kind parent callCost g =
      some (childInit, parentWithheld)) :
    ∃ c : Nat,
      childInit.stateGasCeiling = some c ∧
      DrawnWithinCeiling childInit ∧
      c ≤ parent.stateGasDrawn + g * COST_PER_STATE_BYTE / LEGACY_GAS_PER_STATE_BYTE ∧
      match parent.stateGasCeiling with
      | none => True
      | some pCeil => c ≤ pCeil := by
  rcases parent with ⟨pGas, pRes, pUsed, pDrawn, pResSnap, pUsedSnap, pSnap, _ | pCeil⟩
  · dsimp only [enter_child_d13a] at h_enter
    split at h_enter
    · contradiction
    · simp only [Prod.mk.injEq, Option.some.injEq] at h_enter
      rcases h_enter with ⟨h_c, _⟩
      subst h_c
      dsimp only [derive_child_ceiling, min_ceiling, allowance_from_gas]
      rw [h_sub]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨pDrawn + g * COST_PER_STATE_BYTE / LEGACY_GAS_PER_STATE_BYTE, rfl,
        ⟨Nat.le_refl _, Nat.le_add_right pDrawn _⟩, Nat.le_refl _, trivial⟩
  · rcases h_parent_inv with ⟨_, h_pceil⟩
    dsimp only at h_pceil
    dsimp only [enter_child_d13a] at h_enter
    split at h_enter
    · contradiction
    · simp only [Prod.mk.injEq, Option.some.injEq] at h_enter
      rcases h_enter with ⟨h_c, _⟩
      subst h_c
      dsimp only [derive_child_ceiling, min_ceiling, allowance_from_gas]
      rw [h_sub]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨min pCeil (pDrawn + g * COST_PER_STATE_BYTE / LEGACY_GAS_PER_STATE_BYTE), rfl,
        ⟨Nat.le_refl _, Nat.le_min.mpr ⟨h_pceil, Nat.le_add_right pDrawn _⟩⟩,
        Nat.min_le_right _ _, Nat.min_le_left _ _⟩

/-- **Property 3b (`t_12582_prop3b_untrusted_callee_reservoir_drain_bound`)**:
For any non-inheriting subcall (`CALL`, `STATICCALL`, `CREATE`, `CREATE2`) spawned with forwarded
gas `g` under `#12582`, after ANY sequence of state charges, SSTORE `1 -> 0` refills, and
execution charges inside the child (`apply_frame_ops childInit ops = some childDone`) and for ANY
termination status (`.success`, `.revert`, `.halt`), the net increase in `stateGasDrawn` in the
parent after `exit_child_d13a` is bounded by `⌊g × COST_PER_STATE_BYTE / LEGACY_GAS_PER_STATE_BYTE⌋`
(`⌊g × 1530 / 200⌋`):
`postParent.stateGasDrawn - parent.stateGasDrawn ≤ g * COST_PER_STATE_BYTE / LEGACY_GAS_PER_STATE_BYTE`,
and `DrawnWithinCeiling postParent` is preserved! -/
theorem t_12582_prop3b_untrusted_callee_reservoir_drain_bound
    (kind : CallFrameKind) (h_sub : kind.inheritsCeiling = false)
    (parent childInit parentWithheld childDone : D13AMeter)
    (callCost g : Nat) (ops : List FrameGasOp) (status : ChildStatus)
    (h_parent_inv : DrawnWithinCeiling parent)
    (h_enter : enter_child_d13a .d13a_normative kind parent callCost g =
      some (childInit, parentWithheld))
    (h_ops : apply_frame_ops childInit ops = some childDone) :
    let postParent := exit_child_d13a parentWithheld childDone status
    parent.stateGasDrawn ≤ postParent.stateGasDrawn ∧
    postParent.stateGasDrawn - parent.stateGasDrawn ≤
      g * COST_PER_STATE_BYTE / LEGACY_GAS_PER_STATE_BYTE ∧
    DrawnWithinCeiling postParent := by
  obtain ⟨c, h_ceil_eq, h_child_init_inv, h_c_bound, h_c_pceil⟩ :=
    t_12582_prop3_subcall_ceiling_bounded kind h_sub parent childInit parentWithheld callCost g
      h_parent_inv h_enter
  have h_done_inv := frame_ops_preserve_drawn_within_ceiling ops childInit childDone h_child_init_inv h_ops
  have h_snap_preserved :
      childDone.drawnSnapshot = childInit.drawnSnapshot ∧
      childDone.stateGasCeiling = childInit.stateGasCeiling := by
    clear h_done_inv h_ceil_eq h_child_init_inv h_c_bound h_c_pceil h_enter
    induction ops generalizing childInit with
    | nil =>
      simp only [apply_frame_ops, Option.some.injEq] at h_ops
      subst h_ops
      exact ⟨rfl, rfl⟩
    | cons op rest ih =>
      dsimp only [apply_frame_ops] at h_ops
      cases hop : apply_frame_op childInit op with
      | none => rw [hop] at h_ops; contradiction
      | some m' =>
        rw [hop] at h_ops
        have hm' : m'.drawnSnapshot = childInit.drawnSnapshot ∧ m'.stateGasCeiling = childInit.stateGasCeiling := by
          cases op <;> simp only [apply_frame_op, charge_exec_d13a, charge_state_d13a,
            charge_state_with_ceiling_d13a, refill_state_d13a] at hop
          · split at hop
            · contradiction
            · simp only [Option.some.injEq] at hop; subst hop; exact ⟨rfl, rfl⟩
          · split at hop
            · contradiction
            · simp only [Option.some.injEq] at hop; subst hop; exact ⟨rfl, rfl⟩
          · simp only [Option.some.injEq] at hop; subst hop; exact ⟨rfl, rfl⟩
        have h_rest := ih m' h_ops
        exact ⟨h_rest.1.trans hm'.1, h_rest.2.trans hm'.2⟩
  dsimp only [enter_child_d13a] at h_enter
  split at h_enter
  · contradiction
  · simp only [Prod.mk.injEq, Option.some.injEq] at h_enter
    rcases h_enter with ⟨h_c, h_p⟩
    have h_init_snap : childInit.drawnSnapshot = parent.stateGasDrawn := by
      subst h_c; rfl
    have h_pw_fields :
        parentWithheld.drawnSnapshot = parent.drawnSnapshot ∧
        parentWithheld.stateGasDrawn = parent.stateGasDrawn ∧
        parentWithheld.stateGasCeiling = parent.stateGasCeiling := by
      subst h_p; exact ⟨rfl, rfl, rfl⟩
    rcases h_done_inv with ⟨h_done_ge_snap, h_done_le_ceil⟩
    rw [h_snap_preserved.1, h_init_snap] at h_done_ge_snap
    rw [h_snap_preserved.2, h_ceil_eq] at h_done_le_ceil
    rcases h_parent_inv with ⟨h_p_snap, h_p_ceil⟩
    have h_ratio_nonneg : 0 ≤ g * COST_PER_STATE_BYTE / LEGACY_GAS_PER_STATE_BYTE := Nat.zero_le _
    cases status with
    | success =>
      dsimp only [exit_child_d13a, DrawnWithinCeiling]
      rw [h_pw_fields.1, h_pw_fields.2.2]
      refine ⟨h_done_ge_snap, by omega, ⟨by omega, ?_⟩⟩
      rcases parent with ⟨_, _, _, _, _, _, _, _ | pCeil⟩
      · trivial
      · dsimp only at h_c_pceil ⊢
        omega
    | revert =>
      dsimp only [exit_child_d13a, DrawnWithinCeiling]
      rw [h_snap_preserved.1, h_init_snap, h_pw_fields.1, h_pw_fields.2.2]
      exact ⟨Nat.le_refl _, by omega, ⟨h_p_snap, h_p_ceil⟩⟩
    | halt =>
      dsimp only [exit_child_d13a, DrawnWithinCeiling]
      rw [h_snap_preserved.1, h_init_snap, h_pw_fields.1, h_pw_fields.2.2]
      exact ⟨Nat.le_refl _, by omega, ⟨h_p_snap, h_p_ceil⟩⟩

/-! ## 6. Property 4: `revert` vs `SSTORE 1 -> 0` Asymmetry on `state_gas_drawn`,
Clean-Trace Monotonicity, and Nethermind `#15187`'s 6 Regression Scenarios -/

/-- Run the warm fresh-slot write through #12582 frame entry and both gas charges,
holding the parent's execution gas and the child's grant fixed. -/
def fixed_budget_fresh_write (reservoir : Nat) : Option D13AMeter := do
  let (child, _) ← enter_child_d13a .d13a_normative .call (init_top_meter 100000 reservoir) 50000 50000
  let afterExec ← charge_exec_d13a child (GAS_WARM_ACCESS + GAS_STORAGE_WRITE)
  charge_state_d13a afterExec STATE_GAS_STORAGE_SET LEGACY_SHARE_STORAGE_SET

/-- INV-4 under the normative allowance proposal. A child receives 50,000 gas
from a parent with an empty reservoir. Frame entry succeeds, but the first
warm write of a fresh slot fails. Funding the reservoir makes the identical
write succeed. The allowance is a ceiling on available funds. -/
theorem t_12582_fixed_budget_empty_reservoir :
    (enter_child_d13a .d13a_normative .call (init_top_meter 100000 0) 50000 50000).isSome = true ∧
    fixed_budget_fresh_write 0 = none ∧
    (fixed_budget_fresh_write STATE_GAS_STORAGE_SET).isSome = true := by
  decide

/-- Execute `k` iterations of a warm `SSTORE 0 -> 1` followed by `SSTORE 1 -> 0` in the same frame
(`10,100` exec gas + `97,920` state gas with `10,000` legacy share, then `100` exec gas + `97,920`
refill). -/
def run_sstore_set_clear_loop (m : D13AMeter) : Nat → Option D13AMeter
  | 0 => some m
  | n + 1 =>
    match charge_exec_d13a m (GAS_WARM_ACCESS + GAS_STORAGE_WRITE) with
    | none => none
    | some m1 =>
      match charge_state_d13a m1 STATE_GAS_STORAGE_SET LEGACY_SHARE_STORAGE_SET with
      | none => none
      | some m2 =>
        match charge_exec_d13a m2 GAS_WARM_ACCESS with
        | none => none
        | some m3 =>
          let m4 := refill_state_d13a m3 STATE_GAS_STORAGE_SET
          run_sstore_set_clear_loop m4 n

/-- Two concrete #12582 traces distinguish a storage refill from a revert.
After one set/clear cycle the prepared child has exhausted its allowance.
The next cycle spends execution gas despite a replenished reservoir. On the
separate revert trace the parent recovers its entry value of stateGasDrawn. -/
theorem t_12582_prop4_revert_vs_refill_drawn_asymmetry :
    let top := init_top_meter 1000000 10000000
    let child200k : D13AMeter :=
      { gasLeft := 200000
        stateGasReservoir := 10000000
        stateGasDrawn := 1450000
        reservoirSnapshot := 10000000
        drawnSnapshot := 0
        stateGasCeiling := some 1530000 }
    let after1 := run_sstore_set_clear_loop child200k 1
    let after2 := run_sstore_set_clear_loop child200k 2
    let revertChild :=
      match enter_child_d13a .d13a_normative .call top 50000 50000 with
      | none => none
      | some (c0, pWith) =>
        match charge_state_d13a c0 STATE_GAS_STORAGE_SET LEGACY_SHARE_STORAGE_SET with
        | none => none
        | some c1 => some (exit_child_d13a pWith c1 .revert)
    after1.map (fun m => (m.gasLeft, m.stateGasDrawn, remaining_allowance m)) =
      some (171880, 1530000, some 0) ∧
    after2.map (fun m => (m.gasLeft, m.stateGasDrawn, remaining_allowance m)) =
      some (63760, 1530000, some 0) ∧
    revertChild.map (fun m => m.stateGasDrawn) = some 0 := by
  decide

/-- **Property 4b (`t_12582_prop4b_clean_trace_single_charge_monotone`)**:
For any state-gas charge `(amount, legacyShare)` and any two frame meters `m1` and `m2` that have
the same `stateGasDrawn` and `stateGasCeiling` with `m1.gasLeft ≤ m2.gasLeft` and
`m1.stateGasReservoir ≤ m2.stateGasReservoir` (as occurs on any clean trace when `tx.gas` increases),
if the state charge succeeds on `m1` (`charge_state_d13a m1 amount legacyShare = some post1`), then
it also succeeds on `m2` (`∃ post2, charge_state_d13a m2 amount legacyShare = some post2`) with
`post1.gasLeft ≤ post2.gasLeft`, and the reservoir draw on `m2` is at least as large as on `m1`! -/
theorem t_12582_prop4b_clean_trace_single_charge_monotone
    (m1 m2 post1 : D13AMeter) (amount legacyShare : Nat)
    (h_gas : m1.gasLeft ≤ m2.gasLeft)
    (h_res : m1.stateGasReservoir ≤ m2.stateGasReservoir)
    (h_drawn : m1.stateGasDrawn = m2.stateGasDrawn)
    (h_ceil : m1.stateGasCeiling = m2.stateGasCeiling)
    (h_step1 : charge_state_d13a m1 amount legacyShare = some post1) :
    ∃ post2 : D13AMeter,
      charge_state_d13a m2 amount legacyShare = some post2 ∧
      post1.gasLeft ≤ post2.gasLeft ∧
      post1.stateGasDrawn ≤ post2.stateGasDrawn := by
  dsimp only [charge_state_d13a, charge_state_with_ceiling_d13a] at h_step1 ⊢
  rw [← h_drawn, ← h_ceil]
  have h_cap_le :
      cap_by_ceiling (min (amount - min amount legacyShare) m1.stateGasReservoir)
        m1.stateGasDrawn m1.stateGasCeiling ≤
      cap_by_ceiling (min (amount - min amount legacyShare) m2.stateGasReservoir)
        m1.stateGasDrawn m1.stateGasCeiling := by
    cases m1.stateGasCeiling <;> dsimp only [cap_by_ceiling] <;> omega
  split at h_step1
  · contradiction
  · simp only [Option.some.injEq] at h_step1
    subst h_step1
    have h_ok2 : ¬ (m2.gasLeft < amount - cap_by_ceiling (min (amount - min amount legacyShare) m2.stateGasReservoir)
        m1.stateGasDrawn m1.stateGasCeiling) := by
      omega
    simp only [h_ok2, ↓reduceIte]
    refine ⟨_, rfl, by dsimp only; omega, by dsimp only; omega⟩

/-- **Property 4c (`t_12582_prop4c_nethermind_15187_six_regression_cases`)**:
Machine-checked verification of the 6 core regression scenarios from `NethermindEth/nethermind#15187`
and the normative test table of `ethereum/EIPs#12582`:
1. **Case 1 (`Eip8037_callee_pays_from_gas_left_when_its_ancestor_used_the_allowance`)**:
   A `400,000`-gas frame (`allowance = 3,060,000`) deploys an `1,800`-byte contract (`163,600`
   account-creation reservoir draw + `1,800 × 1,530 = 2,754,000` deposit draw = `2,917,600` drawn,
   leaving `142,400` allowance), then calls a `230,000`-gas callee that writes two cold slots
   (`2 × 87,920 = 175,840` non-legacy state gas). The callee draws `142,400` from the reservoir,
   spills the remaining `33,440` (plus `2 × 22,100 = 44,200` execution + legacy share) from its
   own `gasLeft` (`230,000 - 77,640 = 152,360`), and succeeds!
2. **Case 2 (`Eip8037_large_code_deposit_fails_only_the_create_of_a_gas_limited_callee`)**:
   A `50,000`-gas callee (`allowance = 382,500`) runs `CREATE` whose initcode returns `24,576` bytes
   (`37,601,280` deposit). Even with a `40,000,000` reservoir, the code deposit is capped by the
   create frame's ceiling, so only the `CREATE` fails (`ok = false`) while the caller retains its
   reservoir and succeeds.
3. **Case 3 (`Eip8037_callee_cannot_drain_the_reservoir_of_a_later_callee`)**:
   With `reservoir = 87,920 + 163,600 + 1,024 × 1,530 + 10,000 = 1,828,240`, Callee 1 (`100,000` gas)
   writes a cold slot (`87,920` drawn, leaving `1,740,320`), Callee 2 (`100,000` gas, `765,000`
   allowance) attempts to deploy `1,024` bytes (`1,566,720` deposit):
   - Under `#12581` (`.d13r_unlimited`), Callee 2's deployment succeeds and drains the reservoir to
     `10,000`, causing Callee 3 (`100,000` gas, writing 1 cold slot needing `110,020` without
     reservoir) to halt OOG (`none`)!
   - Under `#12582` (`.d13a_normative`), Callee 2's deployment fails its code deposit, restoring
     the reservoir to `1,740,320`, so Callee 3 succeeds (`some 77900`)!
4. **Case 4 (`Code_deposit_above_the_create_frame_allowance_pays_the_rest_from_gas_left`)**:
   A `50,000`-gas create frame (`allowance = 382,500`) under a `100,000`-gas parent (`allowance = 765,000`,
   with `50,000` remaining in parent) deposits `251` bytes (`251 × 1,530 = 384,030` state gas,
   `48` exec gas). `finish_create_code_deposit_d13a` draws `382,500` from the reservoir and pays
   `1,530 + 48 = 1,578` from the merged `gasLeft` (`100,000 - 1,578 = 98,422`), leaving
   `stateGasReservoir = 9,617,500` and `stateGasDrawn = 382,500`!
5. **Case 5 (`Code_deposit_halt_returns_the_child_draws_to_the_parent_allowance`)**:
   When a `50,000`-gas create child draws its full `382,500` allowance during initcode and then
   fails the code deposit (e.g., `24,576` bytes), `finish_create_code_deposit_d13a` (`RevertRefundToHalt`)
   restores `parent.stateGasDrawn = 0`, so the `100,000`-gas parent can still draw its full
   `765,000` allowance from the reservoir!
6. **Case 6 (`CALL` with value to a cold non-existent account charge ordering before `63/64`,
   `EIPS/eip-8037.md:341-348`)**:
   Starting from `gasLeft = 1,000,000`, charging `COLD_ACCOUNT_ACCESS + CALL_VALUE = 14,300` exec
   gas and `STATE_GAS_NEW_ACCOUNT = 183,600` (`legacyShare = 25,000`) BEFORE `max_message_call_gas`:
   - When `reservoir = 1,000,000`: charges `39,300` from `gasLeft` (`960,700` remaining), forwards
     `max_message_call_gas 960700 = 945,690`, retains `15,010`, and draws `158,600` from reservoir.
   - When `reservoir = 0`: charges `197,900` from `gasLeft` (`802,100` remaining), forwards
     `max_message_call_gas 802100 = 789,568`, and retains `12,532`. -/
theorem t_12582_prop4c_nethermind_15187_six_regression_cases :
    -- Case 1: Ancestor uses 2,917,600 of 3,060,000 allowance; 230,000-gas child writes 2 cold slots and succeeds
    (let top1 := init_top_meter 1000000 10000000
     let dFrame : D13AMeter :=
       { gasLeft := 300000, stateGasReservoir := 7082400, evmStateGasUsed := 2937600,
         stateGasDrawn := 2917600, reservoirSnapshot := 10000000, drawnSnapshot := 0,
         stateGasCeiling := some 3060000 }
     match enter_child_d13a .d13a_normative .call dFrame 230000 230000 with
     | none => none
     | some (e0, dWith) =>
       match charge_exec_d13a e0 (GAS_COLD_STORAGE_ACCESS + GAS_STORAGE_WRITE) with
       | none => none
       | some e1 =>
         match charge_state_d13a e1 STATE_GAS_STORAGE_SET LEGACY_SHARE_STORAGE_SET with
         | none => none
         | some e2 =>
           match charge_exec_d13a e2 (GAS_COLD_STORAGE_ACCESS + GAS_STORAGE_WRITE) with
           | none => none
           | some e3 =>
             match charge_state_d13a e3 STATE_GAS_STORAGE_SET LEGACY_SHARE_STORAGE_SET with
             | none => none
             | some e4 =>
               let dFinal := exit_child_d13a dWith e4 .success
               let topFinal := exit_child_d13a top1 dFinal .success
               some (e4.gasLeft, topFinal.stateGasDrawn)) = some (152360, 3060000) ∧
    -- Case 2: 50,000-gas callee's 24,576-byte CREATE fails only the CREATE
    (let top2 := init_top_meter 16777216 40000000
     match enter_child_d13a .d13a_normative .call top2 50000 50000 with
     | none => none
     | some (callee0, _) =>
       match charge_exec_d13a callee0 Spec.GAS_CREATE_ACCESS with
       | none => none
       | some callee1 =>
         match charge_state_d13a callee1 STATE_GAS_NEW_ACCOUNT LEGACY_SHARE_CREATE with
         | none => none
         | some callee2 =>
           let cg := max_message_call_gas callee2.gasLeft
           match enter_child_d13a .d13a_normative .create callee2 cg cg with
           | none => none
           | some (crInit, calleeWith) =>
             let (calleeAfter, ok) := finish_create_code_deposit_d13a calleeWith crInit 24576 0 true
             some (ok, calleeAfter.evmStateGasUsed, calleeAfter.stateGasDrawn)) = some (false, 0, 163600) ∧
    -- Case 3: 3 callees (100,000 gas each); middle deploys 1,024 bytes. D13R starves 3rd callee; D13A saves 3rd callee
    (let runThreeCallees (mode : AllowanceMode) : Option Nat :=
       let res0 := (STATE_GAS_STORAGE_SET - LEGACY_SHARE_STORAGE_SET) +
         (STATE_GAS_NEW_ACCOUNT - LEGACY_SHARE_CREATE) + 1024 * COST_PER_STATE_BYTE + 10000
       let top := init_top_meter 1000000 res0
       match enter_child_d13a mode .call top 100000 100000 with
       | none => none
       | some (c1_0, topW1) =>
         match charge_exec_d13a c1_0 (GAS_COLD_STORAGE_ACCESS + GAS_STORAGE_WRITE) >>=
             fun m => charge_state_d13a m STATE_GAS_STORAGE_SET LEGACY_SHARE_STORAGE_SET with
         | none => none
         | some c1_done =>
           let topAfter1 := exit_child_d13a topW1 c1_done .success
           match enter_child_d13a mode .call topAfter1 100000 100000 with
           | none => none
           | some (c2_0, topW2) =>
             match charge_exec_d13a c2_0 Spec.GAS_CREATE_ACCESS >>=
                 fun m => charge_state_d13a m STATE_GAS_NEW_ACCOUNT LEGACY_SHARE_CREATE with
             | none => none
             | some c2_afterAcc =>
               let crG := max_message_call_gas c2_afterAcc.gasLeft
               match enter_child_d13a mode .create c2_afterAcc crG crG with
               | none => none
               | some (cr0, c2W) =>
                 let (c2_done, _) := finish_create_code_deposit_d13a c2W cr0 1024 0 true
                 let topAfter2 := exit_child_d13a topW2 c2_done .success
                 match enter_child_d13a mode .call topAfter2 100000 100000 with
                 | none => none
                 | some (c3_0, _) =>
                   match charge_exec_d13a c3_0 (GAS_COLD_STORAGE_ACCESS + GAS_STORAGE_WRITE) >>=
                       fun m => charge_state_d13a m STATE_GAS_STORAGE_SET LEGACY_SHARE_STORAGE_SET with
                   | none => none
                   | some c3_done => some c3_done.gasLeft
     runThreeCallees .d13r_unlimited = none ∧ runThreeCallees .d13a_normative = some 77900) ∧
    -- Case 4: 251-byte code deposit (384,030 state gas, 48 exec gas) draws 382,500 and spills 1,530 from gasLeft
    (let top4 := init_top_meter 1000000 10000000
     match enter_child_d13a .d13a_normative .call top4 100000 100000 with
     | none => none
     | some (p0, _) =>
       match enter_child_d13a .d13a_normative .create p0 50000 50000 with
       | none => none
       | some (c0, pWith) =>
         let (pAfter, ok) := finish_create_code_deposit_d13a pWith c0 251 48 false
         some (ok, pAfter.gasLeft, pAfter.stateGasReservoir, pAfter.evmStateGasUsed, pAfter.stateGasDrawn)) =
      some (true, 98422, 9617500, 384030, 382500) ∧
    -- Case 5: Code-deposit halt removes child draws from parent (`RevertRefundToHalt`)
    (let top5 := init_top_meter 1000000 10000000
     match enter_child_d13a .d13a_normative .call top5 100000 100000 with
     | none => none
     | some (p0, _) =>
       match enter_child_d13a .d13a_normative .create p0 50000 50000 with
       | none => none
       | some (c0, pWith) =>
         match charge_state_d13a c0 382500 0 with
         | none => none
         | some cAfterDraw =>
           let (pAfterHalt, ok) := finish_create_code_deposit_d13a pWith cAfterDraw 24576 0 false
           match charge_state_d13a pAfterHalt 765000 0 with
           | none => none
           | some pFull => some (ok, pAfterHalt.stateGasDrawn, pFull.stateGasDrawn, pFull.gasLeft)) =
      some (false, 0, 765000, 50000) ∧
    -- Case 6: CALL with value to cold non-existent account charge ordering before 63/64
    (let runValueCall (res : Nat) : Option (Nat × Nat × Nat × Nat) :=
       let m0 := init_top_meter 1000000 res
       match charge_exec_d13a m0 (GAS_COLD_ACCOUNT_ACCESS + GAS_CALL_VALUE) with
       | none => none
       | some m1 =>
         match charge_state_d13a m1 STATE_GAS_NEW_ACCOUNT LEGACY_SHARE_NEW_ACCOUNT with
         | none => none
         | some m2 =>
           let chargedBeforeForward := 1000000 - m2.gasLeft
           let forwarded := max_message_call_gas m2.gasLeft
           let retained := m2.gasLeft - forwarded
           let resDrawn := res - m2.stateGasReservoir
           some (chargedBeforeForward, forwarded, retained, resDrawn)
     runValueCall 1000000 = some (39300, 945690, 15010, 158600) ∧
     runValueCall 0 = some (197900, 789568, 12532, 0)) := by
  decide

end Glamsterdam.Gas.Eip12582
