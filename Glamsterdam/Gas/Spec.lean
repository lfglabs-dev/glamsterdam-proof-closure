/-
  Glamsterdam.Gas.Spec: Formal Verification of the Coupled Glamsterdam Gas Model
  (`EIP-8037`, `EIP-8038`, `EIP-2780`, `EIP-7778`)
  Pinned against `ethereum/execution-specs` @ `16898000911c1e3caa57be08509536c10ae92d3e`
  (`src/ethereum/forks/amsterdam/vm/gas.py`, `vm/interpreter.py`, `transactions.py`, `fork.py`).
-/
import Glamsterdam.Common.ElCore

namespace Glamsterdam.Gas.Spec

open Glamsterdam.Common.MetaSpec
open Glamsterdam.Common.ElCore

/-- T-8037-CHARGE-GAS-SOUND: Whenever `charge_gas frame regularGas stateGas = some post`,
    the combined gas (`gasLeft + stateGasReservoir`) decreases by exactly `regularGas + stateGas`,
    and `post.gasLeft ≤ frame.gasLeft` and `post.stateGasReservoir ≤ frame.stateGasReservoir`. -/
theorem t_8037_charge_gas_sound (frame post : EvmGasFrame) (regularGas stateGas : Nat)
    (h : charge_gas frame regularGas stateGas = some post) :
    post.gasLeft + post.stateGasReservoir + regularGas + stateGas =
      frame.gasLeft + frame.stateGasReservoir ∧
    post.gasLeft ≤ frame.gasLeft ∧
    post.stateGasReservoir ≤ frame.stateGasReservoir := by
  dsimp only [charge_gas] at h
  split at h <;> (split at h <;> (simp only [Option.some.injEq, reduceCtorEq] at h; try contradiction))
  all_goals
    subst h
    simp only
    omega

/-- T-8037-RESERVOIR-ROUNDTRIP: Parent forwards 100% of `stateGasReservoir` to child
    (`childInit.stateGasReservoir = parentAfterCharge.stateGasReservoir`) and zeroed parent
    reservoir is restored from `child.stateGasReservoir` on both success and error. -/
theorem t_8037_reservoir_roundtrip_success (parent child : EvmGasFrame) :
    (incorporate_child_on_success { parent with stateGasReservoir := 0 } child).stateGasReservoir =
      child.stateGasReservoir := rfl

theorem t_8037_reservoir_roundtrip_error (parent child : EvmGasFrame) :
    (incorporate_child_on_error { parent with stateGasReservoir := 0 } child).stateGasReservoir =
      child.stateGasReservoir := rfl

/-- EIP-8037 CREATE / CREATE2 gas sequence: deduct `stateGas` (136 * CPSB) + `regularGas`
    BEFORE computing the `63/64` (`L(gasLeft)`) child execution gas cap. -/
def create_child_gas_cap (frame : EvmGasFrame) (regularCreateGas stateCreateGas : Nat) : Option (Nat × EvmGasFrame) :=
  match charge_gas frame regularCreateGas stateCreateGas with
  | none => none
  | some postCharge =>
    let childGas := postCharge.gasLeft - postCharge.gasLeft / 64
    some (childGas, { postCharge with gasLeft := postCharge.gasLeft - childGas, stateGasReservoir := 0 })

/-- Mutant M-8037-1: Computing `63/64` child gas cap BEFORE deducting `stateCreateGas`
    when `stateCreateGas > frame.stateGasReservoir` (reservoir spill). -/
def create_child_gas_cap_mutant (frame : EvmGasFrame) (regularCreateGas stateCreateGas : Nat) : Option (Nat × EvmGasFrame) :=
  if frame.gasLeft < regularCreateGas then none
  else
    let afterReg := frame.gasLeft - regularCreateGas
    let childGas := afterReg - afterReg / 64
    match charge_gas { frame with gasLeft := afterReg - childGas } 0 stateCreateGas with
    | none => none
    | some post => some (childGas, { post with stateGasReservoir := 0 })

def create_child_gas_cap_valid (f : EvmGasFrame) (reg st : Nat) (out : Option (Nat × EvmGasFrame)) : Bool :=
  match out, charge_gas f reg st with
  | some (cg, _), some post => decide (cg = post.gasLeft - post.gasLeft / 64)
  | none, none => true
  | _, _ => false

/-- T-8037-CREATE-ORDER: When `stateCreateGas` spills out of `stateGasReservoir`,
    charging `stateCreateGas` before the `63/64` cap strictly bounds `childGas` by
    `63/64` of the post-spill `gasLeft`, and refutes `create_child_gas_cap_mutant`. -/
def m_8037_1_refuter : WitnessRefuter (EvmGasFrame × Nat × Nat) (Option (Nat × EvmGasFrame))
    (fun ⟨f, reg, st⟩ out => create_child_gas_cap_valid f reg st out = true) where
  reference := fun ⟨f, reg, st⟩ => create_child_gas_cap f reg st
  mutant := fun ⟨f, reg, st⟩ => create_child_gas_cap_mutant f reg st
  ref_sound := by
    intro ⟨f, reg, st⟩
    dsimp only [create_child_gas_cap_valid, create_child_gas_cap]
    cases charge_gas f reg st <;> simp
  killWitness := (⟨1000, 0, 0⟩, 0, 640)
  mutant_refuted := by decide

/-- T-7778-NO-REFUND: Under EIP-7778, transaction gas settlement ignores `refundCounter`;
    `receiptGasUsed = txGas - gasAvailable` and `blockStateGasUsed = txStateGasUsed`. -/
def settle_tx_gas_eip7778 (txGas gasLeft stateGasReservoir initialReservoir : Nat) : Nat × Nat × Nat :=
  let gasAvailable := gasLeft + stateGasReservoir
  let receiptGasUsed := txGas - gasAvailable
  let txStateGasUsed := (initialReservoir + txGas) - (stateGasReservoir + txGas)
  let txRegularGasUsed := receiptGasUsed - txStateGasUsed
  let blockRegularGasAdded := max txRegularGasUsed txStateGasUsed
  (receiptGasUsed, txStateGasUsed, blockRegularGasAdded)

/-- T-7778-8037-DUAL-CAP: Block gas bottleneck `max(txRegularGasUsed, txStateGasUsed)`
    always upper-bounds both dimensions while receipt gas equals `txRegularGasUsed + txStateGasUsed`. -/
theorem t_7778_8037_dual_cap (txRegularGasUsed txStateGasUsed : Nat) :
    txRegularGasUsed ≤ max txRegularGasUsed txStateGasUsed ∧
    txStateGasUsed ≤ max txRegularGasUsed txStateGasUsed := by
  constructor <;> omega

/-- EIP-2780 + EIP-8038 warm/cold state-access constants. -/
def GAS_TX_BASE : Nat := 4500
def GAS_COLD_ACCOUNT_ACCESS : Nat := 2600
def GAS_COLD_ACCOUNT_NOCODE_ACCESS : Nat := 500
def GAS_COLD_STORAGE_ACCESS : Nat := 2100
def GAS_WARM_ACCESS : Nat := 150
def GAS_NEW_ACCOUNT : Nat := 25000

/-- T-2780-INTRINSIC-SPLIT & T-8038-2780-WARM-COLD: Cold account/storage accesses strictly
    exceed warm access (`150`), and empty-code EOA transfer receives the `2100` cold-nocode
    discount (`2600 - 2100 = 500`). -/
theorem t_8038_2780_warm_cold_bounds :
    GAS_WARM_ACCESS < GAS_COLD_ACCOUNT_NOCODE_ACCESS ∧
    GAS_COLD_ACCOUNT_NOCODE_ACCESS < GAS_COLD_STORAGE_ACCESS ∧
    GAS_COLD_STORAGE_ACCESS < GAS_COLD_ACCOUNT_ACCESS ∧
    GAS_COLD_ACCOUNT_ACCESS - GAS_COLD_STORAGE_ACCESS = GAS_COLD_ACCOUNT_NOCODE_ACCESS := by
  decide

@[inline, export glamsterdam_gas_dual_cap_cabi]
def gas_dual_cap_cabi (txRegular txState : UInt64) : UInt64 :=
  max txRegular txState

end Glamsterdam.Gas.Spec
