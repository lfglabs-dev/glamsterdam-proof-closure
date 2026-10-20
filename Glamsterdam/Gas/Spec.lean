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

/-! ### Exact Pinned Gas Constants (`el_vm_gas.py:39-163` @ `16898000`) -/

def COST_PER_STATE_BYTE : Nat := 1530
def STATE_BYTES_PER_NEW_ACCOUNT : Nat := 120
def STATE_BYTES_PER_STORAGE_SET : Nat := 64
def STATE_BYTES_PER_AUTH_BASE : Nat := 23

def STATE_GAS_NEW_ACCOUNT : Nat := STATE_BYTES_PER_NEW_ACCOUNT * COST_PER_STATE_BYTE -- 183,600
def STATE_GAS_STORAGE_SET : Nat := STATE_BYTES_PER_STORAGE_SET * COST_PER_STATE_BYTE -- 97,920
def STATE_GAS_AUTH_BASE : Nat := STATE_BYTES_PER_AUTH_BASE * COST_PER_STATE_BYTE     -- 35,190

def GAS_WARM_ACCESS : Nat := 100
def GAS_COLD_STORAGE_ACCESS : Nat := 2100
def GAS_COLD_ACCOUNT_ACCESS : Nat := 3000
def GAS_ACCOUNT_WRITE : Nat := 9000
def GAS_STORAGE_WRITE : Nat := 10000
def GAS_CREATE_ACCESS : Nat := GAS_ACCOUNT_WRITE + GAS_COLD_ACCOUNT_ACCESS -- 12,000

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

/-- EIP-8037 CREATE / CREATE2 gas sequence: deduct `stateGas` (`120 * CPSB = 183,600`) + `regularGas`
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

/-- Exact `settle_transaction_gas` (`el_vm_gas.py:1163-1228` @ `16898000`):
    - Sender/receipt `gas_used` applies the `1/5` refund cap (`min(gas_used_before_refund / 5, refund_counter)`)
      and `calldata_floor`.
    - Block `execution_gas_used` (`EIP-7778`) ignores `refund_counter` and takes
      `max(gas_used_before_refund - state_gas_used, calldata_floor)`. -/
structure TxGasSettlement where
  gasUsed : Nat
  executionGasUsed : Nat
  stateGasUsed : Nat
  blockBottleneckGas : Nat
  deriving Repr, DecidableEq, BEq

def settle_transaction_gas (txGas calldataFloor gasLeft stateGasLeft refundCounter stateGasUsed : Nat) :
    TxGasSettlement :=
  let gasUsedBeforeRefund := txGas - gasLeft - stateGasLeft
  let gasRefund := min (gasUsedBeforeRefund / 5) refundCounter
  let gasUsedAfterRefund := gasUsedBeforeRefund - gasRefund
  let gasUsed := max gasUsedAfterRefund calldataFloor
  let executionGasUsed := max (gasUsedBeforeRefund - stateGasUsed) calldataFloor
  let blockBottleneckGas := max executionGasUsed stateGasUsed
  ⟨gasUsed, executionGasUsed, stateGasUsed, blockBottleneckGas⟩

/-- T-7778-8037-DUAL-CAP: Block gas bottleneck `max(executionGasUsed, stateGasUsed)`
    always upper-bounds both dimensions, and block `executionGasUsed` is invariant with
    respect to `refundCounter`. -/
theorem t_7778_8037_dual_cap (txGas floor gasLeft stateGasLeft r1 r2 stateGasUsed : Nat) :
    let s1 := settle_transaction_gas txGas floor gasLeft stateGasLeft r1 stateGasUsed
    let s2 := settle_transaction_gas txGas floor gasLeft stateGasLeft r2 stateGasUsed
    s1.executionGasUsed ≤ s1.blockBottleneckGas ∧
    s1.stateGasUsed ≤ s1.blockBottleneckGas ∧
    s1.executionGasUsed = s2.executionGasUsed := by
  dsimp only [settle_transaction_gas]
  refine ⟨?_, ?_, rfl⟩ <;> omega

/-- T-8038-2780-WARM-COLD: Pinned warm/cold access and write gas bounds (`el_vm_gas.py:47-90`). -/
theorem t_8038_2780_warm_cold_bounds :
    GAS_WARM_ACCESS < GAS_COLD_STORAGE_ACCESS ∧
    GAS_COLD_STORAGE_ACCESS < GAS_COLD_ACCOUNT_ACCESS ∧
    GAS_COLD_ACCOUNT_ACCESS < GAS_ACCOUNT_WRITE ∧
    GAS_CREATE_ACCESS = GAS_ACCOUNT_WRITE + GAS_COLD_ACCOUNT_ACCESS ∧
    STATE_GAS_NEW_ACCOUNT = 183600 ∧
    STATE_GAS_STORAGE_SET = 97920 := by
  decide

@[inline, export glamsterdam_gas_dual_cap_cabi]
def gas_dual_cap_cabi (txRegular txState : UInt64) : UInt64 :=
  max txRegular txState

end Glamsterdam.Gas.Spec
