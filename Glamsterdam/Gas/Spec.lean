/-
Copyright (c) 2026 Verity Labs / LFG Labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Marchand, Verity Audit Team
-/
import Glamsterdam.Common.ElCore

/-!
# Glamsterdam Coupled Gas Model Formal Specification and Verification
(`EIP-8037`, `EIP-8038`, `EIP-2780`, `EIP-7778`)

Pinned against `ethereum/execution-specs` @ `16898000911c1e3caa57be08509536c10ae92d3e`:
- `src/ethereum/forks/amsterdam/vm/gas.py` (`StateGasCosts:39-60`, `GasCosts:63-252`,
  `GasMeter:260-325`, `calculate_message_call_gas:801-844`, `max_message_call_gas:846-861`,
  `init_code_cost:864-883`, `check_block_gas_capacity:1038-1089`,
  `allocate_evm_gas:1105-1138`, `settle_transaction_gas:1163-1228`)
- `src/ethereum/forks/amsterdam/transactions.py` (`calculate_intrinsic_cost:687-796`,
  `validate_transaction:587-684`, `count_tokens_in_data:799-809`)
- `src/ethereum/forks/amsterdam/vm/instructions/storage.py` (`sload:37-66`, `sstore:68-162`)
- `src/ethereum/forks/amsterdam/vm/instructions/system.py` (`generic_create:59-186`, `call:465-590`)
- `src/ethereum/forks/amsterdam/vm/eoa_delegation.py` (`set_delegation:231-321`)
-/

namespace Glamsterdam.Gas.Spec

open Glamsterdam.Common.Prelude
open Glamsterdam.Common.MetaSpec
open Glamsterdam.Common.ElCore

/-! ## 1. Exact Pinned Gas Constants (`src/ethereum/forks/amsterdam/vm/gas.py:39-255` @ `16898000`) -/

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
def GAS_CALL_STIPEND : Nat := 2300
def GAS_CALL_VALUE : Nat := GAS_ACCOUNT_WRITE + GAS_CALL_STIPEND -- 11,300
def GAS_CODE_INIT_PER_WORD : Nat := 2
def GAS_CREATE_ACCESS : Nat := GAS_ACCOUNT_WRITE + GAS_COLD_ACCOUNT_ACCESS -- 12,000
def GAS_REFUND_STORAGE_CLEAR : Nat := (GAS_STORAGE_WRITE + GAS_COLD_STORAGE_ACCESS) * 4800 / 5000 -- 11,616

def GAS_TX_BASE : Nat := 12000
def GAS_TX_VALUE_COST : Nat := 6000
def GAS_TX_DATA_TOKEN_STANDARD : Nat := 4
def GAS_TX_DATA_TOKEN_FLOOR : Nat := 16
def GAS_TX_ACCESS_LIST_ADDRESS : Nat := GAS_COLD_ACCOUNT_ACCESS - GAS_WARM_ACCESS -- 2,900
def GAS_TX_ACCESS_LIST_STORAGE_KEY : Nat := GAS_COLD_STORAGE_ACCESS - GAS_WARM_ACCESS -- 2,000
def ACCESS_LIST_ADDRESS_FLOOR_TOKENS : Nat := 80
def ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS : Nat := 128

def TX_MAX_GAS_LIMIT : Nat := 16777216
def TX_MAX_TOTAL_GAS_LIMIT : Nat := 4294967295
def GAS_AUTH_TUPLE_BYTES : Nat := 101
def GAS_PRECOMPILE_ECRECOVER : Nat := 3000
def GAS_EXECUTION_PER_AUTH_BASE_COST : Nat :=
  GAS_AUTH_TUPLE_BYTES * GAS_TX_DATA_TOKEN_FLOOR + GAS_PRECOMPILE_ECRECOVER +
    GAS_COLD_ACCOUNT_ACCESS + 2 * GAS_WARM_ACCESS -- 7,816

def MAX_BLOB_GAS_PER_BLOCK : Nat := 21 * 131072 -- 2,752,512

/-! ## 2. Two-Leg Gas Charging & Reservoir Forwarding (`T-8037-CHARGE-GAS-SOUND` & `T-8037-RESERVOIR-ROUNDTRIP`) -/

/--
**Two-dimensional gas charging conservation and monotonicity (T-8037-CHARGE-GAS-SOUND)**
- *Natural property:* Whenever a coupled execution-gas and state-gas charge succeeds, the sum of execution gas and reservoir gas drops by the exact combined charge and neither counter increases or underflows.
- *Formal statement:* `charge_gas frame regularGas stateGas = some post` implies `post.gasLeft + post.stateGasReservoir + regularGas + stateGas = frame.gasLeft + frame.stateGasReservoir ∧ post.gasLeft ≤ frame.gasLeft ∧ post.stateGasReservoir ≤ frame.stateGasReservoir`.
- *Scope note:* Single-step accounting on `EvmGasFrame` (`vm/gas.py:379-436`).
-/
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

/--
**State-gas reservoir roundtrip on child success (T-8037-RESERVOIR-ROUNDTRIP)**
- *Natural property:* A parent frame whose state-gas reservoir was drained into a child frame adopts the child's remaining reservoir intact when the child succeeds.
- *Formal statement:* `(incorporate_child_on_success { parent with stateGasReservoir := 0 } child).stateGasReservoir = child.stateGasReservoir`.
- *Scope note:* Frame-boundary reservoir handoff on `EvmGasFrame`; full 6-field `GasMeter` spill rollback on revert is proved in `t_8037_meter_reservoir_roundtrip_on_revert`.
-/
theorem t_8037_reservoir_roundtrip_success (parent child : EvmGasFrame) :
    (incorporate_child_on_success { parent with stateGasReservoir := 0 } child).stateGasReservoir =
      child.stateGasReservoir := rfl

/--
**State-gas reservoir roundtrip on child error (T-8037-RESERVOIR-ROUNDTRIP-ERROR)**
- *Natural property:* A parent frame whose state-gas reservoir was drained into a child frame recovers the child's restored reservoir intact when the child fails.
- *Formal statement:* `(incorporate_child_on_error { parent with stateGasReservoir := 0 } child).stateGasReservoir = child.stateGasReservoir`.
- *Scope note:* Frame-boundary error handoff on `EvmGasFrame`.
-/
theorem t_8037_reservoir_roundtrip_error (parent child : EvmGasFrame) :
    (incorporate_child_on_error { parent with stateGasReservoir := 0 } child).stateGasReservoir =
      child.stateGasReservoir := rfl

/--
**Six-field GasMeter reservoir and spill restoration on child revert (T-8037-METER-RESERVOIR-ROUNDTRIP-REVERT)**
- *Natural property:* When a parent drains its reservoir into a child frame, the child charges state gas (even spilling into execution gas), and the child reverts, the parent's execution gas, state-gas reservoir, spill counter, and refund counter all return to their exact pre-call values.
- *Formal statement:* After `drain_state_gas_reservoir`, `charge_state_gas_from_meter ... childStateCharge = some childAfterCharge`, `restore_state_gas`, and `incorporate_child_meter ... true`, `parentFinal.stateGasLeft = parent.stateGasLeft ∧ parentFinal.gasLeft = parent.gasLeft ∧ parentFinal.stateGasSpilled = parent.stateGasSpilled ∧ parentFinal.refundCounter = parent.refundCounter`.
- *Scope note:* Single parent-child revert roundtrip on the 6-field `GasMeter` (`vm/gas.py:493-517, 689-710`) with zero child execution-gas burn; execution-gas burn before revert is modeled in `Glamsterdam.Gas.CallTree`.
-/
theorem t_8037_meter_reservoir_roundtrip_on_revert
    (parent childAfterCharge : GasMeter) (childGrant childStateCharge : Nat)
    (h_withhold : childGrant ≤ parent.gasLeft)
    (h_charge :
      charge_state_gas_from_meter
        { gasLeft := childGrant
          stateGasLeft := parent.stateGasLeft
          stateGasBaseline := parent.stateGasLeft }
        childStateCharge = some childAfterCharge) :
    let (_, parentAfterDrain) := drain_state_gas_reservoir { parent with gasLeft := parent.gasLeft - childGrant }
    let childRestored := restore_state_gas childAfterCharge
    let parentFinal := incorporate_child_meter parentAfterDrain childRestored true
    parentFinal.stateGasLeft = parent.stateGasLeft ∧
    parentFinal.gasLeft = parent.gasLeft ∧
    parentFinal.stateGasSpilled = parent.stateGasSpilled ∧
    parentFinal.refundCounter = parent.refundCounter := by
  dsimp only [charge_state_gas_from_meter] at h_charge
  split at h_charge <;> (try split at h_charge) <;> try contradiction
  all_goals
    simp only [Option.some.injEq] at h_charge
    subst h_charge
    simp only [drain_state_gas_reservoir, restore_state_gas, incorporate_child_meter,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by omega, by omega, by omega, by omega⟩

/-! ## 3. Exact `CREATE*` and `CALL*` Child Gas Grant (`vm/gas.py:801-883` & `system.py:107-127`) -/

/-- Exact `init_code_cost` (`vm/gas.py:864-883`):
`GasCosts.CODE_INIT_PER_WORD * ceil32(init_code_length) // 32`. -/
@[simp]
def init_code_cost (initCodeLength : Nat) : Nat :=
  GAS_CODE_INIT_PER_WORD * ceil32 initCodeLength / 32

/-- Exact `MessageCallGas` (`vm/gas.py:344-360`). -/
structure MessageCallGas where
  cost : Nat
  subCall : Nat
  deriving Repr, DecidableEq, BEq

/-- Exact `calculate_message_call_gas` (`vm/gas.py:801-844`):
- `call_stipend = 0 if value == 0 else call_stipend`
- if `gas_left < extra_gas + memory_cost`, returns `(gas + extra_gas, gas + call_stipend)`
  (which causes the subsequent `charge_gas(message_call_gas.cost + memory_cost)` to raise `OutOfGasError`);
- otherwise caps `gas = min(gas, max_message_call_gas(gas_left - memory_cost - extra_gas))`
  and returns `(gas + extra_gas, gas + call_stipend)`. -/
def calculate_message_call_gas
    (value gas gasLeft memoryCost extraGas : Nat)
    (callStipend : Nat := GAS_CALL_STIPEND) : MessageCallGas :=
  let stipend := if value == 0 then 0 else callStipend
  if gasLeft < extraGas + memoryCost then
    ⟨gas + extraGas, gas + stipend⟩
  else
    let cappedGas := min gas (max_message_call_gas (gasLeft - memoryCost - extraGas))
    ⟨cappedGas + extraGas, cappedGas + stipend⟩

/--
**Message-call gas cap affordability and OOG trigger**
- *Natural property:* Whenever a frame can afford a call's extra gas and memory expansion cost, `calculate_message_call_gas` caps the call cost within `gasLeft`; otherwise it returns an uncapped cost that deterministically triggers `OutOfGasError` on the subsequent charge.
- *Formal statement:* `(extraGas + memoryCost ≤ gasLeft → cost + memoryCost ≤ gasLeft) ∧ (gasLeft < extraGas + memoryCost → cost = gas + extraGas)`.
- *Scope note:* Single-call gas calculation (`vm/gas.py:801-844`) enforcing the EIP-150 `63/64` cap (`max_message_call_gas`).
-/
theorem calculate_message_call_gas_affordable
    (value gas gasLeft memoryCost extraGas stipend : Nat) :
    (extraGas + memoryCost ≤ gasLeft →
      (calculate_message_call_gas value gas gasLeft memoryCost extraGas stipend).cost + memoryCost ≤
        gasLeft) ∧
    (gasLeft < extraGas + memoryCost →
      (calculate_message_call_gas value gas gasLeft memoryCost extraGas stipend).cost =
        gas + extraGas) := by
  unfold calculate_message_call_gas max_message_call_gas
  constructor
  · intro h_afford
    have h_not_lt : ¬ (gasLeft < extraGas + memoryCost) := by omega
    simp [h_not_lt]
    omega
  · intro h_lt
    simp [h_lt]

/-- EIP-8037 CREATE / CREATE2 gas sequence (`system.py:107-113`): deduct `stateGas`
(`120 * CPSB = 183,600`) + `regularGas` BEFORE computing `withhold_create_gas` (`63/64` cap). -/
def create_child_gas_cap (frame : EvmGasFrame) (regularCreateGas stateCreateGas : Nat) :
    Option (Nat × EvmGasFrame) :=
  match charge_gas frame regularCreateGas stateCreateGas with
  | none => none
  | some postCharge =>
    let childGas := postCharge.gasLeft - postCharge.gasLeft / 64
    some (childGas, { postCharge with gasLeft := postCharge.gasLeft - childGas, stateGasReservoir := 0 })

/-- Mutant M-8037-1: Computing `63/64` child gas cap BEFORE deducting `stateCreateGas`
when `stateCreateGas > frame.stateGasReservoir` (reservoir spill). -/
def create_child_gas_cap_mutant (frame : EvmGasFrame) (regularCreateGas stateCreateGas : Nat) :
    Option (Nat × EvmGasFrame) :=
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

/--
**CREATE state-gas charge ordering before the 63/64 child cap (T-8037-CREATE-ORDER)**
- *Natural property:* `CREATE` and `CREATE2` deduct `stateCreateGas` (`183,600`) before computing the `63/64` child execution-gas cap, preventing a reservoir spill from over-granting execution gas to `init_code`.
- *Formal statement:* `WitnessRefuter` proving `create_child_gas_cap` satisfies `cg = post.gasLeft - post.gasLeft / 64` after `charge_gas f reg st = some post`, while `create_child_gas_cap_mutant` fails on `(⟨1000, 0, 0⟩, 0, 640)`.
- *Scope note:* Single `CREATE`/`CREATE2` spawn step (`vm/instructions/system.py:107-113`).
-/
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

/-! ## 4. Exact Intrinsic Gas, `allocate_evm_gas`, `check_block_gas_capacity`, and `settle_transaction_gas`
(`transactions.py:687-796`, `vm/gas.py:1038-1228`) -/

/-- Input summary of a transaction for `calculate_intrinsic_cost` (`transactions.py:687-796`). -/
structure TxIntrinsicInput where
  zeroDataBytes : Nat
  nonZeroDataBytes : Nat
  isCreate : Bool
  isSelfTransfer : Bool
  hasPositiveValue : Bool
  accessListAddresses : Nat
  accessListStorageKeys : Nat
  authCount : Nat
  deriving Repr, DecidableEq, BEq

/-- Exact `IntrinsicGasCost` (`transactions.py:42-56`). -/
structure IntrinsicGasCost where
  execution : Nat
  calldataFloor : Nat
  deriving Repr, DecidableEq, BEq

/-- Exact `calculate_intrinsic_cost` (`transactions.py:687-796`):
- `tokens_in_calldata = zeroDataBytes + nonZeroDataBytes * 4`
- `data_cost = tokens_in_calldata * 4`
- `recipient_execution_gas`:
  - if `isCreate`: `CREATE_ACCESS` (`12,000`) and `init_code_gas = init_code_cost(dataLen)`
  - else if `!isSelfTransfer`: `COLD_ACCOUNT_ACCESS` (`3,000`) + (`TX_VALUE_COST` (`6,000`) if `hasPositiveValue`)
  - else (`isSelfTransfer` and `!isCreate`): `0`
- `access_list_cost = accessListAddresses * 2900 + accessListStorageKeys * 2000`
- `access_list_data_cost = (accessListAddresses * 80 + accessListStorageKeys * 128) * 16`
- `auth_cost = authCount * 7816`
- `base_execution_gas = TX_BASE (12,000) + recipient_execution_gas`
- `calldata_floor = base_execution_gas + dataLen * 4 * 16 + access_list_data_cost`
- `execution = base_execution_gas + init_code_gas + data_cost + access_list_cost + access_list_data_cost + auth_cost`. -/
def calculate_intrinsic_cost (tx : TxIntrinsicInput) : IntrinsicGasCost :=
  let dataLen := tx.zeroDataBytes + tx.nonZeroDataBytes
  let tokensInCalldata := tx.zeroDataBytes + tx.nonZeroDataBytes * 4
  let dataCost := tokensInCalldata * GAS_TX_DATA_TOKEN_STANDARD
  let recipientExecutionGas :=
    if tx.isCreate then
      GAS_CREATE_ACCESS
    else if !tx.isSelfTransfer then
      GAS_COLD_ACCOUNT_ACCESS + (if tx.hasPositiveValue then GAS_TX_VALUE_COST else 0)
    else
      0
  let initCodeGas := if tx.isCreate then init_code_cost dataLen else 0
  let accessListCost :=
    tx.accessListAddresses * GAS_TX_ACCESS_LIST_ADDRESS +
      tx.accessListStorageKeys * GAS_TX_ACCESS_LIST_STORAGE_KEY
  let tokensInAccessList :=
    tx.accessListAddresses * ACCESS_LIST_ADDRESS_FLOOR_TOKENS +
      tx.accessListStorageKeys * ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS
  let accessListDataCost := tokensInAccessList * GAS_TX_DATA_TOKEN_FLOOR
  let authCost := tx.authCount * GAS_EXECUTION_PER_AUTH_BASE_COST
  let floorTokensInCalldata := dataLen * GAS_TX_DATA_TOKEN_STANDARD
  let baseExecutionGas := GAS_TX_BASE + recipientExecutionGas
  let dataFloorGasCost :=
    baseExecutionGas + floorTokensInCalldata * GAS_TX_DATA_TOKEN_FLOOR + accessListDataCost
  { execution :=
      baseExecutionGas + initCodeGas + dataCost + accessListCost + accessListDataCost + authCost
    calldataFloor := dataFloorGasCost }

/-- Exact `EvmGasAllocation` (`vm/gas.py:1093-1103`). -/
structure EvmGasAllocation where
  executionGas : Nat
  stateGasReservoir : Nat
  deriving Repr, DecidableEq, BEq

/-- Exact `allocate_evm_gas` (`vm/gas.py:1105-1138`):
Splits `txGas - intrinsic.execution` into `executionGas = min(TX_MAX_GAS_LIMIT - intrinsic.execution, evmGas)`
and `stateGasReservoir = evmGas - executionGas`. -/
def allocate_evm_gas (txGas : Nat) (intrinsic : IntrinsicGasCost) : EvmGasAllocation :=
  let evmGas := txGas - intrinsic.execution
  let executionGasBudget := TX_MAX_GAS_LIMIT - intrinsic.execution
  let executionGas := min executionGasBudget evmGas
  let stateGasReservoir := evmGas - executionGas
  ⟨executionGas, stateGasReservoir⟩

/--
**Transaction gas split between execution budget and state-gas reservoir (T-8037-ALLOCATE-EVM-GAS-SOUND)**
- *Natural property:* For any valid transaction, `allocate_evm_gas` partitions `txGas` without loss or overflow into intrinsic execution gas, the EVM execution budget (bounded so total execution gas never exceeds `TX_MAX_GAS_LIMIT = 2^24`), and the state-gas reservoir.
- *Formal statement:* Given `intrinsic.execution ≤ txGas` and `intrinsic.execution ≤ TX_MAX_GAS_LIMIT`, `intrinsic.execution + alloc.executionGas + alloc.stateGasReservoir = txGas ∧ intrinsic.execution + alloc.executionGas ≤ TX_MAX_GAS_LIMIT`.
- *Scope note:* Transaction-entry allocation (`vm/gas.py:1105-1138`) under `validate_transaction` preconditions.
-/
theorem t_8037_allocate_evm_gas_sound (txGas : Nat) (intrinsic : IntrinsicGasCost)
    (h_gas : intrinsic.execution ≤ txGas)
    (h_cap : intrinsic.execution ≤ TX_MAX_GAS_LIMIT) :
    let alloc := allocate_evm_gas txGas intrinsic
    intrinsic.execution + alloc.executionGas + alloc.stateGasReservoir = txGas ∧
    intrinsic.execution + alloc.executionGas ≤ TX_MAX_GAS_LIMIT := by
  unfold allocate_evm_gas
  simp only
  omega

/-- Exact `check_block_gas_capacity` (`vm/gas.py:1038-1089`). -/
def check_block_gas_capacity
    (blockGasLimit blockGasUsed blockStateGasUsed blobGasUsed txGas txBlobGas : Nat) : Bool :=
  let executionGasAvailable := blockGasLimit - blockGasUsed
  let stateGasAvailable := blockGasLimit - blockStateGasUsed
  let blobGasAvailable := MAX_BLOB_GAS_PER_BLOCK - blobGasUsed
  decide (min TX_MAX_GAS_LIMIT txGas ≤ executionGasAvailable) &&
    decide (txGas ≤ stateGasAvailable) &&
    decide (txBlobGas ≤ blobGasAvailable)

/-- Exact `settle_transaction_gas` (`vm/gas.py:1163-1228` @ `16898000`):
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

/-- Exact signed `state_gas_used : Int` variant of `settle_transaction_gas` (`vm/gas.py:1163-1228`),
clamping `settled_state_gas_used = max(0, state_gas_used)`. -/
def settle_transaction_gas_int
    (txGas calldataFloor gasLeft stateGasLeft refundCounter : Nat) (stateGasUsed : Int) :
    TxGasSettlement :=
  settle_transaction_gas txGas calldataFloor gasLeft stateGasLeft refundCounter stateGasUsed.toNat

/--
**EIP-7778 / EIP-8037 dual block gas bottleneck and refund invariance (T-7778-8037-DUAL-CAP)**
- *Natural property:* At transaction settlement, the block bottleneck gas `max(executionGasUsed, stateGasUsed)` upper-bounds both gas dimensions, and block `executionGasUsed` is completely invariant to `refundCounter`.
- *Formal statement:* `s1.executionGasUsed ≤ s1.blockBottleneckGas ∧ s1.stateGasUsed ≤ s1.blockBottleneckGas ∧ s1.executionGasUsed = s2.executionGasUsed` for any refund counters `r1, r2`.
- *Scope note:* Transaction-level settlement (`vm/gas.py:1163-1228`); sender receipt `gasUsed` still applies the `1/5` refund cap.
-/
theorem t_7778_8037_dual_cap (txGas floor gasLeft stateGasLeft r1 r2 stateGasUsed : Nat) :
    let s1 := settle_transaction_gas txGas floor gasLeft stateGasLeft r1 stateGasUsed
    let s2 := settle_transaction_gas txGas floor gasLeft stateGasLeft r2 stateGasUsed
    s1.executionGasUsed ≤ s1.blockBottleneckGas ∧
    s1.stateGasUsed ≤ s1.blockBottleneckGas ∧
    s1.executionGasUsed = s2.executionGasUsed := by
  dsimp only [settle_transaction_gas]
  refine ⟨?_, ?_, rfl⟩ <;> omega

/--
**EIP-8038 / EIP-2780 warm-cold access ordering and state-byte pricing constants (T-8038-2780-WARM-COLD)**
- *Natural property:* Pinned Amsterdam gas constants strictly order warm access (`100`) below cold storage access (`2,100`), cold account access (`3,000`), and account write (`9,000`), and match the derived creation and storage-set state-gas schedules.
- *Formal statement:* `GAS_WARM_ACCESS < GAS_COLD_STORAGE_ACCESS < GAS_COLD_ACCOUNT_ACCESS < GAS_ACCOUNT_WRITE ∧ GAS_CREATE_ACCESS = 12000 ∧ STATE_GAS_NEW_ACCOUNT = 183600 ∧ STATE_GAS_STORAGE_SET = 97920`.
- *Scope note:* Constant-schedule verification against `vm/gas.py:47-90` (`COST_PER_STATE_BYTE = 1,530`).
-/
theorem t_8038_2780_warm_cold_bounds :
    GAS_WARM_ACCESS < GAS_COLD_STORAGE_ACCESS ∧
    GAS_COLD_STORAGE_ACCESS < GAS_COLD_ACCOUNT_ACCESS ∧
    GAS_COLD_ACCOUNT_ACCESS < GAS_ACCOUNT_WRITE ∧
    GAS_CREATE_ACCESS = 12000 ∧
    STATE_GAS_NEW_ACCOUNT = 183600 ∧
    STATE_GAS_STORAGE_SET = 97920 := by
  decide

/-! ## 5. Exact `sstore` Transcription (`vm/instructions/storage.py:68-162`) and
    Refuter for `F-8038-7778-SSTORE-RESET-REFUND-CAP-AND-BLOCK-GAS` -/

/-- Outcome of the gas and refund calculations in `sstore` (`storage.py:88-157`). -/
structure SstorePricing where
  execGasCost : Nat
  stateGasCost : Nat
  refundDelta : Int
  stateGasRefundCredited : Nat
  deriving Repr, DecidableEq, BEq

/-- Exact `sstore` pricing (`vm/instructions/storage.py:68-162`):
- `accessCost = 2100` if cold else `100`.
- `writeCost = 10000` (`STORAGE_WRITE`) if `originalValue == currentValue && currentValue != newValue` else `0`.
- `refundDelta`:
  - if `currentValue != newValue`:
    - `+ 11616` (`REFUND_STORAGE_CLEAR`) if `originalValue != 0 && currentValue != 0 && newValue == 0`
    - `- 11616` if `originalValue != 0 && currentValue == 0`
    - `+ 10000` (`STORAGE_WRITE`) if `originalValue == newValue`
- `stateGasCost = 97920` (`STORAGE_SET`) if `originalValue == currentValue && currentValue != newValue && originalValue == 0`
- `stateGasRefundCredited = 97920` (`STORAGE_SET`) if `currentValue != newValue && originalValue == newValue && originalValue == 0`. -/
def price_sstore (isCold : Bool) (originalValue currentValue newValue : Nat) : SstorePricing :=
  let accessCost := if isCold then GAS_COLD_STORAGE_ACCESS else GAS_WARM_ACCESS
  let writeCost :=
    if originalValue == currentValue && currentValue != newValue then GAS_STORAGE_WRITE else 0
  let clearRefund : Int :=
    if currentValue != newValue then
      let r1 : Int :=
        if originalValue != 0 && currentValue != 0 && newValue == 0 then
          (GAS_REFUND_STORAGE_CLEAR : Int)
        else 0
      let r2 : Int :=
        if originalValue != 0 && currentValue == 0 then
          -(GAS_REFUND_STORAGE_CLEAR : Int)
        else 0
      let r3 : Int :=
        if originalValue == newValue then
          (GAS_STORAGE_WRITE : Int)
        else 0
      r1 + r2 + r3
    else 0
  let stateGasCost :=
    if originalValue == currentValue && currentValue != newValue && originalValue == 0 then
      STATE_GAS_STORAGE_SET
    else 0
  let stateGasRefundCredited :=
    if currentValue != newValue && originalValue == newValue && originalValue == 0 then
      STATE_GAS_STORAGE_SET
    else 0
  { execGasCost := accessCost + writeCost
    stateGasCost := stateGasCost
    refundDelta := clearRefund
    stateGasRefundCredited := stateGasRefundCredited }

/-- Dirty-reset sequence (`0 -> X -> 0` in the same transaction on a warm slot after initial write):
1. First `SSTORE(key, 1)` (warm): charges `100 + 10000 = 10,100` execution gas and `97,920` state gas.
2. Second `SSTORE(key, 0)` (warm): charges `100` execution gas, credits `97,920` back to `GasMeter` via
   `credit_state_gas_refund`, and puts `10,000` (`STORAGE_WRITE`) into `refund_counter`.
Under `settle_transaction_gas` (`vm/gas.py:1211-1222`):
- `gas_used_before_refund = baseTxExecGas + 10100 + 100 = baseTxExecGas + 10200` (because the `97,920`
  state gas was restored directly into `state_gas_left` / `gas_left`).
- `gas_refund = min((baseTxExecGas + 10200) / 5, 10000)`.
- Whenever `baseTxExecGas < 39800` (e.g., `baseTxExecGas = 15000`, a standard 1-call tx),
  `gas_refund = (15000 + 10200) / 5 = 5040 < 10000`, so `4,960` of the temporary `STORAGE_WRITE`
  charge is permanently lost to the 20% refund cap!
- Furthermore, `execution_gas_used` ignores `refund_counter` completely (`vm/gas.py:1217-1222`),
  charging `baseTxExecGas + 10200` to the block limit instead of `baseTxExecGas + 200` (violating
  `eip-7778.md:43`: "Storage discounts that reflect actual reduced computational work (e.g., warm
  storage access, reverting to original values) remain applied to block gas accounting"). -/
def sstore_dirty_reset_settlement_v16898000 (baseTxExecGas : Nat) : TxGasSettlement :=
  let p1 := price_sstore false 0 0 1
  let p2 := price_sstore false 0 1 0
  let totalExecCharged := baseTxExecGas + p1.execGasCost + p2.execGasCost
  let netStateGas := p1.stateGasCost - p2.stateGasRefundCredited
  let refundCounter := (p1.refundDelta + p2.refundDelta).toNat
  settle_transaction_gas totalExecCharged 0 0 0 refundCounter netStateGas

/-- EIP-7778 compliant dirty-reset settlement where `STORAGE_WRITE` (`10,000`) on a `0 -> X -> 0`
reset is credited directly (like `credit_state_gas_refund`) rather than routed through the capped
and block-ignored `refund_counter`. -/
def sstore_dirty_reset_settlement_direct (baseTxExecGas : Nat) : TxGasSettlement :=
  let p1 := price_sstore false 0 0 1
  let p2 := price_sstore false 0 1 0
  let netExecCharged := baseTxExecGas + p1.execGasCost + p2.execGasCost - GAS_STORAGE_WRITE
  let netStateGas := p1.stateGasCost - p2.stateGasRefundCredited
  settle_transaction_gas netExecCharged 0 0 0 0 netStateGas

/--
**Counterexample refuter: SSTORE 0 -> X -> 0 reset routed through capped refund_counter (F-8038-7778-SSTORE-RESET-REFUND-CAP-AND-BLOCK-GAS)**
- *Natural property:* On a same-transaction warm `0 -> 1 -> 0` dirty reset, state gas (`97,920`) is refilled directly, whereas the `10,000` `STORAGE_WRITE` reset credit goes into `refund_counter`, where the `1/5` refund cap can clip it for the sender and EIP-7778 omits it from block `execution_gas_used`.
- *Formal statement:* `WitnessRefuter` at `baseTxExecGas = 15000` showing `sstore_dirty_reset_settlement_v16898000 15000` charges `gasUsed = 20160` and `executionGasUsed = 25200` instead of `15200`.
- *Scope note:* Two-write `SSTORE` settlement trace (`vm/instructions/storage.py:68-162` and `vm/gas.py:1211-1222`).
-/
def f_8038_7778_sstore_reset_refuter :
    WitnessRefuter Nat TxGasSettlement
      (fun baseTx out => out.gasUsed = baseTx + 200 ∧ out.executionGasUsed = baseTx + 200) where
  reference := sstore_dirty_reset_settlement_direct
  mutant := sstore_dirty_reset_settlement_v16898000
  ref_sound := by
    intro baseTx
    dsimp [sstore_dirty_reset_settlement_direct, price_sstore, settle_transaction_gas,
      GAS_WARM_ACCESS, GAS_STORAGE_WRITE, STATE_GAS_STORAGE_SET,
      STATE_BYTES_PER_STORAGE_SET, COST_PER_STATE_BYTE]
    omega
  killWitness := 15000
  mutant_refuted := by decide

/-- Potential function $\Phi(\text{orig}, \text{curr}) = R_{\text{clear}} \cdot [\text{orig} \neq 0 \wedge \text{curr} = 0] \ge 0$
for `sstore` clear refunds (`src/ethereum/forks/amsterdam/vm/instructions/storage.py:126-139` @ `16898000`
and `EvmGasSemantics/Rules/Storage.lean:25-35` in `fradamt/evm-gas-semantics-lean`). -/
@[simp]
def sstore_clear_potential (originalValue currentValue : Nat) : Int :=
  if originalValue != 0 && currentValue == 0 then
    (GAS_REFUND_STORAGE_CLEAR : Int)
  else
    0

/--
**Telescoping potential decomposition for single-step SSTORE refund deltas**
- *Natural property:* Every `SSTORE` refund delta decomposes into the exact change in a non-negative clear potential plus a non-negative `STORAGE_WRITE` reset bonus, so `refundCounter - sstore_clear_potential orig curr` never decreases across any `SSTORE`.
- *Formal statement:* `p.refundDelta = (sstore_clear_potential originalValue newValue - sstore_clear_potential originalValue currentValue) + resetBonus` with `resetBonus ≥ 0`, `sstore_clear_potential originalValue newValue ≥ 0`, and `sstore_clear_potential originalValue originalValue = 0`.
- *Scope note:* Single-slot `SSTORE` pricing (`vm/instructions/storage.py:126-139`); lifts to multi-step traces by telescoping summation across independent slots.
-/
theorem t_8038_sstore_refund_delta_potential
    (isCold : Bool) (originalValue currentValue newValue : Nat) :
    let p := price_sstore isCold originalValue currentValue newValue
    let resetBonus : Int :=
      if currentValue != newValue && originalValue == newValue then (GAS_STORAGE_WRITE : Int) else 0
    p.refundDelta =
      (sstore_clear_potential originalValue newValue - sstore_clear_potential originalValue currentValue) +
        resetBonus ∧
    resetBonus ≥ 0 ∧
    sstore_clear_potential originalValue newValue ≥ 0 ∧
    sstore_clear_potential originalValue originalValue = 0 := by
  dsimp only [price_sstore, sstore_clear_potential, GAS_REFUND_STORAGE_CLEAR,
    GAS_STORAGE_WRITE, GAS_COLD_STORAGE_ACCESS]
  by_cases h_orig : originalValue = 0 <;>
    by_cases h_curr : currentValue = 0 <;>
    by_cases h_new : newValue = 0 <;>
    by_cases h_cn : currentValue = newValue <;>
    by_cases h_on : originalValue = newValue <;>
    simp [h_orig, h_curr, h_new, h_cn, h_on] <;>
    omega

/--
**Two-step SSTORE refund-counter non-negativity with negative child delta**
- *Natural property:* Although a child frame re-dirtying an originally non-zero cleared slot incurs a negative local `refundDelta` (`-11,616` or `-1,616`), merging it with the parent's prior clear (`+11,616`) keeps the transaction-wide `refundCounter` non-negative.
- *Formal statement:* If `r0 ≥ sstore_clear_potential orig orig`, two steps `orig -> v1 -> v2` satisfy `r0 + d1 + d2 ≥ sstore_clear_potential orig v2 ≥ 0`, while `(price_sstore false 1 0 2).refundDelta = -11616` and `(price_sstore false 1 0 1).refundDelta = -1616`.
- *Scope note:* Two-step single-slot lemma; generalized to arbitrary trace lengths and reverting children in `t_8038_refund_counter_telescope_trace_root_nonneg`.
-/
theorem t_8038_refund_counter_telescope_nonneg
    (isCold1 isCold2 : Bool) (orig v1 v2 : Nat) (r0 : Int)
    (h_inv0 : r0 ≥ sstore_clear_potential orig orig) :
    let d1 := (price_sstore isCold1 orig orig v1).refundDelta
    let d2 := (price_sstore isCold2 orig v1 v2).refundDelta
    (r0 + d1 ≥ sstore_clear_potential orig v1 ∧ sstore_clear_potential orig v1 ≥ 0) ∧
    (r0 + d1 + d2 ≥ sstore_clear_potential orig v2 ∧ sstore_clear_potential orig v2 ≥ 0) ∧
    (price_sstore false 1 0 2).refundDelta = -11616 ∧
    (price_sstore false 1 0 1).refundDelta = -1616 := by
  have h_step1 := t_8038_sstore_refund_delta_potential isCold1 orig orig v1
  have h_step2 := t_8038_sstore_refund_delta_potential isCold2 orig v1 v2
  refine ⟨⟨by omega, h_step1.2.2.1⟩, ⟨by omega, h_step2.2.2.1⟩, by decide, by decide⟩

/-- Inductive step of a single-slot multi-frame `SSTORE` trace:
- `sstore isCold newVal`: performs `SSTORE` to `newVal` and adds `refundDelta` to `refundCounter`.
- `revertedChild childWrites`: executes a child frame that performs `childWrites` and then reverts
  or halts (`restore_state_gas` zeroes `child.refundCounter` and `restore_tx_state` rolls back
  `currentValue` to the pre-child value). -/
inductive SstoreTraceStep where
  | sstore (isCold : Bool) (newVal : Nat)
  | revertedChild (childWrites : List (Bool × Nat))
  deriving Repr, DecidableEq, BEq

/-- Execute a `List SstoreTraceStep` starting from `(currVal, refundCounter)` with transaction-original
slot value `origVal`. -/
def run_sstore_refund_trace (origVal : Nat) : List SstoreTraceStep → Nat × Int → Nat × Int
  | [], st => st
  | (.sstore isCold newVal) :: rest, (currVal, r) =>
    let d := (price_sstore isCold origVal currVal newVal).refundDelta
    run_sstore_refund_trace origVal rest (newVal, r + d)
  | (.revertedChild _) :: rest, (currVal, r) =>
    run_sstore_refund_trace origVal rest (currVal, r)

/--
**Inductive potential invariant across multi-frame SSTORE traces**
- *Natural property:* Any sequence of committed `SSTORE` steps and reverted/halted child frames preserves the lower bound `refundCounter ≥ sstore_clear_potential orig curr ≥ 0`.
- *Formal statement:* Given `r ≥ sstore_clear_potential orig curr`, `let (curr', r') := run_sstore_refund_trace orig trace (curr, r)` satisfies `r' ≥ sstore_clear_potential orig curr' ∧ sstore_clear_potential orig curr' ≥ 0`.
- *Scope note:* Single-slot `SstoreTraceStep` trace model; successful child frames fold into `.sstore` steps by associativity of integer addition.
-/
theorem t_8038_refund_counter_telescope_trace_inv
    (orig : Nat) (trace : List SstoreTraceStep) (curr : Nat) (r : Int)
    (h_inv : r ≥ sstore_clear_potential orig curr) :
    let (curr', r') := run_sstore_refund_trace orig trace (curr, r)
    r' ≥ sstore_clear_potential orig curr' ∧ sstore_clear_potential orig curr' ≥ 0 := by
  induction trace generalizing curr r with
  | nil =>
    dsimp [run_sstore_refund_trace]
    have h_nonneg := (t_8038_sstore_refund_delta_potential false orig curr curr).2.2.1
    exact ⟨h_inv, h_nonneg⟩
  | cons step rest ih =>
    cases step with
    | sstore isCold newVal =>
      dsimp [run_sstore_refund_trace]
      have h_step := t_8038_sstore_refund_delta_potential isCold orig curr newVal
      apply ih newVal (r + (price_sstore isCold orig curr newVal).refundDelta)
      omega
    | revertedChild _ =>
      dsimp [run_sstore_refund_trace]
      exact ih curr r h_inv

/--
**Root refund-counter non-negativity at transaction settlement**
- *Natural property:* Starting from transaction entry (`curr = orig`, `refundCounter = 0`), any finite trace of committed `SSTORE` writes and reverted/halted child frames finishes with a non-negative root `refundCounter`.
- *Formal statement:* `(run_sstore_refund_trace orig trace (orig, 0)).2 ≥ 0` for all `orig : Nat` and `trace : List SstoreTraceStep`.
- *Scope note:* Abstract `SstoreTraceStep` model (lifting across independent storage slots since EIP-8246 `SELFDESTRUCT` grants `0` refund); does not model arbitrary EVM opcodes outside `SSTORE` and frame rollback.
-/
theorem t_8038_refund_counter_telescope_trace_root_nonneg
    (orig : Nat) (trace : List SstoreTraceStep) :
    (run_sstore_refund_trace orig trace (orig, 0)).2 ≥ 0 := by
  have h0 : (0 : Int) ≥ sstore_clear_potential orig orig := by
    have h_eq := (t_8038_sstore_refund_delta_potential false orig orig orig).2.2.2
    omega
  have h_inv := t_8038_refund_counter_telescope_trace_inv orig trace orig 0 h0
  omega

/-! ## 6. Exact `set_delegation` Account-Creation Predicate (`vm/eoa_delegation.py:295`) and
    Relationship to `NoEmptyAccountLeaves` (`F-8037-7702-DELEGATION-ACCOUNT-EXISTS-VS-ALIVE`) -/

/-- Unpatched `set_delegation` (`vm/eoa_delegation.py:295` @ `16898000`):
Charges `StateGasCosts.NEW_ACCOUNT` (`183,600`) iff `not account_exists(tx_state, authority)`. -/
def set_delegation_charges_new_account_v16898000 (txState : TransactionState) (authority : Address) : Bool :=
  !account_exists txState authority

/-- Consistent `is_account_alive` predicate used by all 5 other `StateGasCosts.NEW_ACCOUNT`
charging sites (`call`, `generic_create`, `selfdestruct`, `charge_value_transfer_to_non_alive_account`). -/
def set_delegation_charges_new_account_alive (txState : TransactionState) (authority : Address) : Bool :=
  !is_account_alive txState authority

/--
**Equivalence of account_exists and is_account_alive in set_delegation under pruned state (T-8037-7702-DELEGATION-INVARIANT-EQUIV)**
- *Natural property:* Whenever the state trie contains no unpruned empty account leaves (`NoEmptyAccountLeaves`), `set_delegation`'s `not account_exists` check charges `NEW_ACCOUNT` state gas on the exact same states as `not is_account_alive`.
- *Formal statement:* Under `NoEmptyAccountLeaves txState authority`, `set_delegation_charges_new_account_v16898000 txState authority = set_delegation_charges_new_account_alive txState authority`.
- *Scope note:* Holds on all states reachable through `state_tracker.py` mutators (`no_empty_account_leaves_preserved`); diverges only on synthetic pre-states containing an unpruned `EMPTY_ACCOUNT` leaf (`f_8037_7702_delegation_exists_vs_alive_refuter`).
-/
theorem t_8037_7702_delegation_exists_eq_alive_under_invariant
    (txState : TransactionState) (authority : Address)
    (h_wf : NoEmptyAccountLeaves txState authority) :
    set_delegation_charges_new_account_v16898000 txState authority =
      set_delegation_charges_new_account_alive txState authority := by
  dsimp only [set_delegation_charges_new_account_v16898000, set_delegation_charges_new_account_alive]
  rw [account_exists_iff_alive_of_no_empty_leaves txState authority h_wf]

/--
**Counterexample refuter: set_delegation skips NEW_ACCOUNT charge on unpruned empty leaf (F-8037-7702-DELEGATION-ACCOUNT-EXISTS-VS-ALIVE)**
- *Natural property:* If a pre-state contains an explicit unpruned `EMPTY_ACCOUNT` leaf for `authority`, `account_exists` returns `true` while `is_account_alive` returns `false`, skipping the `183,600` `NEW_ACCOUNT` state-gas charge in `set_delegation`.
- *Formal statement:* `WitnessRefuter` on `accounts := [(0xdead, EMPTY_ACCOUNT)]` where `set_delegation_charges_new_account_v16898000` returns `false` while `!is_account_alive` is `true`.
- *Scope note:* Synthetic fixture boundary violating `NoEmptyAccountLeaves` (`vm/eoa_delegation.py:295`).
-/
def f_8037_7702_delegation_exists_vs_alive_refuter :
    WitnessRefuter (TransactionState × Address) Bool
      (fun ⟨st, auth⟩ charged => charged = !is_account_alive st auth) where
  reference := fun ⟨st, auth⟩ => set_delegation_charges_new_account_alive st auth
  mutant := fun ⟨st, auth⟩ => set_delegation_charges_new_account_v16898000 st auth
  ref_sound := fun _ => rfl
  killWitness := (
    { parent := { preState := { accounts := [(0xdead, EMPTY_ACCOUNT)] } } },
    0xdead
  )
  mutant_refuted := by decide

/-! ## 7. System-Transaction Gas & Reservoir Transcription (`fork.py:100-114, 724-780`) and
    Top-Level `create_evm` Delegation Ordering (`vm/interpreter.py:159-196, 261-285`) -/

/-- Exact `SYSTEM_TRANSACTION_GAS` (`fork.py:107` @ `16898000`): `ExecutionGas(Uint(30000000))`. -/
def SYSTEM_TRANSACTION_GAS : Nat := 30000000

/-- Exact `SYSTEM_MAX_SSTORES_PER_CALL` (`fork.py:108` @ `16898000`): `Uint(16)`. -/
def SYSTEM_MAX_SSTORES_PER_CALL : Nat := 16

/-- Exact `state_gas_reservoir` configured by `process_unchecked_system_transaction`
(`fork.py:759-761` @ `16898000`):
`StateGas(StateGasCosts.STORAGE_SET * SYSTEM_MAX_SSTORES_PER_CALL) = 97920 * 16 = 1,566,720`. -/
def SYSTEM_TRANSACTION_STATE_GAS_RESERVOIR : Nat :=
  STATE_GAS_STORAGE_SET * SYSTEM_MAX_SSTORES_PER_CALL

/-- Exact initial `GasMeter` constructed by `process_top_level` (`vm/interpreter.py:261-265`) when
invoked from `process_unchecked_system_transaction` (`fork.py:750-774` @ `16898000`). -/
def process_unchecked_system_transaction_meter : GasMeter :=
  { gasLeft := SYSTEM_TRANSACTION_GAS
    stateGasLeft := SYSTEM_TRANSACTION_STATE_GAS_RESERVOIR
    stateGasBaseline := SYSTEM_TRANSACTION_STATE_GAS_RESERVOIR }

/--
**System-transaction execution gas and state-gas reservoir provisioning (T-8037-SYS-TX-RESERVOIR-SOUND)**
- *Natural property:* Unchecked system transactions initialize `GasMeter` with `30,000,000` execution gas and a `1,566,720` (`16 × 97,920`) state-gas reservoir, satisfying the spill invariant and funding up to `16` fresh storage writes purely from `stateGasLeft` with zero execution-gas spill.
- *Formal statement:* For any `k ≤ SYSTEM_MAX_SSTORES_PER_CALL` (`16`), `process_unchecked_system_transaction_meter` has `gasLeft = 30000000`, `stateGasLeft = 1566720`, `SpillInvariant`, and `charge_state_gas_from_meter ... (k * STATE_GAS_STORAGE_SET) = some post` with `post.gasLeft = 30000000` and `post.stateGasSpilled = 0`.
- *Scope note:* System-transaction meter initialization (`fork.py:107-108, 756-761`).
-/
theorem t_8037_sys_tx_reservoir_sound (k : Nat) (h_k : k ≤ SYSTEM_MAX_SSTORES_PER_CALL) :
    process_unchecked_system_transaction_meter.gasLeft = 30000000 ∧
    process_unchecked_system_transaction_meter.stateGasLeft = 1566720 ∧
    process_unchecked_system_transaction_meter.SpillInvariant ∧
    ∃ post,
      charge_state_gas_from_meter process_unchecked_system_transaction_meter (k * STATE_GAS_STORAGE_SET) =
        some post ∧
      post.gasLeft = SYSTEM_TRANSACTION_GAS ∧
      post.stateGasSpilled = 0 := by
  refine ⟨rfl, rfl, Or.inr rfl, ?_⟩
  have h_le : k * STATE_GAS_STORAGE_SET ≤ process_unchecked_system_transaction_meter.stateGasLeft := by
    dsimp [process_unchecked_system_transaction_meter, SYSTEM_TRANSACTION_STATE_GAS_RESERVOIR,
      SYSTEM_MAX_SSTORES_PER_CALL, STATE_GAS_STORAGE_SET, STATE_BYTES_PER_STORAGE_SET,
      COST_PER_STATE_BYTE] at *
    omega
  refine ⟨{ process_unchecked_system_transaction_meter with
              stateGasLeft := process_unchecked_system_transaction_meter.stateGasLeft - k * STATE_GAS_STORAGE_SET },
          ?_, rfl, rfl⟩
  unfold charge_state_gas_from_meter
  simp [h_le]

/-- Validated projection (`mapping_kind: projection`) of `create_evm` (`vm/interpreter.py:133-196`)
invoked inside `process_top_level` (`vm/interpreter.py:235-288` @ `16898000`), isolating the
ordering between EIP-7702 delegation state-gas charging and recipient account reading:
- In `create_evm` (`vm/interpreter.py:160-163`), `set_delegation(block_env, tx_env, gas_meter)`
  executes at line 161 BEFORE `resolve_delegated_code_address` and `get_account(tx_env.state, code_address)`
  read `tx_env.recipient` at lines 189-196!
- When `set_delegation` raises `OutOfGasError` (`ExceptionalHalt`), `process_top_level` catches
  `ExceptionalHalt` at line 270 and calls `restore_tx_state(tx_env.state, prep_snapshot)` (which
  preserves `tx_env.state.account_reads`), `restore_state_gas_to_entry`, and `forfeit_remaining_gas`,
  returning before lines 189-196 are ever reached.
- Because `incorporate_tx_into_block` (`fork.py:711-719`) subsequently merges `tx_env.state.account_reads`
  into the Block Access List (`EIP-7928`), `tx_env.recipient` is omitted from `account_reads` even
  though `GasCosts.COLD_ACCOUNT_ACCESS` (`3,000`) was charged upfront in `calculate_intrinsic_cost`. -/
structure TopLevelDelegationState where
  meter : GasMeter
  accountReads : List Address
  deriving Repr, DecidableEq, BEq

/-- Validated projection of `create_evm` delegation and recipient resolution ordering (`vm/interpreter.py:133-196`). -/
def create_evm_delegation_v16898000 (authority recipient : Address) (newAccountCharge : Nat) :
    SpecM TopLevelDelegationState Unit Unit :=
  fun s =>
    let s1 := { s with accountReads := authority :: s.accountReads }
    match charge_state_gas_from_meter s1.meter newAccountCharge with
    | none => .err () s1
    | some m' =>
      let mCommitted := commit_state_gas m'
      .ok () { meter := mCommitted, accountReads := recipient :: s1.accountReads }

/-- Validated projection of `process_top_level` catching `ExceptionalHalt` from `create_evm` (`vm/interpreter.py:235-288`):
rolls back state gas via `restore_state_gas_to_entry` and `forfeit_remaining_gas` while preserving
accumulated `accountReads` from `restore_tx_state`. -/
def top_level_delegation_v16898000 (authority recipient : Address) (newAccountCharge : Nat) :
    SpecM TopLevelDelegationState Unit Unit :=
  fun s =>
    match create_evm_delegation_v16898000 authority recipient newAccountCharge s with
    | .ok () sOk => .ok () sOk
    | .err () sErr =>
      let mHalted := forfeit_remaining_gas (restore_state_gas_to_entry sErr.meter s.meter.stateGasBaseline)
      .err () { sErr with meter := mHalted }

def top_level_delegation_patched (authority recipient : Address) (newAccountCharge : Nat) :
    SpecM TopLevelDelegationState Unit Unit :=
  fun s =>
    let s0 := { s with accountReads := recipient :: s.accountReads }
    match create_evm_delegation_v16898000 authority recipient newAccountCharge s0 with
    | .ok () sOk => .ok () sOk
    | .err () sErr =>
      let mHalted := forfeit_remaining_gas (restore_state_gas_to_entry sErr.meter s.meter.stateGasBaseline)
      .err () { sErr with meter := mHalted }

/--
**Counterexample refuter: set_delegation OOG omits tx.recipient from Block Access List reads (F-2780-7928-SET-DELEGATION-OOG-OMITS-RECIPIENT-READ)**
- *Natural property:* Because `create_evm` executes `set_delegation` before reading `tx_env.recipient`, an `OutOfGasError` during `set_delegation` aborts `process_top_level` before `recipient` is recorded in `account_reads` for the EIP-7928 Block Access List, even though intrinsic gas already charged `COLD_ACCOUNT_ACCESS`.
- *Formal statement:* `WitnessRefuter` on `gasLeft = 10000, stateGasLeft = 0, charge = STATE_GAS_NEW_ACCOUNT` showing `top_level_delegation_v16898000` halts with `recipient ∉ res.state.accountReads`.
- *Scope note:* Top-level EIP-7702 / EIP-7928 ordering projection (`vm/interpreter.py:133-196, 235-288`); does not model cross-transaction authorization replay (`INV-8`).
-/
def f_2780_7928_set_delegation_oog_omits_recipient_refuter :
    WitnessRefuter (TopLevelDelegationState × Address × Address × Nat) (Result Unit TopLevelDelegationState Unit)
      (fun ⟨s0, _, recipient, charge⟩ res =>
        res.state.accountReads.contains recipient = true ∧
        (res.isErr = true ↔ s0.meter.stateGasLeft + s0.meter.gasLeft < charge)) where
  reference := fun ⟨s0, auth, recp, chg⟩ => top_level_delegation_patched auth recp chg s0
  mutant := fun ⟨s0, auth, recp, chg⟩ => top_level_delegation_v16898000 auth recp chg s0
  ref_sound := by
    intro ⟨s0, auth, recp, chg⟩
    dsimp only [top_level_delegation_patched, create_evm_delegation_v16898000]
    cases hc : charge_state_gas_from_meter s0.meter chg with
    | none =>
      dsimp only [charge_state_gas_from_meter] at hc
      split at hc <;> (try split at hc) <;> try contradiction
      simp only [Result.state, List.contains_cons, beq_self_eq_true, Bool.or_true, Bool.true_or,
        Result.isErr, true_iff, true_and]
      omega
    | some m' =>
      dsimp only [charge_state_gas_from_meter] at hc
      split at hc <;> (try split at hc) <;> try contradiction
      all_goals
        simp only [Result.state, List.contains_cons, beq_self_eq_true, Bool.or_true, Bool.true_or,
          Result.isErr, Bool.false_eq_true, false_iff, true_and]
        omega
  killWitness := (
    { meter := { gasLeft := 10000, stateGasLeft := 0, stateGasBaseline := 0 }, accountReads := [] },
    0xaa,
    0xbb,
    STATE_GAS_NEW_ACCOUNT
  )
  mutant_refuted := by decide

@[inline, export glamsterdam_gas_dual_cap_cabi]
def gas_dual_cap_cabi (txRegular txState : UInt64) : UInt64 :=
  max txRegular txState

@[inline, export glamsterdam_settle_gas_used_cabi]
def settle_gas_used_cabi (txGas floor gasLeft stateGasLeft refund stateGasUsed : UInt64) : UInt64 :=
  (settle_transaction_gas txGas.toNat floor.toNat gasLeft.toNat stateGasLeft.toNat refund.toNat stateGasUsed.toNat).gasUsed.toUInt64

@[inline, export glamsterdam_settle_exec_gas_used_cabi]
def settle_exec_gas_used_cabi (txGas floor gasLeft stateGasLeft refund stateGasUsed : UInt64) : UInt64 :=
  (settle_transaction_gas txGas.toNat floor.toNat gasLeft.toNat stateGasLeft.toNat refund.toNat stateGasUsed.toNat).executionGasUsed.toUInt64

@[inline, export glamsterdam_allocate_exec_gas_cabi]
def allocate_exec_gas_cabi (txGas intrinsicExec : UInt64) : UInt64 :=
  (allocate_evm_gas txGas.toNat ⟨intrinsicExec.toNat, 0⟩).executionGas.toUInt64

@[inline, export glamsterdam_allocate_reservoir_cabi]
def allocate_reservoir_cabi (txGas intrinsicExec : UInt64) : UInt64 :=
  (allocate_evm_gas txGas.toNat ⟨intrinsicExec.toNat, 0⟩).stateGasReservoir.toUInt64

@[inline, export glamsterdam_sstore_exec_cost_cabi]
def sstore_exec_cost_cabi (isCold origVal currVal newVal : UInt64) : UInt64 :=
  (price_sstore (isCold != 0) origVal.toNat currVal.toNat newVal.toNat).execGasCost.toUInt64

@[inline, export glamsterdam_sstore_state_cost_cabi]
def sstore_state_cost_cabi (isCold origVal currVal newVal : UInt64) : UInt64 :=
  (price_sstore (isCold != 0) origVal.toNat currVal.toNat newVal.toNat).stateGasCost.toUInt64

@[inline, export glamsterdam_sstore_state_refund_cabi]
def sstore_state_refund_cabi (isCold origVal currVal newVal : UInt64) : UInt64 :=
  (price_sstore (isCold != 0) origVal.toNat currVal.toNat newVal.toNat).stateGasRefundCredited.toUInt64

structure Estimator where
  cap : Nat
  intrinsicExec : Nat
  callGas : Nat
  stateGas : Nat
  delta : Nat
  reservoir : Nat
  ok : Bool
  deriving Repr, DecidableEq, BEq

def budgetFits (cap intrinsicExec callGas stateGas : Nat) : Bool :=
  let alloc := allocate_evm_gas cap ⟨intrinsicExec, 0⟩
  decide (intrinsicExec ≤ cap) &&
    decide (callGas ≤ alloc.executionGas) &&
    decide (callGas + stateGas ≤ alloc.executionGas + alloc.stateGasReservoir)

def observedBudget (e : Estimator) : Prop :=
  let alloc := allocate_evm_gas e.cap ⟨e.intrinsicExec, 0⟩
  e.intrinsicExec ≤ TX_MAX_GAS_LIMIT ∧
  e.callGas ≤ TX_MAX_GAS_LIMIT - e.intrinsicExec ∧
  e.reservoir = alloc.stateGasReservoir ∧
  e.delta = e.callGas ∧
  e.ok = budgetFits e.cap e.intrinsicExec e.callGas e.stateGas

def acceptsAtDelta (e e' : Estimator) : Prop :=
  e.ok = true ∧
  e'.cap = e.intrinsicExec + e.delta ∧
  e'.intrinsicExec = e.intrinsicExec ∧
  e'.callGas = e.callGas ∧
  e'.stateGas = e.stateGas ∧
  e'.delta = e.delta ∧
  e'.reservoir = (allocate_evm_gas e'.cap ⟨e'.intrinsicExec, 0⟩).stateGasReservoir ∧
  e'.ok = budgetFits e'.cap e'.intrinsicExec e'.callGas e'.stateGas

/--
**Abstract gas-estimator unsoundness above 2^24**
- *Natural property:* When a probe runs at `cap > TX_MAX_GAS_LIMIT` (`2^24`), `allocate_evm_gas` provisions a positive state-gas reservoir invisible to a `gasleft()`-delta estimator; replaying at `cap' = intrinsicExec + delta ≤ 2^24` zeroes the reservoir and causes the state-allocating execution to fail.
- *Formal statement:* Given `e.cap > TX_MAX_GAS_LIMIT`, `observedBudget e`, `e.ok = true`, and `e.delta < e.callGas + e.stateGas`, `e.reservoir > 0` and there exists `e'` with `acceptsAtDelta e e'`, `e'.cap ≤ TX_MAX_GAS_LIMIT`, `e'.reservoir = 0`, and `e'.ok = false`.
- *Scope note:* Abstract budget-allocation and `gasleft()`-delta estimator model; does not model live client RPC (`eth_estimateGas`) binary search.
-/
theorem estimator_unsound_above_2pow24
    (e : Estimator)
    (hcap : e.cap > TX_MAX_GAS_LIMIT)
    (hobs : observedBudget e)
    (hok : e.ok = true)
    (hdelta : e.delta < e.callGas + e.stateGas) :
    e.reservoir > 0 ∧
    ∃ e' : Estimator,
      acceptsAtDelta e e' ∧
      e'.cap ≤ TX_MAX_GAS_LIMIT ∧
      e'.reservoir = 0 ∧
      e'.ok = false := by
  rcases hobs with ⟨hintr, hcall, hres, hdel, heok⟩
  refine ⟨?_, ?_⟩
  · dsimp only [allocate_evm_gas, TX_MAX_GAS_LIMIT] at hres ⊢
    unfold TX_MAX_GAS_LIMIT at hcap hintr
    omega
  · let cap' := e.intrinsicExec + e.delta
    let alloc' := allocate_evm_gas cap' ⟨e.intrinsicExec, 0⟩
    refine ⟨{
      cap := cap'
      intrinsicExec := e.intrinsicExec
      callGas := e.callGas
      stateGas := e.stateGas
      delta := e.delta
      reservoir := alloc'.stateGasReservoir
      ok := budgetFits cap' e.intrinsicExec e.callGas e.stateGas
    }, ?_, ?_, ?_, ?_⟩
    · refine ⟨hok, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · dsimp only [cap']
      omega
    · dsimp only [alloc', cap', allocate_evm_gas, TX_MAX_GAS_LIMIT] at *
      omega
    · dsimp only [budgetFits, cap', allocate_evm_gas, TX_MAX_GAS_LIMIT] at *
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      right
      omega

def highBudgetProbeWitness : Estimator :=
  let cap := 16900000
  let intrinsicExec := 21000
  let callGas := 100000
  let stateGas := STATE_GAS_STORAGE_SET
  let alloc := allocate_evm_gas cap ⟨intrinsicExec, 0⟩
  { cap := cap
    intrinsicExec := intrinsicExec
    callGas := callGas
    stateGas := stateGas
    delta := callGas
    reservoir := alloc.stateGasReservoir
    ok := budgetFits cap intrinsicExec callGas stateGas }

def reducedBudgetCandidateWitness : Estimator :=
  let cap := highBudgetProbeWitness.intrinsicExec + highBudgetProbeWitness.delta
  let alloc := allocate_evm_gas cap ⟨highBudgetProbeWitness.intrinsicExec, 0⟩
  { cap := cap
    intrinsicExec := highBudgetProbeWitness.intrinsicExec
    callGas := highBudgetProbeWitness.callGas
    stateGas := highBudgetProbeWitness.stateGas
    delta := highBudgetProbeWitness.delta
    reservoir := alloc.stateGasReservoir
    ok := budgetFits cap highBudgetProbeWitness.intrinsicExec highBudgetProbeWitness.callGas highBudgetProbeWitness.stateGas }

/--
**Concrete 16.9M-to-121k witness for abstract estimator unsoundness**
- *Natural property:* A probe at `cap = 16,900,000` (`reservoir = 122,784`) succeeds on a `100,000`-execution-gas + `97,920`-state-gas operation while reporting `delta = 100,000`, so the candidate budget `cap' = 121,000 ≤ 2^24` gets `reservoir = 0` and fails.
- *Formal statement:* `highBudgetProbeWitness.ok = true ∧ highBudgetProbeWitness.reservoir = 122784 ∧ acceptsAtDelta highBudgetProbeWitness reducedBudgetCandidateWitness ∧ reducedBudgetCandidateWitness.cap = 121000 ∧ reducedBudgetCandidateWitness.reservoir = 0 ∧ reducedBudgetCandidateWitness.ok = false`.
- *Scope note:* Concrete witness paired with `estimator_unsound_above_2pow24` and negative control `allocation_zero_reservoir_below_2pow24`.
-/
theorem estimator_unsound_above_2pow24_witness :
    highBudgetProbeWitness.cap > TX_MAX_GAS_LIMIT ∧
    observedBudget highBudgetProbeWitness ∧
    highBudgetProbeWitness.ok = true ∧
    highBudgetProbeWitness.reservoir = 122784 ∧
    highBudgetProbeWitness.delta < highBudgetProbeWitness.callGas + highBudgetProbeWitness.stateGas ∧
    acceptsAtDelta highBudgetProbeWitness reducedBudgetCandidateWitness ∧
    reducedBudgetCandidateWitness.cap = 121000 ∧
    reducedBudgetCandidateWitness.cap ≤ TX_MAX_GAS_LIMIT ∧
    reducedBudgetCandidateWitness.reservoir = 0 ∧
    reducedBudgetCandidateWitness.ok = false := by
  refine ⟨by decide, ⟨by decide, by decide, rfl, rfl, rfl⟩, by decide, by decide, by decide,
    ⟨by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by decide, by decide, by decide, by decide⟩

/--
**Zero state-gas reservoir below or at the 2^24 execution gas cap**
- *Natural property:* Whenever `txGas ≤ TX_MAX_GAS_LIMIT` (`16,777,216`), `allocate_evm_gas` assigns `0` to `stateGasReservoir` and routes all post-intrinsic gas into `executionGas`.
- *Formal statement:* Given `intrinsic.execution ≤ txGas ≤ TX_MAX_GAS_LIMIT`, `(allocate_evm_gas txGas intrinsic).stateGasReservoir = 0 ∧ (allocate_evm_gas txGas intrinsic).executionGas = txGas - intrinsic.execution`.
- *Scope note:* Negative control for `estimator_unsound_above_2pow24` on `vm/gas.py:1105-1138`.
-/
theorem allocation_zero_reservoir_below_2pow24 (txGas : Nat) (intrinsic : IntrinsicGasCost)
    (h_lo : intrinsic.execution ≤ txGas)
    (h_hi : txGas ≤ TX_MAX_GAS_LIMIT) :
    let alloc := allocate_evm_gas txGas intrinsic
    alloc.stateGasReservoir = 0 ∧
    alloc.executionGas = txGas - intrinsic.execution := by
  unfold allocate_evm_gas TX_MAX_GAS_LIMIT at *
  simp only
  omega

structure FixedBudgetSubcallOutcome where
  txSuccess : Bool
  subcallSuccess : Bool
  postGasLeft : Nat
  postStateGasLeft : Nat
  deriving Repr, DecidableEq, BEq

def run_fixed_budget_caught_subcall
    (txGas intrinsicExec preExecGas subcallCap subcallExecNeed subcallStateNeed : Nat) :
    Option FixedBudgetSubcallOutcome :=
  if txGas < intrinsicExec then
    none
  else
    let alloc := allocate_evm_gas txGas ⟨intrinsicExec, 0⟩
    let parent0 : GasMeter :=
      { gasLeft := alloc.executionGas
        stateGasLeft := alloc.stateGasReservoir
        stateGasBaseline := alloc.stateGasReservoir }
    match charge_gas_from_meter parent0 preExecGas with
    | none => none
    | some parent1 =>
      if parent1.gasLeft < subcallCap then
        none
      else
        let (_, parentAfterDrain) :=
          drain_state_gas_reservoir { parent1 with gasLeft := parent1.gasLeft - subcallCap }
        let child0 : GasMeter :=
          { gasLeft := subcallCap
            stateGasLeft := parent1.stateGasLeft
            stateGasBaseline := parent1.stateGasLeft }
        match charge_gas_from_meter child0 subcallExecNeed >>=
            fun c1 => charge_state_gas_from_meter c1 subcallStateNeed with
        | some childDone =>
          let parentFinal := incorporate_child_meter parentAfterDrain childDone false
          some ⟨true, true, parentFinal.gasLeft, parentFinal.stateGasLeft⟩
        | none =>
          let childHalted := forfeit_remaining_gas (restore_state_gas child0)
          let parentFinal := incorporate_child_meter parentAfterDrain childHalted true
          some ⟨true, false, parentFinal.gasLeft, parentFinal.stateGasLeft⟩

/--
**Transaction-gas dependence of fixed-budget caught subcalls**
- *Natural property:* A caught child call capped at `150,000` execution gas that requires `60,000` execution gas plus one fresh storage slot (`97,920` state gas) fails at `txGas = 500,000` (`reservoir = 0`) yet succeeds at `txGas = 16,900,000` (`reservoir = 122,784`) because the forwarded reservoir covers the state-gas charge.
- *Formal statement:* `run_fixed_budget_caught_subcall 500000 21000 50000 150000 60000 STATE_GAS_STORAGE_SET` yields `some (true, false)`, whereas `txGas = 16900000` yields `some (true, true)`.
- *Scope note:* Two-frame `GasMeter` model capturing the Uniswap v4 `notifyUnsubscribe` fixed-budget pattern; does not replay live EVM bytecode.
-/
theorem t_8037_c13_fixed_budget_subcall_tx_gas_dependent :
    (run_fixed_budget_caught_subcall 500000 21000 50000 150000 60000 STATE_GAS_STORAGE_SET).map
      (fun o => (o.txSuccess, o.subcallSuccess)) = some (true, false) ∧
    (run_fixed_budget_caught_subcall 16900000 21000 50000 150000 60000 STATE_GAS_STORAGE_SET).map
      (fun o => (o.txSuccess, o.subcallSuccess)) = some (true, true) := by
  exact ⟨by decide, by decide⟩

/-! ## 8. Multi-Transaction Block Gas Accounting (`check_block_gas_capacity` + `settle_transaction_gas`) -/

/-- Cumulative block-level gas usage across the three EIP-8037 / EIP-4844 dimensions. -/
structure BlockGasState where
  blockGasUsed : Nat := 0
  blockStateGasUsed : Nat := 0
  blobGasUsed : Nat := 0
  deriving Repr, DecidableEq, BEq

/-- Per-transaction settlement inputs for block-level dual gas accounting. -/
structure BlockTxGas where
  txGas : Nat
  calldataFloor : Nat
  gasLeft : Nat
  stateGasLeft : Nat
  refundCounter : Nat
  stateGasUsed : Nat
  txBlobGas : Nat := 0
  deriving Repr, DecidableEq, BEq

/-- Apply one transaction to the cumulative block gas counters:
1. Verify `check_block_gas_capacity` against the symbolic `blockGasLimit`.
2. Settle the transaction via `settle_transaction_gas` and check execution/state settlement bounds
   (`s.executionGasUsed ≤ min TX_MAX_GAS_LIMIT tx.txGas` and `s.stateGasUsed ≤ tx.txGas`).
3. Accumulate `executionGasUsed`, `stateGasUsed`, and `txBlobGas`. -/
def apply_tx_block_gas (blockGasLimit : Nat) (st : BlockGasState) (tx : BlockTxGas) :
    Option BlockGasState :=
  if check_block_gas_capacity blockGasLimit st.blockGasUsed st.blockStateGasUsed
      st.blobGasUsed tx.txGas tx.txBlobGas then
    let s := settle_transaction_gas tx.txGas tx.calldataFloor tx.gasLeft
      tx.stateGasLeft tx.refundCounter tx.stateGasUsed
    if s.executionGasUsed ≤ min TX_MAX_GAS_LIMIT tx.txGas ∧ s.stateGasUsed ≤ tx.txGas then
      some
        { blockGasUsed := st.blockGasUsed + s.executionGasUsed
          blockStateGasUsed := st.blockStateGasUsed + s.stateGasUsed
          blobGasUsed := st.blobGasUsed + tx.txBlobGas }
    else
      none
  else
    none

/-- Fold `apply_tx_block_gas` over a list of transactions in a block. -/
def run_block_gas_accounting (blockGasLimit : Nat) :
    List BlockTxGas → BlockGasState → Option BlockGasState
  | [], st => some st
  | tx :: rest, st =>
    match apply_tx_block_gas blockGasLimit st tx with
    | none => none
    | some st' => run_block_gas_accounting blockGasLimit rest st'

private theorem apply_tx_block_gas_refund_indep (blockGasLimit : Nat) (st : BlockGasState)
    (tx : BlockTxGas) (altRefund : Nat) :
    apply_tx_block_gas blockGasLimit st { tx with refundCounter := altRefund } =
      apply_tx_block_gas blockGasLimit st tx := by
  unfold apply_tx_block_gas settle_transaction_gas
  rfl

/--
**Multi-transaction block dual gas cap and refund invariance for any block gas limit (T-7778-8037-BLOCK-GAS-INVARIANT)**
- *Natural property:* For any symbolic `blockGasLimit`, folding any sequence of valid transactions through `check_block_gas_capacity` and `settle_transaction_gas` keeps both `blockGasUsed` and `blockStateGasUsed` within `blockGasLimit` (and `blobGasUsed ≤ MAX_BLOB_GAS_PER_BLOCK`), and changing every transaction's `refundCounter` leaves the block gas state completely unchanged.
- *Formal statement:* Under initial capacity bounds on `st0`, `run_block_gas_accounting blockGasLimit txs st0 = some stFinal` implies `stFinal.blockGasUsed ≤ blockGasLimit ∧ stFinal.blockStateGasUsed ≤ blockGasLimit ∧ stFinal.blobGasUsed ≤ MAX_BLOB_GAS_PER_BLOCK`, and mapping `refundCounter` via any function `f` yields the identical `Option BlockGasState`.
- *Scope note:* Multi-transaction block gas fold over `vm/gas.py:1038-1089, 1163-1228` with symbolic `blockGasLimit`.
-/
theorem t_7778_8037_block_gas_cap_and_refund_invariance
    (blockGasLimit : Nat) (txs : List BlockTxGas) (st0 : BlockGasState)
    (h_exec0 : st0.blockGasUsed ≤ blockGasLimit)
    (h_state0 : st0.blockStateGasUsed ≤ blockGasLimit)
    (h_blob0 : st0.blobGasUsed ≤ MAX_BLOB_GAS_PER_BLOCK) :
    (∀ stFinal, run_block_gas_accounting blockGasLimit txs st0 = some stFinal →
      stFinal.blockGasUsed ≤ blockGasLimit ∧
      stFinal.blockStateGasUsed ≤ blockGasLimit ∧
      stFinal.blobGasUsed ≤ MAX_BLOB_GAS_PER_BLOCK) ∧
    (∀ f : Nat → Nat,
      run_block_gas_accounting blockGasLimit
        (txs.map (fun tx => { tx with refundCounter := f tx.refundCounter })) st0 =
      run_block_gas_accounting blockGasLimit txs st0) := by
  induction txs generalizing st0 with
  | nil =>
    refine ⟨?_, fun _ => rfl⟩
    intro stFinal h
    simp only [run_block_gas_accounting, Option.some.injEq] at h
    subst h
    exact ⟨h_exec0, h_state0, h_blob0⟩
  | cons tx rest ih =>
    constructor
    · intro stFinal h
      dsimp only [run_block_gas_accounting] at h
      cases h_step : apply_tx_block_gas blockGasLimit st0 tx with
      | none => rw [h_step] at h; contradiction
      | some st1 =>
        rw [h_step] at h
        unfold apply_tx_block_gas at h_step
        split at h_step
        · rename_i h_cap
          dsimp only at h_step
          split at h_step
          · rename_i h_bounds
            simp only [Option.some.injEq] at h_step
            subst h_step
            unfold check_block_gas_capacity at h_cap
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cap
            have h_exec1 :
                st0.blockGasUsed +
                  (settle_transaction_gas tx.txGas tx.calldataFloor tx.gasLeft
                    tx.stateGasLeft tx.refundCounter tx.stateGasUsed).executionGasUsed ≤
                  blockGasLimit := by omega
            have h_state1 :
                st0.blockStateGasUsed +
                  (settle_transaction_gas tx.txGas tx.calldataFloor tx.gasLeft
                    tx.stateGasLeft tx.refundCounter tx.stateGasUsed).stateGasUsed ≤
                  blockGasLimit := by omega
            have h_blob1 : st0.blobGasUsed + tx.txBlobGas ≤ MAX_BLOB_GAS_PER_BLOCK := by omega
            exact (ih _ h_exec1 h_state1 h_blob1).1 stFinal h
          · contradiction
        · contradiction
    · intro f
      dsimp only [List.map, run_block_gas_accounting]
      rw [apply_tx_block_gas_refund_indep]
      cases h_step : apply_tx_block_gas blockGasLimit st0 tx with
      | none => rfl
      | some st1 =>
        unfold apply_tx_block_gas at h_step
        split at h_step
        · rename_i h_cap
          dsimp only at h_step
          split at h_step
          · rename_i h_bounds
            simp only [Option.some.injEq] at h_step
            subst h_step
            unfold check_block_gas_capacity at h_cap
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cap
            exact (ih _ (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega)).2 f
          · contradiction
        · contradiction

/-- Reachable two-transaction 60M-gas block witness: a 45M contract deployment (2M execution gas,
38M state gas) and a 15M pure-compute transaction fit together under the dual block cap. -/
theorem t_7778_8037_block_gas_witness :
    let deployTx : BlockTxGas :=
      { txGas := 45000000, calldataFloor := 100000, gasLeft := 0, stateGasLeft := 5000000,
        refundCounter := 10000, stateGasUsed := 38000000 }
    let computeTx : BlockTxGas :=
      { txGas := 15000000, calldataFloor := 21000, gasLeft := 0, stateGasLeft := 0,
        refundCounter := 50000, stateGasUsed := 0 }
    run_block_gas_accounting 60000000 [deployTx, computeTx] {} =
      some ⟨17000000, 38000000, 0⟩ := by
  decide

/-! ## 9. Real Child-Rollback Bridge & Multi-Slot `SSTORE` Refund Trace -/

/-- Execute a `List SstoreTraceStep` while explicitly running every `.revertedChild` sub-trace
on a child frame starting at `child.refundCounter = 0` and rolling back via `restore_state_gas`
and `restore_tx_state`. -/
def run_sstore_refund_trace_with_child_exec (origVal : Nat) :
    List SstoreTraceStep → Nat × Int → Nat × Int
  | [], st => st
  | (.sstore isCold newVal) :: rest, (currVal, r) =>
    let d := (price_sstore isCold origVal currVal newVal).refundDelta
    run_sstore_refund_trace_with_child_exec origVal rest (newVal, r + d)
  | (.revertedChild childWrites) :: rest, (currVal, r) =>
    let (_, childRefund) := childWrites.foldl
      (fun (cv, cr) (isCold, nv) => (nv, cr + (price_sstore isCold origVal cv nv).refundDelta))
      (currVal, (0 : Int))
    let childMeterAfter : GasMeter :=
      { gasLeft := 0, stateGasLeft := 0, stateGasBaseline := 0, refundCounter := childRefund }
    let childRestored := restore_state_gas childMeterAfter
    run_sstore_refund_trace_with_child_exec origVal rest (currVal, r + childRestored.refundCounter)

/-- Equivalence showing explicit child execution + `restore_state_gas` rollback equals the abstract
`run_sstore_refund_trace` transition. -/
theorem run_sstore_refund_trace_with_child_exec_eq (origVal : Nat) (trace : List SstoreTraceStep)
    (st : Nat × Int) :
    run_sstore_refund_trace_with_child_exec origVal trace st =
      run_sstore_refund_trace origVal trace st := by
  induction trace generalizing st with
  | nil => rfl
  | cons step rest ih =>
    cases st with
    | mk currVal r =>
      cases step with
      | sstore isCold newVal =>
        dsimp only [run_sstore_refund_trace_with_child_exec, run_sstore_refund_trace]
        exact ih (newVal, r + (price_sstore isCold origVal currVal newVal).refundDelta)
      | revertedChild childWrites =>
        dsimp only [run_sstore_refund_trace_with_child_exec, run_sstore_refund_trace, restore_state_gas]
        simpa only [Int.add_zero] using ih (currVal, r)

/-- Multi-slot execution step interleaving `SSTORE` across arbitrary storage keys, pure compute
opcodes (`execOp`), and nested reverting child frames (`revertedChild`). -/
inductive MultiSlotTraceStep where
  | sstore (key : StorageKey) (isCold : Bool) (newVal : Nat)
  | execOp (gasCost : Nat)
  | revertedChild (childSteps : List MultiSlotTraceStep)
  deriving Repr, BEq

/-- Update a storage map at a single key. -/
def updateSlot (m : StorageKey → Nat) (k : StorageKey) (v : Nat) : StorageKey → Nat :=
  fun k' => if k' == k then v else m k'

/-- Execute a multi-slot trace with explicit child-frame execution and `restore_state_gas` rollback. -/
def run_multislot_refund_trace (origMap : StorageKey → Nat) :
    List MultiSlotTraceStep → (StorageKey → Nat) × Int → (StorageKey → Nat) × Int
  | [], st => st
  | (.sstore key isCold newVal) :: rest, (currMap, r) =>
    let d := (price_sstore isCold (origMap key) (currMap key) newVal).refundDelta
    run_multislot_refund_trace origMap rest (updateSlot currMap key newVal, r + d)
  | (.execOp _) :: rest, st =>
    run_multislot_refund_trace origMap rest st
  | (.revertedChild childSteps) :: rest, (currMap, r) =>
    let (_, childRefund) := run_multislot_refund_trace origMap childSteps (currMap, 0)
    let childRestored := restore_state_gas
      { gasLeft := 0, stateGasLeft := 0, stateGasBaseline := 0, refundCounter := childRefund }
    run_multislot_refund_trace origMap rest (currMap, r + childRestored.refundCounter)

/-- Sum of `sstore_clear_potential` across a duplicate-free list of storage keys. -/
def multi_slot_potential (origMap currMap : StorageKey → Nat) : List StorageKey → Int
  | [] => 0
  | k :: ks => sstore_clear_potential (origMap k) (currMap k) + multi_slot_potential origMap currMap ks

private theorem multi_slot_potential_nonneg (origMap currMap : StorageKey → Nat) (ks : List StorageKey) :
    multi_slot_potential origMap currMap ks ≥ 0 := by
  induction ks with
  | nil => simp [multi_slot_potential]
  | cons k ks ih =>
    dsimp only [multi_slot_potential]
    have hk := (t_8038_sstore_refund_delta_potential false (origMap k) (currMap k) (currMap k)).2.2.1
    omega

private theorem multi_slot_potential_orig_zero (origMap : StorageKey → Nat) (ks : List StorageKey) :
    multi_slot_potential origMap origMap ks = 0 := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    dsimp only [multi_slot_potential]
    have hk := (t_8038_sstore_refund_delta_potential false (origMap k) (origMap k) (origMap k)).2.2.2
    omega

private theorem multi_slot_potential_update_not_mem (origMap currMap : StorageKey → Nat)
    (key : StorageKey) (newVal : Nat) (ks : List StorageKey) (h_not : key ∉ ks) :
    multi_slot_potential origMap (updateSlot currMap key newVal) ks =
      multi_slot_potential origMap currMap ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    have h_ne : k ≠ key := fun h_eq => h_not (by simp [h_eq])
    have h_not_tl : key ∉ ks := fun h_mem => h_not (List.mem_cons_of_mem k h_mem)
    have h_beq : (k == key) = false := beq_false_of_ne h_ne
    dsimp only [multi_slot_potential, updateSlot]
    rw [h_beq]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [ih h_not_tl]

private theorem multi_slot_potential_update_mem (origMap currMap : StorageKey → Nat)
    (key : StorageKey) (newVal : Nat) (ks : List StorageKey)
    (h_nodup : ks.Nodup) (h_mem : key ∈ ks) :
    multi_slot_potential origMap (updateSlot currMap key newVal) ks -
      multi_slot_potential origMap currMap ks =
    sstore_clear_potential (origMap key) newVal -
      sstore_clear_potential (origMap key) (currMap key) := by
  induction ks with
  | nil => contradiction
  | cons k ks ih =>
    rw [List.nodup_cons] at h_nodup
    rcases h_nodup with ⟨h_k_not_in, h_ks_nodup⟩
    cases List.mem_cons.mp h_mem with
    | inl h_eq =>
      subst h_eq
      dsimp only [multi_slot_potential]
      have h_tl := multi_slot_potential_update_not_mem origMap currMap key newVal ks h_k_not_in
      have h_at : updateSlot currMap key newVal key = newVal := by simp [updateSlot]
      rw [h_at, h_tl]
      omega
    | inr h_in_tl =>
      have h_ne : k ≠ key := fun h_eq => h_k_not_in (h_eq ▸ h_in_tl)
      have h_beq : (k == key) = false := beq_false_of_ne h_ne
      dsimp only [multi_slot_potential]
      have h_at : updateSlot currMap key newVal k = currMap k := by simp [updateSlot, h_beq]
      rw [h_at]
      have h_rec := ih h_ks_nodup h_in_tl
      omega

/-- All storage keys written at top-level steps of a `MultiSlotTraceStep` list belong to `ks`. -/
def MultiSlotKeysIn (ks : List StorageKey) : List MultiSlotTraceStep → Prop
  | [] => True
  | (.sstore key _ _) :: rest => key ∈ ks ∧ MultiSlotKeysIn ks rest
  | (.execOp _) :: rest => MultiSlotKeysIn ks rest
  | (.revertedChild _) :: rest => MultiSlotKeysIn ks rest

theorem t_8038_multislot_refund_trace_inv
    (origMap : StorageKey → Nat) (ks : List StorageKey) (h_nodup : ks.Nodup)
    (trace : List MultiSlotTraceStep) (h_keys : MultiSlotKeysIn ks trace)
    (currMap : StorageKey → Nat) (r : Int)
    (h_inv : r ≥ multi_slot_potential origMap currMap ks) :
    (run_multislot_refund_trace origMap trace (currMap, r)).2 ≥
      multi_slot_potential origMap (run_multislot_refund_trace origMap trace (currMap, r)).1 ks ∧
    multi_slot_potential origMap (run_multislot_refund_trace origMap trace (currMap, r)).1 ks ≥ 0 := by
  induction trace generalizing currMap r with
  | nil =>
    simp only [run_multislot_refund_trace]
    exact ⟨h_inv, multi_slot_potential_nonneg origMap currMap ks⟩
  | cons step rest ih =>
    cases step with
    | sstore key isCold newVal =>
      rcases h_keys with ⟨h_mem, h_rest⟩
      simp only [run_multislot_refund_trace]
      have h_step := t_8038_sstore_refund_delta_potential isCold (origMap key) (currMap key) newVal
      have h_pot := multi_slot_potential_update_mem origMap currMap key newVal ks h_nodup h_mem
      apply ih h_rest (updateSlot currMap key newVal)
        (r + (price_sstore isCold (origMap key) (currMap key) newVal).refundDelta)
      omega
    | execOp _ =>
      simp only [run_multislot_refund_trace]
      exact ih h_keys currMap r h_inv
    | revertedChild _ =>
      simp only [run_multislot_refund_trace, restore_state_gas, Int.add_zero]
      exact ih h_keys currMap r h_inv

/--
**Multi-slot root refund-counter non-negativity with interleaved compute and child rollbacks (T-8038-REFUND-MULTISLOT-NONNEG)**
- *Natural property:* Starting from any pre-transaction storage map `origMap` with `refundCounter = 0`, any finite multi-slot sequence of `SSTORE` writes across arbitrary keys, interleaved pure compute opcodes, and nested reverting child frames ends with a non-negative root `refundCounter`.
- *Formal statement:* For any duplicate-free key set `ks` covering top-level `SSTORE` keys, `(run_multislot_refund_trace origMap trace (origMap, 0)).2 ≥ 0`.
- *Scope note:* Multi-slot `SSTORE` + pure compute + `restore_state_gas` child-rollback trace model.
-/
theorem t_8038_multislot_refund_trace_root_nonneg
    (origMap : StorageKey → Nat) (ks : List StorageKey) (h_nodup : ks.Nodup)
    (trace : List MultiSlotTraceStep) (h_keys : MultiSlotKeysIn ks trace) :
    (run_multislot_refund_trace origMap trace (origMap, 0)).2 ≥ 0 := by
  have h0 : (0 : Int) ≥ multi_slot_potential origMap origMap ks := by
    rw [multi_slot_potential_orig_zero]
    omega
  have h_inv := t_8038_multislot_refund_trace_inv origMap ks h_nodup trace h_keys origMap 0 h0
  omega

/-! ## 10. EIP-7702 Set-Then-Clear Committed Charge & `INV-8` Mined-OOG Replay -/

/-- Apply one EIP-7702 authorization entry (`vm/eoa_delegation.py:231-321`):
charges `STATE_GAS_AUTH_BASE` (`35,190`) plus `STATE_GAS_NEW_ACCOUNT` (`183,600`) when the
authority is not yet alive, then commits state gas via `commit_state_gas` regardless of whether
`target = 0` (clear) or `target ≠ 0` (set). -/
def apply_delegation_entry (m : GasMeter) (_target : Address) (alreadyAlive : Bool) : Option GasMeter :=
  let charge := STATE_GAS_AUTH_BASE + (if alreadyAlive then 0 else STATE_GAS_NEW_ACCOUNT)
  (charge_state_gas_from_meter m charge).map commit_state_gas

private theorem charge_state_gas_commit_delta (m m' : GasMeter) (c : Nat)
    (h : charge_state_gas_from_meter m c = some m') :
    let mc := commit_state_gas m'
    (mc.stateGasCommittedSpill : Int) - (mc.stateGasBaseline : Int) =
      (m.stateGasCommittedSpill : Int) + (m.stateGasSpilled : Int) - (m.stateGasLeft : Int) + (c : Int) ∧
    mc.stateGasSpilled = 0 ∧
    mc.stateGasLeft = mc.stateGasBaseline := by
  unfold charge_state_gas_from_meter at h
  by_cases h1 : m.stateGasLeft ≥ c
  · simp only [h1, ↓reduceIte, Option.some.injEq] at h
    subst h
    dsimp only [commit_state_gas]
    refine ⟨by omega, rfl, rfl⟩
  · by_cases h2 : m.stateGasLeft + m.gasLeft ≥ c
    · simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
      subst h
      dsimp only [commit_state_gas]
      refine ⟨by omega, rfl, rfl⟩
    · simp only [h1, h2, ↓reduceIte, reduceCtorEq] at h

/--
**EIP-7702 delegation set-then-clear retains committed state-gas charge (T-8037-7702-SET-CLEAR-KEEPS-CHARGE)**
- *Natural property:* Setting an EIP-7702 delegation and then clearing it (`target = 0`) in the same transaction keeps the full committed state-gas charge, and a subsequent EVM body `REVERT` (`restore_state_gas`) does not refund it.
- *Formal statement:* Starting at entry (`stateGasLeft = reservoir, stateGasSpilled = 0, stateGasCommittedSpill = 0`), after `apply_delegation_entry m0 target false = some m1`, `apply_delegation_entry m1 0 true = some m2`, and `restore_state_gas m2`, `tx_state_gas_used (restore_state_gas m2) reservoir = (STATE_GAS_AUTH_BASE + STATE_GAS_NEW_ACCOUNT + STATE_GAS_AUTH_BASE : Int)`.
- *Scope note:* Confirms the second intended corner case locked during scoping (`vm/eoa_delegation.py:231-321`, `vm/gas.py:459-517`).
-/
theorem t_8037_7702_set_then_clear_keeps_charge
    (m0 m1 m2 : GasMeter) (reservoir : Nat) (target : Address)
    (h_left : m0.stateGasLeft = reservoir)
    (h_spilled : m0.stateGasSpilled = 0)
    (h_comm : m0.stateGasCommittedSpill = 0)
    (h1 : apply_delegation_entry m0 target false = some m1)
    (h2 : apply_delegation_entry m1 0 true = some m2) :
    tx_state_gas_used (restore_state_gas m2) reservoir =
      (STATE_GAS_AUTH_BASE + STATE_GAS_NEW_ACCOUNT + STATE_GAS_AUTH_BASE : Int) := by
  unfold apply_delegation_entry at h1 h2
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Option.map_eq_some_iff] at h1 h2
  rcases h1 with ⟨m1', hc1, rfl⟩
  rcases h2 with ⟨m2', hc2, rfl⟩
  have hd1 := charge_state_gas_commit_delta m0 m1' (STATE_GAS_AUTH_BASE + STATE_GAS_NEW_ACCOUNT) hc1
  have hd2 := charge_state_gas_commit_delta (commit_state_gas m1') m2' STATE_GAS_AUTH_BASE hc2
  dsimp only [restore_state_gas, tx_state_gas_used]
  omega

/--
**EIP-7702 `INV-8` mined-OOG rollback leaves authorization replayable (F-8037-7702-INV8-REPLAY-AFTER-OOG)**
- *Natural property:* When a top-level EIP-7702 transaction runs out of gas during `set_delegation`, the transaction halts (forfeiting execution gas while restoring the state-gas reservoir) and rolls back the authority's state, allowing the same signed delegation to be replayed and succeed in a later transaction with sufficient gas.
- *Formal statement:* At `gasLeft = 10000, stateGasLeft = 0`, `top_level_delegation_v16898000 0xaa 0xbb STATE_GAS_NEW_ACCOUNT` returns `.err` with `gasLeft = 0`, whereas replaying the same `(0xaa, 0xbb, STATE_GAS_NEW_ACCOUNT)` with `gasLeft = 200000` returns `.ok` with `0xaa` and `0xbb` recorded.
- *Scope note:* Two-transaction `INV-8` replay witness over `top_level_delegation_v16898000` (`vm/interpreter.py:133-288`).
-/
theorem t_8037_7702_inv8_mined_oog_replay :
    let sLow : TopLevelDelegationState :=
      { meter := { gasLeft := 10000, stateGasLeft := 0, stateGasBaseline := 0 }, accountReads := [] }
    let sHigh : TopLevelDelegationState :=
      { meter := { gasLeft := 200000, stateGasLeft := 0, stateGasBaseline := 0 }, accountReads := [] }
    let r1 := top_level_delegation_v16898000 0xaa 0xbb STATE_GAS_NEW_ACCOUNT sLow
    let r2 := top_level_delegation_v16898000 0xaa 0xbb STATE_GAS_NEW_ACCOUNT sHigh
    r1.isErr = true ∧ r1.state.meter.gasLeft = 0 ∧ r1.state.meter.stateGasLeft = 0 ∧
    r2.isErr = false ∧ r2.state.accountReads.contains 0xaa = true ∧
      r2.state.accountReads.contains 0xbb = true := by
  decide

end Glamsterdam.Gas.Spec
