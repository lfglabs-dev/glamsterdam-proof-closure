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

/-- Exact 6-field `GasMeter` roundtrip theorem (`vm/gas.py:689-710, 493-517` & `vm/__init__.py:188-245`):
When a parent drains its `stateGasLeft` into a child (`drain_state_gas_reservoir`), the child
executes an arbitrary state-gas charge `childStateCharge` (possibly spilling out of the reservoir
into `child.gasLeft`!), and the child then reverts (`restore_state_gas` followed by
`incorporate_child_meter parentAfterDrain childRestored true`), the parent's `stateGasLeft` is
restored to `parent.stateGasLeft` and all spilled execution gas is returned to `gasLeft`! -/
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

/-- Theorem: Whenever `gasLeft ≥ extraGas + memoryCost`, `calculate_message_call_gas` guarantees
that `cost + memoryCost ≤ gasLeft`, and whenever `gasLeft < extraGas + memoryCost`,
`calculate_message_call_gas` returns `cost = gas + extraGas` (so `cost + memoryCost > gasLeft` and
the subsequent `charge_gas_from_meter` deterministically raises `OutOfGasError`). -/
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

/-- Theorem (`T-8037-ALLOCATE-EVM-GAS-CONSERVATION`): Whenever `intrinsic.execution ≤ txGas` and
`intrinsic.execution ≤ TX_MAX_GAS_LIMIT` (guaranteed by `validate_transaction`),
`allocate_evm_gas` partitions `txGas` without loss or overflow:
`intrinsic.execution + alloc.executionGas + alloc.stateGasReservoir = txGas` and
`intrinsic.execution + alloc.executionGas ≤ TX_MAX_GAS_LIMIT`. -/
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

/-- T-8038-2780-WARM-COLD: Pinned warm/cold access and write gas bounds (`vm/gas.py:47-90`). -/
theorem t_8038_2780_warm_cold_bounds :
    GAS_WARM_ACCESS < GAS_COLD_STORAGE_ACCESS ∧
    GAS_COLD_STORAGE_ACCESS < GAS_COLD_ACCOUNT_ACCESS ∧
    GAS_COLD_ACCOUNT_ACCESS < GAS_ACCOUNT_WRITE ∧
    GAS_CREATE_ACCESS = GAS_ACCOUNT_WRITE + GAS_COLD_ACCOUNT_ACCESS ∧
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

/-- Explicit `WitnessRefuter` for `F-8038-7778-SSTORE-RESET-REFUND-CAP-AND-BLOCK-GAS`:
On `baseTxExecGas = 15000`, `sstore_dirty_reset_settlement_v16898000` charges the user `20,160` gas
and charges the block `25,200` execution gas, whereas the direct reset charges `15,200` for both. -/
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

/-- Theorem (`t_8038_sstore_refund_delta_potential`, `vm/instructions/storage.py:126-139`):
Every single `SSTORE` transition from `currentValue` to `newValue` (with transaction-original value
`originalValue`) satisfies the exact telescoping decomposition:
`refundDelta = (Φ(orig, new) - Φ(orig, curr)) + [curr ≠ new ∧ orig = new] * STORAGE_WRITE`.
Consequently, while a child frame's local `refundCounter` can be negative (e.g. `-11,616` or `-1,616`
when a parent cleared an originally non-zero slot `1 -> 0` and the child re-dirties it `0 -> 2` or
`0 -> 1`), the quantity `refundCounter - Φ(orig, curr)` is monotonically non-decreasing across every
`SSTORE` (`postRefund - Φ(orig, new) ≥ preRefund - Φ(orig, curr)`). -/
theorem t_8038_sstore_refund_delta_potential
    (isCold : Bool) (originalValue currentValue newValue : Nat) :
    let p := price_sstore isCold originalValue currentValue newValue
    let resetBonus : Int :=
      if currentValue != newValue && originalValue == newValue then (GAS_STORAGE_WRITE : Int) else 0
    p.refundDelta =
      (sstore_clear_potential originalValue newValue - sstore_clear_potential originalValue currentValue) +
        resetBonus ∧
    0 ≤ resetBonus ∧
    0 ≤ sstore_clear_potential originalValue newValue ∧
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

/-- Theorem (`t_8038_refund_counter_telescope_nonneg`, two-step lemma for
`EvmGasSemantics/Meter.lean` line 62, `EvmGasSemantics/Rules/Setup.lean` line 60, and
`EvmGasSemantics/Exec.lean` lines 170-174 in `fradamt/evm-gas-semantics-lean`, plus EELS
`src/ethereum/forks/amsterdam/vm/gas.py:1168`):
Starting from transaction entry where `currentValue = originalValue` and `refundCounter = 0`,
two consecutive `SSTORE` transitions `orig -> v1 -> v2` on a slot preserve
`refundCounter ≥ Φ(orig, curr) ≥ 0` (generalized to arbitrary `List SstoreTraceStep` sequences
with reverting child frames in `t_8038_refund_counter_telescope_trace_root_nonneg` below).
In particular:
1. A child frame entering at `curr = 0` (`orig ≠ 0`) and writing `0 -> 2` has negative local
   `child.refundDelta = -11616 < 0` (or `-1616 < 0` on `0 -> 1`),
2. Yet when merged with the parent that performed `orig -> 0` (`parent.refundDelta = +11616`),
   the combined transaction `refundCounter` is `0 ≥ Φ(orig, 2) = 0` (or `10000 ≥ Φ(orig, 1) = 0`). -/
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

/-- Theorem (`t_8038_refund_counter_telescope_trace_nonneg`):
For ANY finite sequence `trace : List SstoreTraceStep` of committed `SSTORE`s (which includes
merged successful child frames by associativity of `+`) and reverted/halted child frames, starting
from any state `(curr, r)` satisfying `r ≥ sstore_clear_potential orig curr`, the post-trace state
`(curr', r')` satisfies `r' ≥ sstore_clear_potential orig curr' ≥ 0`. In particular, starting from
transaction entry `(orig, 0)`, the root `refundCounter` is unconditionally `≥ 0`. -/
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

/-- Theorem: On every `TransactionState` satisfying `NoEmptyAccountLeaves` (which is preserved by all
`state_tracker.py` mutators via `no_empty_account_leaves_preserved`), `set_delegation_charges_new_account_v16898000`
and `set_delegation_charges_new_account_alive` are observationally identical. -/
theorem t_8037_7702_delegation_exists_eq_alive_under_invariant
    (txState : TransactionState) (authority : Address)
    (h_wf : NoEmptyAccountLeaves txState authority) :
    set_delegation_charges_new_account_v16898000 txState authority =
      set_delegation_charges_new_account_alive txState authority := by
  dsimp only [set_delegation_charges_new_account_v16898000, set_delegation_charges_new_account_alive]
  rw [account_exists_iff_alive_of_no_empty_leaves txState authority h_wf]

/-- Explicit `WitnessRefuter` for `F-8037-7702-DELEGATION-ACCOUNT-EXISTS-VS-ALIVE`:
Only when `authority` is present in `PreState` as an unpruned `EMPTY_ACCOUNT` leaf (violating
`NoEmptyAccountLeaves`, e.g. in a synthetic EEST fixture) does `account_exists` return `true`
while `is_account_alive` returns `false`. -/
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

/-- Theorem (`t_8037_sys_tx_reservoir_sound`, `fork.py:107-108, 756-761`):
`process_unchecked_system_transaction` provisions `execution_gas_grant = 30,000,000` and
`state_gas_reservoir = 1,566,720` (`16 * STATE_GAS_STORAGE_SET`), satisfying `GasMeter.SpillInvariant`
and covering up to `16` new storage slot writes (`k ≤ SYSTEM_MAX_SSTORES_PER_CALL`) purely from
`stateGasLeft` with `stateGasSpilled = 0`. -/
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

end Glamsterdam.Gas.Spec
