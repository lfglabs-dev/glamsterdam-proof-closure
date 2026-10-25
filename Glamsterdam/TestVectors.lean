/-
Copyright (c) 2026 Verity Labs / LFG Labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Marchand, Verity Audit Team
-/
import Glamsterdam.Common.Prelude
import Glamsterdam.Common.MetaSpec
import Glamsterdam.Common.ElCore
import Glamsterdam.Eip8246.Spec
import Glamsterdam.Gas.Spec
import Glamsterdam.Gas.CallTree
import Glamsterdam.Gloas7732.Spec

/-!
# Glamsterdam In-Kernel Test Vectors ("Double Checks de Secours")

This module provides kernel-checked (`by decide` / `by rfl`, with zero `native_decide`)
test-vector theorems extracted directly from `ethereum/execution-specs` (`16898000`) and
`ethereum/consensus-specs` (`v1.7.0-beta.4` @ `aa16bb4c`).

Every transcribed function in `ElCore`, `Eip8246.Spec`, `Gas.Spec`, and `Gloas7732.Spec`
is exercised on concrete inputs covering both normal paths and boundary/edge cases, locking
the Lean 4 definitions against transcription drift.
-/

namespace Glamsterdam.TestVectors

open Glamsterdam.Common.Prelude
open Glamsterdam.Common.MetaSpec
open Glamsterdam.Common.ElCore
open Glamsterdam.Eip8246.Spec
open Glamsterdam.Gas.Spec
open Glamsterdam.Gas.CallTree
open Glamsterdam.Gloas7732.Spec

/-! ## 1. `ElCore` State Tracker & `GasMeter` Test Vectors -/

/-- Test Vector 1: `TransactionState` read chain (`txWrites -> parent.accountWrites -> preState`),
`set_storage`, `destroy_storage_tx`, and `clear_account_preserving_balance_tx` when `balance > 0`
vs `balance = 0`. -/
theorem tv_elcore_tx_state_lifecycle :
    let pre : PreState := {
      accounts := [(0x100, { nonce := 3, balance := 500, codeHash := 0xabc, codeEmpty := false })]
      storage := [((0x100, 1), 42)]
    }
    let st0 : TransactionState := { parent := { preState := pre } }
    let st1 := set_storage st0 0x100 2 99
    let stCleared := clear_account_preserving_balance_tx st1 0x100
    let stZeroBal := set_account st0 0x200 (some { nonce := 1, balance := 0, codeHash := 0xdef, codeEmpty := false })
    let stZeroCleared := clear_account_preserving_balance_tx stZeroBal 0x200
    get_storage st1 0x100 1 = 42 ∧
    get_storage st1 0x100 2 = 99 ∧
    (get_account stCleared 0x100).balance = 500 ∧
    (get_account stCleared 0x100).nonce = 0 ∧
    (get_account stCleared 0x100).codeHash = EMPTY_CODE_HASH ∧
    get_storage stCleared 0x100 1 = 0 ∧
    get_storage stCleared 0x100 2 = 0 ∧
    get_account_optional stZeroCleared 0x200 = none := by
  decide

/-- Test Vector 2: `GasMeter` reservoir charge, spill into `gasLeft`, LIFO `credit_state_gas_refund`,
`commit_state_gas`, `restore_state_gas`, and `repay_state_gas_spill`. -/
theorem tv_elcore_gas_meter_spill_and_lifo_refund :
    let m0 : GasMeter := { gasLeft := 100000, stateGasLeft := 50000, stateGasBaseline := 50000 }
    let m1 := charge_state_gas_from_meter m0 80000
    let m2 := m1.map (fun m => credit_state_gas_refund m 80000)
    let m3 := m1.map (fun m => repay_state_gas_spill { m with stateGasLeft := 20000 })
    let m4 := m1.map commit_state_gas
    let m5 := m1.map restore_state_gas
    m1 = some {
      gasLeft := 70000
      stateGasLeft := 0
      stateGasBaseline := 50000
      refundCounter := 0
      stateGasSpilled := 30000
      stateGasCommittedSpill := 0
    } ∧
    m2 = some m0 ∧
    m3 = some {
      gasLeft := 90000
      stateGasLeft := 0
      stateGasBaseline := 50000
      refundCounter := 0
      stateGasSpilled := 10000
      stateGasCommittedSpill := 0
    } ∧
    m4 = some {
      gasLeft := 70000
      stateGasLeft := 0
      stateGasBaseline := 0
      refundCounter := 0
      stateGasSpilled := 0
      stateGasCommittedSpill := 30000
    } ∧
    m5 = some m0 := by
  decide

/-! ## 2. `Eip8246.Spec` (`SELFDESTRUCT` & BAL Clear) Test Vectors -/

/-- Test Vector 3: `exec_selfdestruct` on distinct beneficiary (dead vs alive) and self-beneficiary
(`originator = beneficiary`, preserving balance without self-burn), plus `incorporate_child_frame`
on revert (`childError = true`, discarding `accountsToDelete`) vs success (`childError = false`). -/
theorem tv_eip8246_selfdestruct_vectors :
    let sdSelf : SelfdestructStep := {
      originator := 0xaa
      beneficiary := 0xaa
      originatorBalance := 1000
      beneficiaryBalance := 1000
      beneficiaryAlive := true
      beneficiaryCold := false
      originatorCreatedInTx := true
    }
    let sdDeadBeneficiary : SelfdestructStep := {
      originator := 0xaa
      beneficiary := 0xbb
      originatorBalance := 1000
      beneficiaryBalance := 0
      beneficiaryAlive := false
      beneficiaryCold := true
      originatorCreatedInTx := false
    }
    let parentFrame : EvmFrame := {
      txState := {}
      gasMeter := { gasLeft := 50000, stateGasLeft := 0, stateGasBaseline := 0 }
      accountsToDelete := [0x11]
    }
    let childFrame : EvmFrame := {
      txState := set_storage {} 0xaa 1 99
      gasMeter := { gasLeft := 10000, stateGasLeft := 0, stateGasBaseline := 0 }
      accountsToDelete := [0x22]
    }
    exec_selfdestruct sdSelf = {
      execGasCharged := 5000
      stateGasCharged := 0
      postOriginatorBalance := 1000
      postBeneficiaryBalance := 1000
      scheduledForClear := true
    } ∧
    exec_selfdestruct sdDeadBeneficiary = {
      execGasCharged := 17000
      stateGasCharged := 183600
      postOriginatorBalance := 0
      postBeneficiaryBalance := 1000
      scheduledForClear := false
    } ∧
    (incorporate_child_frame parentFrame childFrame true).accountsToDelete = [0x11] ∧
    (incorporate_child_frame parentFrame childFrame false).accountsToDelete = [0x11, 0x22] := by
  decide

/-! ## 3. `Gas.Spec` (`EIP-8037`, `EIP-8038`, `EIP-2780`, `EIP-7778`) Test Vectors -/

/-- Test Vector 4: `calculate_intrinsic_cost` across EOA transfer, self-transfer, contract creation,
access list surcharge (`EIP-7981`), and `SetCodeTransaction` authorizations (`EIP-7702`, `authCount = 2`). -/
theorem tv_gas_intrinsic_cost_vectors :
    let simpleTransfer : TxIntrinsicInput := {
      zeroDataBytes := 0
      nonZeroDataBytes := 0
      isCreate := false
      isSelfTransfer := false
      hasPositiveValue := true
      accessListAddresses := 0
      accessListStorageKeys := 0
      authCount := 0
    }
    let selfTransfer : TxIntrinsicInput := {
      zeroDataBytes := 0
      nonZeroDataBytes := 0
      isCreate := false
      isSelfTransfer := true
      hasPositiveValue := true
      accessListAddresses := 0
      accessListStorageKeys := 0
      authCount := 0
    }
    let createTx : TxIntrinsicInput := {
      zeroDataBytes := 10
      nonZeroDataBytes := 22
      isCreate := true
      isSelfTransfer := false
      hasPositiveValue := false
      accessListAddresses := 1
      accessListStorageKeys := 2
      authCount := 0
    }
    let setCodeTx : TxIntrinsicInput := {
      zeroDataBytes := 0
      nonZeroDataBytes := 0
      isCreate := false
      isSelfTransfer := false
      hasPositiveValue := false
      accessListAddresses := 0
      accessListStorageKeys := 0
      authCount := 2
    }
    calculate_intrinsic_cost simpleTransfer = ⟨21000, 21000⟩ ∧
    calculate_intrinsic_cost selfTransfer = ⟨12000, 12000⟩ ∧
    calculate_intrinsic_cost createTx = ⟨36670, 31424⟩ ∧
    calculate_intrinsic_cost setCodeTx = ⟨30632, 15000⟩ := by
  decide

/-- Test Vector 5: `allocate_evm_gas`, `settle_transaction_gas`, and `price_sstore` across
cold zero->nonzero creation (`0 -> 42`), warm modification (`42 -> 99`), and dirty reset (`42 -> 0`). -/
theorem tv_gas_allocate_settle_and_sstore_vectors :
    let alloc := allocate_evm_gas 20000000 ⟨21000, 21000⟩
    let settled := settle_transaction_gas 100000 21000 40000 0 15000 20000
    let s1 := price_sstore true 0 0 42
    let sMod := price_sstore false 0 42 99
    let s2 := price_sstore false 0 42 0
    let sClear := price_sstore true 10 10 0
    alloc = ⟨16756216, 3222784⟩ ∧
    settled = ⟨48000, 40000, 20000, 40000⟩ ∧
    s1 = ⟨12100, 97920, 0, 0⟩ ∧
    sMod = ⟨100, 0, 0, 0⟩ ∧
    s2 = ⟨100, 0, 10000, 97920⟩ ∧
    sClear = ⟨12100, 0, 11616, 0⟩ := by
  decide

/-! ## 4. `Gloas7732.Spec` (`EIP-7732` + `EIP-8282`) Test Vectors -/

/-- Test Vector 6: `can_builder_cover_bid`, `get_builder_payment_quorum_threshold`,
`settle_builder_payment`, `process_builder_pending_payments`, and `process_builder_deposit_eip8282_patched`. -/
theorem tv_gloas7732_builder_and_quorum_vectors :
    let quorum := get_builder_payment_quorum_threshold 32000000000000 32
    let p1 : BuilderPendingPayment := ⟨600000000000, ⟨0xaa, 5000000, 0⟩, 7⟩
    let p2 : BuilderPendingPayment := ⟨599999999999, ⟨0xbb, 4000000, 1⟩, 8⟩
    let (clearedP1, directSettled) := settle_builder_payment p1 []
    let (_, _, settled) := process_builder_pending_payments quorum [p1, p2] [p1, p2] []
    let topupBal := process_builder_deposit_eip8282_patched {
      pubkeyRegistered := true
      credentialPrefix := 0x00
      signatureValid := false
      currentBalance := 1000000000
      depositAmount := 500000000
    }
    let lifecycleSame := settle_slot_bid_lifecycle 0xaa 5000000 0 7 600000000000 quorum .confirmedSameEpoch
    let lifecycleNext := settle_slot_bid_lifecycle 0xaa 5000000 0 7 0 quorum .confirmedNextEpoch
    let lifecycleTwo := settle_slot_bid_lifecycle 0xaa 5000000 0 7 0 quorum .confirmedAfterTwoEpochs
    let slashedList := slash_validator_pending_payments 7 [p1, p2]
    let traceWt := accrue_attester_weight_trace false 0 32000000000 [true, true, false, true]
    PAYLOAD_BUILDER_VERSION = 0 ∧
    quorum = 600000000000 ∧
    can_builder_cover_bid 2000000000 500000000 500000000 = true ∧
    can_builder_cover_bid 2000000000 500000000 500000001 = false ∧
    clearedP1 = {} ∧
    directSettled = [⟨0xaa, 5000000, 0⟩] ∧
    settled = [⟨0xaa, 5000000, 0⟩] ∧
    lifecycleSame = [⟨0xaa, 5000000, 0⟩] ∧
    lifecycleNext = [⟨0xaa, 5000000, 0⟩] ∧
    lifecycleTwo = [⟨0xaa, 5000000, 0⟩] ∧
    slashedList = [{}, p2] ∧
    traceWt = (true, 32000000000) ∧
    topupBal = 1500000000 := by
  decide

/-! ## 5. `Gas.CallTree` (`FV-CORE` Multi-Frame Call Tree & Refill Variants `D0..D13S`) Test Vectors -/

/-- Test Vector 7: `exec_sstore_frame` (`2300` sentry excluding `stateGasLeft`), `enter_child_frame`,
`exit_child_frame` across `D0`, `D13R`, and `D13S`, and `run_m4_sibling_delta_trace`. -/
theorem tv_calltree_multi_frame_vectors :
    let mSentryBlocked : CallFrameMeter := { meter := { gasLeft := 2300, stateGasLeft := 500000, stateGasBaseline := 500000 } }
    exec_sstore_frame .amsterdamD0 mSentryBlocked false 0 0 1 = none ∧
    run_m4_sibling_delta_trace .amsterdamD0 500000 20000 = some ⟨391980, 469800, true⟩ ∧
    run_m4_sibling_delta_trace .amsterdamD13 500000 20000 = some ⟨391980, 371880, false⟩ ∧
    run_m4_sibling_delta_trace .amsterdamD13R 500000 20000 = some ⟨391980, 469800, true⟩ ∧
    run_m4_sibling_delta_trace .amsterdamD13S 500000 20000 = some ⟨391980, 469800, true⟩ := by
  decide

end Glamsterdam.TestVectors
