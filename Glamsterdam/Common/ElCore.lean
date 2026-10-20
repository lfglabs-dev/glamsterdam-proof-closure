/-
  Glamsterdam.Common.ElCore: Shared 16-Function Execution Layer Core
  Pinned against `ethereum/execution-specs` @ `16898000911c1e3caa57be08509536c10ae92d3e`
  (`src/ethereum/forks/amsterdam/`).
  Models the shared state, journal checkpoints, balance transfers, account clearing,
  two-leg gas charging (`gas_left` + `state_gas_reservoir`), and child frame incorporation.
-/
import Glamsterdam.Common.MetaSpec

namespace Glamsterdam.Common.ElCore

open Glamsterdam.Common.MetaSpec

abbrev Address := Nat
abbrev StorageKey := Nat
abbrev StorageVal := Nat

structure Account where
  nonce : Nat := 0
  balance : Nat := 0
  codeEmpty : Bool := true
  storageNonEmpty : Bool := false
  deriving Repr, DecidableEq, BEq

structure WorldSnapshot where
  targetAccount : Account := {}
  recipientBalance : Nat := 0
  createdInTx : Bool := false
  markedToDelete : Bool := false
  deriving Repr, DecidableEq, BEq

structure State where
  current : WorldSnapshot := {}
  snapshots : List WorldSnapshot := []
  deriving Repr, DecidableEq, BEq

structure EvmGasFrame where
  gasLeft : Nat
  stateGasReservoir : Nat
  refundCounter : Nat := 0
  deriving Repr, DecidableEq, BEq

/-! ### 1-3. Journal Checkpoints (`begin_transaction`, `commit_transaction`, `rollback_transaction`) -/

def begin_transaction (s : State) : State :=
  { s with snapshots := s.current :: s.snapshots }

def commit_transaction (s : State) : State :=
  match s.snapshots with
  | _ :: rest => { s with snapshots := rest }
  | [] => s

def rollback_transaction (s : State) : State :=
  match s.snapshots with
  | snap :: rest => { current := snap, snapshots := rest }
  | [] => s

/-- T-COMMON-CHECKPOINT-ROLLBACK: Rolling back after `begin_transaction` and arbitrary
    in-frame mutations restores the exact pre-checkpoint `State`. -/
theorem t_common_checkpoint_rollback (s : State) (mutated : WorldSnapshot) :
    rollback_transaction { (begin_transaction s) with current := mutated } = s := by
  cases s; rfl

/-! ### 4-8. Balance & Account Destruction Primitives (`move_ether`, `clear_account_preserving_balance`, `destroy_storage`) -/

def set_account_balance (acc : Account) (newBalance : Nat) : Account :=
  { acc with balance := newBalance }

def move_ether_self (acc : Account) (amount : Nat) : Option Account :=
  if acc.balance ≥ amount then
    some acc
  else
    none

def move_ether_distinct (senderBalance recipientBalance amount : Nat) : Option (Nat × Nat) :=
  if senderBalance ≥ amount then
    some (senderBalance - amount, recipientBalance + amount)
  else
    none

theorem move_ether_distinct_conserves_sum (s r amount s' r' : Nat)
    (h : move_ether_distinct s r amount = some (s', r')) :
    s' + r' = s + r := by
  unfold move_ether_distinct at h
  split at h <;> simp_all
  omega

def destroy_storage (acc : Account) : Account :=
  { acc with storageNonEmpty := false }

def clear_account_preserving_balance (snap : WorldSnapshot) : WorldSnapshot :=
  if snap.markedToDelete && snap.createdInTx then
    let cleared := destroy_storage { snap.targetAccount with nonce := 0, codeEmpty := true }
    { snap with targetAccount := cleared }
  else
    snap

/-! ### 9-11. Two-Leg Gas Charging (`charge_gas`) & Child Frame Incorporation (`incorporate_child_on_success`, `incorporate_child_on_error`) -/

def charge_gas (frame : EvmGasFrame) (regularGas stateGas : Nat) : Option EvmGasFrame :=
  let spill := if stateGas > frame.stateGasReservoir then stateGas - frame.stateGasReservoir else 0
  let totalRegularNeeded := regularGas + spill
  if frame.gasLeft < totalRegularNeeded then
    none
  else
    let newReservoir := frame.stateGasReservoir - min stateGas frame.stateGasReservoir
    let newGasLeft := frame.gasLeft - totalRegularNeeded
    some { frame with gasLeft := newGasLeft, stateGasReservoir := newReservoir }

def incorporate_child_on_success (parent child : EvmGasFrame) : EvmGasFrame :=
  { parent with
    gasLeft := parent.gasLeft + child.gasLeft
    stateGasReservoir := child.stateGasReservoir
    refundCounter := parent.refundCounter + child.refundCounter }

def incorporate_child_on_error (parent child : EvmGasFrame) : EvmGasFrame :=
  { parent with
    gasLeft := parent.gasLeft + child.gasLeft
    stateGasReservoir := child.stateGasReservoir }

@[inline, export glamsterdam_charge_gas_ok_cabi]
def charge_gas_ok_cabi (gasLeft reservoir regularGas stateGas : UInt64) : Bool :=
  (charge_gas ⟨gasLeft.toNat, reservoir.toNat, 0⟩ regularGas.toNat stateGas.toNat).isSome

end Glamsterdam.Common.ElCore
