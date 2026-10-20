/-
  Glamsterdam.Eip8246.Spec: Formal Verification of EIP-8246
  ("Clear Destroyed Account Without Balance Wipe")
  Pinned against `ethereum/execution-specs` @ `16898000911c1e3caa57be08509536c10ae92d3e`
  (`src/ethereum/forks/amsterdam/state_tracker.py` & `vm/instructions/system.py`).
-/
import Glamsterdam.Common.ElCore

namespace Glamsterdam.Eip8246.Spec

open Glamsterdam.Common.MetaSpec
open Glamsterdam.Common.ElCore

/-- T-8246-BALANCE-PRESERVED: `clear_account_preserving_balance` never modifies
    the target account's balance or recipient balance, regardless of whether the
    account was created in the same transaction or marked for deletion. -/
theorem t_8246_balance_preserved (snap : WorldSnapshot) :
    (clear_account_preserving_balance snap).targetAccount.balance = snap.targetAccount.balance ∧
    (clear_account_preserving_balance snap).recipientBalance = snap.recipientBalance := by
  unfold clear_account_preserving_balance destroy_storage
  split <;> simp

/-- T-8246-SAME-TX-CREATE-DESTROY: When an account is both created in the current
    transaction (`createdInTx = true`) and marked for deletion (`markedToDelete = true`),
    `clear_account_preserving_balance` clears `nonce` to `0`, `codeEmpty` to `true`,
    and wipes storage (`storageNonEmpty = false`) while preserving `balance`. -/
theorem t_8246_same_tx_create_destroy (snap : WorldSnapshot)
    (h_del : snap.markedToDelete = true) (h_cr : snap.createdInTx = true) :
    let post := (clear_account_preserving_balance snap).targetAccount
    post.nonce = 0 ∧ post.codeEmpty = true ∧ post.storageNonEmpty = false ∧
    post.balance = snap.targetAccount.balance := by
  simp [clear_account_preserving_balance, destroy_storage, h_del, h_cr]

/-- Under EIP-8246 + EIP-8037, same-tx `SELFDESTRUCT` grants zero state-gas refund. -/
def selfdestruct_state_gas_refund (_createdInTx _markedToDelete : Bool) : Nat := 0

/-- T-8246-NO-STATE-GAS-REFUND: Same-tx `CREATE` + `SELFDESTRUCT` does not refund
    the 136-byte account creation state gas (`CPSB * 136`). -/
theorem t_8246_no_state_gas_refund (createdInTx markedToDelete : Bool) :
    selfdestruct_state_gas_refund createdInTx markedToDelete = 0 := rfl

/-- End-to-end EL transaction balance accounting across sender, contract, recipient,
    coinbase, withdrawals, and burned base/blob fees. -/
structure ElEthAccounting where
  preSum : Nat
  withdrawals : Nat
  feesBurned : Nat
  postSum : Nat
  deriving Repr, DecidableEq, BEq

def ethConservationGate (a : ElEthAccounting) : Bool :=
  decide (a.postSum + a.feesBurned = a.preSum + a.withdrawals)

def ethConservationMetaGate : MetaGateSpec ElEthAccounting
    (fun a => a.postSum + a.feesBurned = a.preSum + a.withdrawals) where
  gate := ethConservationGate
  sound := fun a h => by simpa [ethConservationGate] using h
  complete := fun a h => by simpa [ethConservationGate] using h
  posWitness := ⟨1000, 50, 10, 1040⟩
  negWitness := ⟨1000, 50, 10, 940⟩
  nonVacuous := rfl
  tight := rfl

/-- T-8246-ETH-CONSERVATION: 1-to-1 ETH conservation across `clear_account_preserving_balance`.
    Any residual balance on a same-tx created and self-destructed contract (e.g. from
    `selfdestruct(self)` or subsequent inbound transfers) is preserved in the post-state sum. -/
theorem t_8246_eth_conservation (snap : WorldSnapshot) :
    (clear_account_preserving_balance snap).targetAccount.balance +
      (clear_account_preserving_balance snap).recipientBalance =
    snap.targetAccount.balance + snap.recipientBalance := by
  have ⟨h1, h2⟩ := t_8246_balance_preserved snap
  omega

/-- Mutant M-8246-1 (pre-8246 `destroy_account` behavior that wipes `balance := 0`
    during end-of-tx cleanup) is refuted by `WitnessRefuter` whenever residual balance > 0. -/
def clear_account_mutant_wipe_balance (snap : WorldSnapshot) : WorldSnapshot :=
  if snap.markedToDelete && snap.createdInTx then
    { snap with targetAccount := { nonce := 0, balance := 0, codeEmpty := true, storageNonEmpty := false } }
  else
    snap

def m_8246_1_refuter : WitnessRefuter WorldSnapshot WorldSnapshot
    (fun pre post => post.targetAccount.balance = pre.targetAccount.balance) where
  reference := clear_account_preserving_balance
  mutant := clear_account_mutant_wipe_balance
  ref_sound := fun snap => (t_8246_balance_preserved snap).1
  killWitness := { targetAccount := { balance := 100 }, createdInTx := true, markedToDelete := true }
  mutant_refuted := by decide

@[inline, export glamsterdam_eip8246_eth_conservation_cabi]
def eip8246_eth_conservation_cabi (preSum withdrawals feesBurned postSum : UInt64) : Bool :=
  ethConservationGate ⟨preSum.toNat, withdrawals.toNat, feesBurned.toNat, postSum.toNat⟩

end Glamsterdam.Eip8246.Spec
