import Lean.Data.Json
import Glamsterdam.Gloas7732.Spec

open Lean Glamsterdam.Gloas7732.Spec

deriving instance FromJson, ToJson for BuilderPendingWithdrawal
deriving instance FromJson, ToJson for BuilderPendingPayment

structure PaymentInput where
  totalActiveBalance : Nat
  slotsPerEpoch : Nat
  payments : List BuilderPendingPayment
  withdrawals : List BuilderPendingWithdrawal
  deriving FromJson

/-- Test-only ABI. Python supplies the ordered pre-state window and active balance.
Lean computes the quorum, rotates the window and emits the two post-state queues. -/
@[export glamsterdam_replay_payment_window]
def replayPaymentWindow (input : String) : String := Id.run do
  let result := do
    let data : PaymentInput ← fromJson? (← Json.parse input)
    if data.slotsPerEpoch == 0 || data.payments.length != 2 * data.slotsPerEpoch then
      throw "invalid two-epoch payment window"
    let quorum := get_builder_payment_quorum_threshold data.totalActiveBalance data.slotsPerEpoch
    let (first, second, withdrawals) := process_builder_pending_payments quorum
      (data.payments.take data.slotsPerEpoch) (data.payments.drop data.slotsPerEpoch) data.withdrawals
    pure (Json.mkObj [("payments", toJson (first ++ second)), ("withdrawals", toJson withdrawals)])
  match result with
  | .ok output => return output.compress
  | .error message => return (Json.mkObj [("error", toJson message)]).compress
