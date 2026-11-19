import Lean.Data.Json
import Glamsterdam.Gloas7732.BuilderRequests
import Glamsterdam.Gloas7732.PayloadAttestation

open Lean Glamsterdam.Gloas7732.Spec

deriving instance FromJson, ToJson for BuilderPendingWithdrawal
deriving instance FromJson, ToJson for BuilderPendingPayment
deriving instance FromJson, ToJson for Builder

structure ValidatorBalance where
  activationEpoch : Nat
  exitEpoch : Nat
  effectiveBalance : Nat
  deriving FromJson

structure Input where
  handler : String
  slot : Nat
  slotsPerEpoch : Nat
  payments : List BuilderPendingPayment
  withdrawals : List BuilderPendingWithdrawal
  deriving FromJson

private def applyCase (json : Json) : Except String Json := do
  let i : Input ← fromJson? json
  if i.slotsPerEpoch == 0 || i.payments.length != 2 * i.slotsPerEpoch then
    throw "invalid two-epoch payment window"
  let epoch := i.slot / i.slotsPerEpoch
  if i.handler == "builder_pending_payments" then
    let validators : List ValidatorBalance ← json.getObjValAs? _ "validators"
    let increment : Nat ← json.getObjValAs? _ "increment"
    let active := validators.foldl (fun total v =>
      if v.activationEpoch ≤ epoch && epoch < v.exitEpoch then total + v.effectiveBalance else total) 0
    let quorum := get_builder_payment_quorum_threshold (max active increment) i.slotsPerEpoch
    let (first, second, withdrawals) := process_builder_pending_payments quorum
      (i.payments.take i.slotsPerEpoch) (i.payments.drop i.slotsPerEpoch) i.withdrawals
    return Json.mkObj [("payments", toJson (first ++ second)), ("withdrawals", toJson withdrawals)]
  if i.handler == "payload_attestation" then
    let attestedSlot ← json.getObjValAs? Nat "attestedSlot"
    let indices := Glamsterdam.Gloas7732.payloadAttesters i.slot attestedSlot i.slotsPerEpoch
      (← json.getObjValAs? Nat "gloasEpoch") (← json.getObjValAs? Nat "parentRoot")
      (← json.getObjValAs? Nat "attestedRoot") (← json.getObjValAs? (Array (Array Nat)) "window")
      (← json.getObjValAs? (Array Bool) "bits")
    let some signers := indices | return Json.mkObj [("accepted", toJson false)]
    if let some result ← json.getObjValAs? (Option Bool) "verifiedSignature" then
      return Json.mkObj [("accepted", toJson result)]
    let keys ← json.getObjValAs? (Array Nat) "pubkeys"
    let some pubkeys := signers.mapM (fun index => keys[index]?) | throw "PTC index outside registry"
    let forkEpoch ← json.getObjValAs? Nat "forkEpoch"
    let versionField := if attestedSlot / i.slotsPerEpoch < forkEpoch then "previousVersion" else "currentVersion"
    return Json.mkObj [("signers", toJson pubkeys), ("version", ← json.getObjVal? versionField)]
  let builders ← json.getObjValAs? (List Builder) "builders"
  let pubkey ← json.getObjValAs? Nat "pubkey"
  let delay ← json.getObjValAs? Nat "delay"
  if i.handler == "builder_exit_request" then
    let source ← json.getObjValAs? Nat "source"
    let finalized ← json.getObjValAs? Nat "finalized"
    return Json.mkObj [("builders", toJson (applyBuilderExit builders pubkey source finalized
      epoch delay i.payments i.withdrawals))]
  if i.handler == "builder_deposit_request" then
    let credentialPrefix ← json.getObjValAs? Nat "prefix"
    let amount ← json.getObjValAs? Nat "amount"
    match applyBuilderTopUp builders pubkey credentialPrefix amount epoch delay with
    | some result => return Json.mkObj [("builders", toJson result)]
    | none =>
      let valid ← json.getObjValAs? (Option Bool) "verifiedSignature"
      match valid with
      | none => return Json.mkObj [("verifyBuilderSignature", toJson true)]
      | some result =>
        let credentials ← json.getObjValAs? Nat "credentials"
        return Json.mkObj [("builders", toJson
          (registerBuilder builders pubkey credentials amount epoch result))]
  throw "unknown handler"

/-- Compiled transitions emit replacements for the fields they own. Other SSZ
fields retain their pre-state values during serialization of the post-state. -/
@[export glamsterdam_replay_payment_window]
def replayPaymentWindow (input : String) : String :=
  match Json.parse input >>= applyCase with
  | .ok output => output.compress
  | .error message => (Json.mkObj [("error", toJson message)]).compress
