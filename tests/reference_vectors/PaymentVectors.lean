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

structure Attester where
  index : Nat
  flags : Nat
  balance : Nat
  deriving FromJson

private def applyAttestation (json : Json) (i : Input) : Except String Json := do
  let voteSlot ← json.getObjValAs? Nat "voteSlot"
  let targetEpoch ← json.getObjValAs? Nat "targetEpoch"
  let head ← json.getObjValAs? String "head"
  let slotRoot ← json.getObjValAs? String "slotRoot"
  let prevRoot ← json.getObjValAs? String "prevRoot"
  let sameSlot := voteSlot == 0 || (head == slotRoot && head != prevRoot)
  let payloadIndex ← json.getObjValAs? Nat "payloadIndex"
  let source ← json.getObjValAs? String "source"
  let justified ← json.getObjValAs? String "justified"
  if source != justified || (sameSlot && payloadIndex != 0) then
    return Json.mkObj [("accepted", toJson false)]
  let targetMatches := (← json.getObjValAs? String "target") == (← json.getObjValAs? String "targetRoot")
  let available ← json.getObjValAs? Bool "available"
  let delay := i.slot - voteSlot
  let timelySource := delay * delay ≤ i.slotsPerEpoch
  let timelyHead := targetMatches && head == slotRoot &&
    (sameSlot || payloadIndex == (if available then 1 else 0)) && delay == (← json.getObjValAs? Nat "minDelay")
  let mask := (if timelySource then 1 else 0) + (if targetMatches then 2 else 0) + (if timelyHead then 4 else 0)
  let current := targetEpoch == i.slot / i.slotsPerEpoch
  let index := (if current then i.slotsPerEpoch else 0) + voteSlot % i.slotsPerEpoch
  let some payment := i.payments[index]? | throw "invalid attestation payment index"
  let mut weight := payment.weight
  let mut flags := #[]
  for v in (← json.getObjValAs? (Array Attester) "attesters") do
    let after := v.flags ||| mask
    if after != v.flags && sameSlot && payment.withdrawal.amount > 0 then
      weight := (accrue_attester_weight (v.flags != 0) weight v.balance).2
    flags := flags.push (v.index, after)
  return Json.mkObj [("accepted", toJson true), ("current", toJson current), ("index", toJson index),
    ("weight", toJson weight), ("flags", toJson flags), ("mask", toJson mask)]

private def applyCase (json : Json) : Except String Json := do
  let handler ← json.getObjValAs? String "handler"
  if handler == "fork" then
    let size ← json.getObjValAs? Nat "size"
    let ring : AvailabilityRing := { size }
    return toJson (ring.getBit (← json.getObjValAs? Nat "slot"))
  if handler == "withdrawals" then
    let mut balances ← json.getObjValAs? (Array Nat) "balances"
    for (index, amount) in (← json.getObjValAs? (Array (Nat × Nat)) "debits") do
      let some balance := balances[index]? | throw "builder debit outside registry"
      balances := balances.set! index (Glamsterdam.Common.Prelude.saturatingSub balance amount)
    return toJson balances
  let i : Input ← fromJson? json
  if i.slotsPerEpoch == 0 || i.payments.length != 2 * i.slotsPerEpoch then
    throw "invalid two-epoch payment window"
  let epoch := i.slot / i.slotsPerEpoch
  if i.handler == "proposer_slashing" then
    return toJson (slash_validator_pending_payments (← json.getObjValAs? Nat "proposer") i.payments)
  if i.handler == "attestation" then return ← applyAttestation json i
  if i.handler == "builder_pending_payments" then
    let validators : List ValidatorBalance ← json.getObjValAs? _ "validators"
    let increment : Nat ← json.getObjValAs? _ "increment"
    let active := validators.foldl (fun total v =>
      if v.activationEpoch ≤ epoch && epoch < v.exitEpoch then total + v.effectiveBalance else total) 0
    let quorum := get_builder_payment_quorum_threshold (max active increment) i.slotsPerEpoch
    let (first, second, withdrawals) := process_builder_pending_payments quorum
      (i.payments.take i.slotsPerEpoch) (i.payments.drop i.slotsPerEpoch) i.withdrawals
    return Json.mkObj [("payments", toJson (first ++ second)), ("withdrawals", toJson withdrawals)]
  if i.handler == "execution_payload_bid" then
    let bid ← json.getObjValAs? BuilderPendingWithdrawal "bid"
    let phase ← json.getObjValAs? String "phase"
    if phase == "coverage" then
      let balance ← json.getObjValAs? Nat "balance"
      let pending := get_pending_balance_to_withdraw_for_builder i.withdrawals i.payments bid.builderIndex
      return Json.mkObj [("covered", toJson (can_builder_cover_bid balance pending bid.amount)),
        ("pending", toJson pending)]
    let proposer ← json.getObjValAs? Nat "proposer"
    let index := i.slotsPerEpoch + i.slot % i.slotsPerEpoch
    let payments := if bid.amount == 0 then i.payments else
      i.payments.set index (paymentForBid bid proposer 0)
    return Json.mkObj [("payments", toJson payments), ("withdrawals", toJson i.withdrawals)]
  if i.handler == "parent_execution_payload" then
    let parentHash ← json.getObjValAs? Nat "parentHash"
    let bidParentHash ← json.getObjValAs? Nat "bidParentHash"
    if !is_canonical_full_slot_payload parentHash ⟨bidParentHash, []⟩ then
      let empty ← json.getObjValAs? Bool "emptyRequests"
      return Json.mkObj [("path", toJson (if empty then "empty_parent" else "reject_empty_requests"))]
    let root ← json.getObjValAs? String "requestsRoot"
    let commitment ← json.getObjValAs? String "requestsCommitment"
    if root != commitment then return Json.mkObj [("path", toJson "reject_commitment")]
    let limits ← json.getObjValAs? (List (Nat × Nat)) "requestLimits"
    if limits.any (fun (size, limit) => size > limit) then
      return Json.mkObj [("path", toJson "reject_limit")]
    let parentSlot ← json.getObjValAs? Nat "parentSlot"
    let parentEpoch := parentSlot / i.slotsPerEpoch
    let same := parentEpoch == epoch
    if same || parentEpoch == epoch - 1 then
      let index := (if same then i.slotsPerEpoch else 0) + parentSlot % i.slotsPerEpoch
      let some payment := i.payments[index]? | throw "payment index outside window"
      let (cleared, withdrawals) := settle_builder_payment payment i.withdrawals
      return Json.mkObj [("path", toJson (if same then "current_epoch" else "previous_epoch")),
        ("payments", toJson (i.payments.set index cleared)), ("withdrawals", toJson withdrawals)]
    let bid ← json.getObjValAs? BuilderPendingWithdrawal "parentBid"
    let withdrawals := appendOlderBid i.withdrawals bid
    return Json.mkObj [("path", toJson "older_parent"), ("payments", toJson i.payments),
      ("withdrawals", toJson withdrawals)]
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
