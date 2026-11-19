import Glamsterdam.Gloas7732.Spec

namespace Glamsterdam.Gloas7732.Spec

/-- Apply the pinned exit request to the registry. The two preset configurations
supply different withdrawability delays. An ignored request is a successful no-op. -/
def applyBuilderExit (builders : List Builder) (pubkey source finalized epoch delay : Nat)
    (payments : List BuilderPendingPayment) (withdrawals : List BuilderPendingWithdrawal) :
    List Builder := Id.run do
  let some index := builders.findIdx? (fun b => b.pubkey == pubkey) | return builders
  let some b := builders[index]? | return builders
  let pending := get_pending_balance_to_withdraw_for_builder withdrawals payments index
  if source == b.executionAddress && can_builder_exit (is_active_builder b finalized) pending then
    return builders.set index { b with withdrawableEpoch := epoch + delay }
  return builders

/-- Pinned credential and existing-builder paths. A new registration with builder
credentials needs signature verification before its registry result is known. -/
def applyBuilderTopUp (builders : List Builder) (pubkey credentialPrefix amount epoch delay : Nat) :
    Option (List Builder) := do
  if credentialPrefix != BUILDER_WITHDRAWAL_PREFIX then return builders
  let index ← builders.findIdx? (fun b => b.pubkey == pubkey)
  let b ← builders[index]?
  let withdrawable := if b.withdrawableEpoch != FAR_FUTURE_EPOCH && b.balance == 0 then
    epoch + delay else b.withdrawableEpoch
  let balance := process_builder_deposit_v170_beta4_buggy
    ⟨true, credentialPrefix, false, b.balance, amount⟩
  return builders.set index { b with balance, withdrawableEpoch := withdrawable }

end Glamsterdam.Gloas7732.Spec
