import EvmGasSemantics.Theorems.Spec.NeedExact

set_option autoImplicit false
namespace EvmGasSemantics.Spec

/-- Check whether an execution succeeded cleanly (no caught child failures and all reached sites entered),
corresponding to the second-stage predicate of Nethermind PR #15203 (`avoidNestedOutOfGas`). -/
def statusCleanSuccess (r : ForkResult) : Bool :=
  Contract.statusSuccess r &&
    r.frames.all (fun f => f.caught != some true) &&
    r.sites.all (fun s => !s.executed || s.entered)

/-- Two-stage estimator modeling Nethermind PR #15203 (`avoidNestedOutOfGas`):
if the upper bound `cap` succeeds cleanly, bisect for the lowest gas limit with clean success;
otherwise fall back to plain status bisection. -/
def avoidNestedOOGEstimator (cap : Nat) (oracle : Contract.GasOracle) : Except ExecError (Option Nat) := do
  let rCap ← oracle cap
  if !Contract.statusSuccess rCap then return none
  if !statusCleanSuccess rCap then
    return ← Contract.binarySearchEstimator cap oracle
  if statusCleanSuccess (← oracle 0) then return some 0
  return some (← Contract.bisectStatus (fun g => do
    let r ← oracle g
    return { r with tx := if statusCleanSuccess r then r.tx else .invalid g "NestedOutOfGas" }) (cap + 1) 0 cap)

theorem statusCleanSuccess_iff_noCaughtFailure (r : ForkResult)
    (hSucc : Contract.statusSuccess r = true) :
    statusCleanSuccess r = true ↔ NoCaughtFailure r := by
  simp only [statusCleanSuccess, NoCaughtFailure, Bool.and_eq_true, List.all_eq_true,
    Bool.not_eq_true]
  rw [hSucc]
  constructor
  · rintro ⟨hFrames, hSites⟩
    constructor
    · rcases hFrames with ⟨_, hFrames⟩
      intro f hf hCaught
      have h := hFrames f hf
      simp [hCaught] at h
    · intro s hs hex
      have := hSites s hs
      simp [hex] at this
      exact this
  · rintro ⟨hFrames, hSites⟩
    constructor
    · refine ⟨rfl, ?_⟩
      intro f hf
      have h := hFrames f hf
      simp at h ⊢
      exact h
    · intro s hs
      by_cases hex : s.executed = true
      · have he := hSites s hs hex
        simp [he]
      · simp [hex]

theorem runsAsDescribed_iff_statusCleanSuccess (fork : Fork) (c : ElaboratedCase) (g : Nat) :
    RunsAsDescribed fork c g ↔ ∃ r, runAt fork c g = .ok r ∧ statusCleanSuccess r = true := by
  constructor
  · rintro ⟨r, hr, hSucc, hNoCatch⟩
    exact ⟨r, hr, (statusCleanSuccess_iff_noCaughtFailure r hSucc).mpr hNoCatch⟩
  · rintro ⟨r, hr, hClean⟩
    have hSucc : Contract.statusSuccess r = true := by
      simp [statusCleanSuccess] at hClean
      exact hClean.1.1
    exact ⟨r, hr, hSucc, (statusCleanSuccess_iff_noCaughtFailure r hSucc).mp hClean⟩

theorem statusCleanSuccess_monotone (fork : Fork) (c : ElaboratedCase) (g₁ g₂ : Nat)
    (r₁ r₂ : ForkResult)
    (hBranch : NoIfGas c) (hArgs : NoWrappingGasArgs c) (hSender : NoSenderValueTransfer c)
    (hOrder : g₁ ≤ g₂) (hDomain : GasDomain fork c g₂)
    (hRun₁ : runAt fork c g₁ = .ok r₁) (hRun₂ : runAt fork c g₂ = .ok r₂)
    (hClean₁ : statusCleanSuccess r₁ = true) :
    statusCleanSuccess r₂ = true := by
  have hSucc₁ : Contract.statusSuccess r₁ = true := by
    simp [statusCleanSuccess] at hClean₁
    exact hClean₁.1.1
  have hRunDesc₁ : RunsAsDescribed fork c g₁ :=
    (runsAsDescribed_iff_statusCleanSuccess fork c g₁).mpr ⟨r₁, hRun₁, hClean₁⟩
  have hRunDesc₂ : RunsAsDescribed fork c g₂ :=
    runsAsDescribed_monotone fork c g₁ g₂ hBranch hArgs hSender hOrder hDomain hRunDesc₁
  obtain ⟨r, hr, hSucc, hNoCatch⟩ := hRunDesc₂
  cases hr.symm.trans hRun₂
  exact (statusCleanSuccess_iff_noCaughtFailure r₂ hSucc).mpr hNoCatch

end EvmGasSemantics.Spec
