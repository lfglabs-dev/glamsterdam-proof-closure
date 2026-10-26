import EvmGasSemantics.Theorems.Spec.Monotone.Sim.Assembly

/-!
# DESIGN §6: Monotonicity Corollaries (S13, S15) and Least-Gas / Bisection Exactness (S21–S25)

EELS pin: `16898000911c1e3caa57be08509536c10ae92d3e`, both forks'
`fork.py:process_transaction` and `vm/interpreter.py`.
All seven theorem statements match `EvmGasSemantics/Spec/Statements.lean` verbatim.
-/

set_option autoImplicit false
namespace EvmGasSemantics.Spec

private theorem clean_of_success_noCatch (fork : Fork) (c : ElaboratedCase) (g : Nat)
    (hCatch : NoCatch c) (hSuccess : Succeeds fork c g) : CleanAt fork c g := by
  obtain ⟨r, hr, hs⟩ := hSuccess
  have hd := runsAsDescribed_of_succeeds_noCatch fork c g hCatch ⟨r, hr, hs⟩
  rcases hd with ⟨r', hr', hs', hn⟩
  cases hr'.symm.trans hr
  exact ⟨r, hr, (noCaughtFailure_iff_clean fork c g r hr hs).mp hn⟩

/-- S13: All four independent hypotheses are needed. Only the higher budget
needs an explicit domain premise: lower success already implies admission. -/
theorem success_monotone (fork : Fork) (c : ElaboratedCase) (g₁ g₂ : Nat)
    (hBranch : NoIfGas c) (hCatch : NoCatch c)
    (hArgs : NoWrappingGasArgs c) (hSender : NoSenderValueTransfer c)
    (hOrder : g₁ ≤ g₂) (hDomain : GasDomain fork c g₂)
    (hSuccess : Succeeds fork c g₁) :
    Succeeds fork c g₂ := by
  exact (success_monotone_of_clean_trace fork c g₁ g₂ hBranch hArgs hSender hOrder hDomain
    hSuccess (clean_of_success_noCatch fork c g₁ hCatch hSuccess)).1

/-- S15: The stronger success notion also persists, with the same sender
restriction missing from the older clean-trace formalization now explicit. -/
theorem runsAsDescribed_monotone (fork : Fork) (c : ElaboratedCase) (g₁ g₂ : Nat)
    (hBranch : NoIfGas c) (hArgs : NoWrappingGasArgs c)
    (hSender : NoSenderValueTransfer c) (hOrder : g₁ ≤ g₂)
    (hDomain : GasDomain fork c g₂) (hRun : RunsAsDescribed fork c g₁) :
    RunsAsDescribed fork c g₂ := by
  obtain ⟨r, hr, hs, hn⟩ := hRun
  obtain ⟨⟨r₂, hr₂, hs₂⟩, ⟨r₂', hr₂', hc₂⟩⟩ :=
    success_monotone_of_clean_trace fork c g₁ g₂ hBranch hArgs hSender hOrder hDomain
      ⟨r, hr, hs⟩ ⟨r, hr, (noCaughtFailure_iff_clean fork c g₁ r hr hs).mp hn⟩
  cases hr₂'.symm.trans hr₂
  exact ⟨r₂, hr₂, hs₂, (noCaughtFailure_iff_clean fork c g₂ r₂ hr₂ hs₂).mpr hc₂⟩

private def Ensures {α : Type} (p : α → Prop) (act : Exec.M α) : Prop :=
  ∀ m a m', act m = .ok (a, m') → p a

private theorem ensures_bind {α β : Type} {p : β → Prop} (x : Exec.M α) (f : α → Exec.M β)
    (h : ∀ a, Ensures p (f a)) : Ensures p (x >>= f) := by
  intro m b m' hx
  simp only [bind, StateT.bind, Except.bind] at hx
  split at hx
  · contradiction
  · exact h _ _ _ _ hx

private theorem ensures_ite {α : Type} {p : α → Prop} (b : Prop) [Decidable b]
    (x y : Exec.M α) (hx : Ensures p x) (hy : Ensures p y) :
    Ensures p (if b then x else y) := by
  split <;> assumption

private theorem transaction_signature_isSuccess (c : ElaboratedCase) (i : Tx.IntrinsicCost)
    (a : Tx.Allocation) : Ensures (fun r => (Need.signature r).isSuccess = Contract.statusSuccess r)
    (Exec.transaction c i a) := by
  unfold Exec.transaction
  apply ensures_bind; intro s0
  apply ensures_bind; intro entry
  apply ensures_bind; intro refund
  apply ensures_bind; intro s1
  extract_lets target finish dispatch plan create resolve
  have hf (cs : Option CodeStart) :
      Ensures (fun r => (Need.signature r).isSuccess = Contract.statusSuccess r) (finish cs) := by
    unfold finish
    apply ensures_bind; intro top
    extract_lets top'
    apply ensures_bind; intro u
    apply ensures_bind; intro s
    extract_lets jp
    split
    · intro m b m' hx
      cases hx
    · intro m b m' hx
      cases hx
      cases top.outcome <;> rfl
  have hd (code : Nat) :
      Ensures (fun r => (Need.signature r).isSuccess = Contract.statusSuccess r) (dispatch code) := by
    unfold dispatch
    apply ensures_bind; intro running
    apply ensures_ite
    · apply ensures_bind; intro s
      apply ensures_bind; intro u
      apply ensures_bind; intro u
      apply ensures_bind; intro u
      apply ensures_bind; intro u
      extract_lets next
      have hn (u : Unit) :
          Ensures (fun r => (Need.signature r).isSuccess = Contract.statusSuccess r) (next u) := by
        unfold next
        apply ensures_bind; intro u
        apply ensures_bind; intro cs
        exact hf cs
      apply ensures_ite
      · apply ensures_bind; intro u; exact hn u
      · apply ensures_bind; intro u
        apply ensures_bind; intro u
        apply ensures_ite
        · apply ensures_bind; intro u; exact hn u
        · exact hn ()
    · apply ensures_bind; intro s
      apply ensures_bind; intro meters
      apply ensures_bind; intro u
      apply ensures_bind; intro cs
      exact hf cs
  have hc (u : Unit) :
      Ensures (fun r => (Need.signature r).isSuccess = Contract.statusSuccess r) (create u) := by
    unfold create
    apply ensures_bind; intro u
    apply ensures_bind; intro code
    exact hd code
  have hr (code : Nat) :
      Ensures (fun r => (Need.signature r).isSuccess = Contract.statusSuccess r) (resolve code) := by
    unfold resolve
    apply ensures_bind; intro running
    apply ensures_bind; intro s
    apply ensures_ite
    · apply ensures_bind; intro s
      apply ensures_bind; intro u
      apply ensures_bind; intro u
      apply ensures_bind; intro code
      exact hd code
    · apply ensures_bind; intro code
      exact hd code
  apply ensures_ite
  · apply ensures_ite
    · apply ensures_bind; intro u; exact hc u
    · exact hc ()
  · apply ensures_bind; intro u
    apply ensures_bind; intro running
    apply ensures_ite
    · apply ensures_bind; intro s
      apply ensures_bind; intro code
      exact hr code
    · apply ensures_bind; intro code
      exact hr code

theorem runAt_signature_isSuccess (fork : Fork) (c : ElaboratedCase) (g : Nat)
    (r : ForkResult) (hRun : runAt fork c g = .ok r) :
    (Need.signature r).isSuccess = Contract.statusSuccess r := by
  have h := hRun
  have hw := wellFormed_of_run _ _ _ h
  unfold runAt Exec.run at h
  simp only [hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat all_goals first
    | contradiction
    | (solve | cases h; rfl)
    | (split at h)
  all_goals try contradiction
  cases h
  exact transaction_signature_isSuccess _ _ _ _ _ _ (by assumption)

private theorem outcomeAt_isSuccess_iff (fork : Fork) (c : ElaboratedCase) (g : Nat) :
    (∃ s, Need.outcomeAt fork c g = .ok s ∧ s.isSuccess = true) ↔ Succeeds fork c g := by
  constructor
  · rintro ⟨s, hs, hsucc⟩
    change (runAt fork c g).map Need.signature = .ok s at hs
    cases hr : runAt fork c g with
    | error e => simp [hr, Except.map] at hs
    | ok r =>
      simp only [hr, Except.map, Except.ok.injEq] at hs
      subst s
      rw [runAt_signature_isSuccess fork c g r hr] at hsucc
      exact ⟨r, hr, hsucc⟩
  · rintro ⟨r, hr, hsucc⟩
    refine ⟨Need.signature r, ?_, ?_⟩
    · change (runAt fork c g).map Need.signature = .ok (Need.signature r)
      simp [hr, Except.map]
    · rw [runAt_signature_isSuccess fork c g r hr]
      exact hsucc

private theorem not_succeeds_of_need_none (fork : Fork) (c : ElaboratedCase) (g : Nat)
    (hNone : Need.need fork c = .ok none) : ¬ Succeeds fork c g := by
  intro hS
  have hDom := succeeds_gasDomain fork c g hS
  rcases hS with ⟨r, hr, hsucc⟩
  have hout : Need.outcomeAt fork c g = .ok (Need.signature r) := by
    change (runAt fork c g).map Need.signature = .ok (Need.signature r)
    simp [hr, Except.map]
  have hfalse := Need.need_none hNone (Nat.zero_le g) hDom.1 hout
  rw [runAt_signature_isSuccess fork c g r hr] at hfalse
  rw [hsucc] at hfalse
  contradiction

private theorem not_succeeds_of_lt_need_some (fork : Fork) (c : ElaboratedCase) (n k : Nat)
    (hSome : Need.need fork c = .ok (some n)) (hkn : k < n) : ¬ Succeeds fork c k := by
  intro hS
  rcases hS with ⟨r, hr, hsucc⟩
  have hout : Need.outcomeAt fork c k = .ok (Need.signature r) := by
    change (runAt fork c k).map Need.signature = .ok (Need.signature r)
    simp [hr, Except.map]
  have hfalse := (Need.need_some hSome).2.2.2 k (Nat.zero_le k) hkn (Need.signature r) hout
  rw [runAt_signature_isSuccess fork c k r hr] at hfalse
  rw [hsucc] at hfalse
  contradiction

/-- S21: Unconditional least-success characterization is already `Need.need_some`
and `Need.need_none`; the new content is upward closure under the four hypotheses.
Impossible supported paths have `.ok none` and neither side holds at any budget. -/
theorem need_exact (fork : Fork) (c : ElaboratedCase) (g : Nat)
    (hSupport : Supported fork c) (hBranch : NoIfGas c) (hCatch : NoCatch c)
    (hArgs : NoWrappingGasArgs c) (hSender : NoSenderValueTransfer c) :
    Succeeds fork c g ↔ GasDomain fork c g ∧ MeetsNeed (Need.need fork c) g := by
  obtain ⟨opt, hNeed⟩ := (need_returns_iff_supported fork c).mpr hSupport
  cases opt with
  | none =>
    constructor
    · intro hS
      exact False.elim (not_succeeds_of_need_none fork c g hNeed hS)
    · rintro ⟨_, n, hn, _⟩
      rw [hNeed] at hn
      cases hn
  | some n =>
    have hSome := Need.need_some hNeed
    have hSn : Succeeds fork c n := (outcomeAt_isSuccess_iff fork c n).mp hSome.2.2.1
    constructor
    · intro hS
      refine ⟨succeeds_gasDomain fork c g hS, n, hNeed, ?_⟩
      by_cases hng : n ≤ g
      · exact hng
      · exact False.elim (not_succeeds_of_lt_need_some fork c n g hNeed (by omega) hS)
    · rintro ⟨hDom, m, hm, hmg⟩
      rw [hNeed] at hm
      cases hm
      exact success_monotone fork c n g hBranch hCatch hArgs hSender hmg hDom hSn

/-- S22: Under NoCatch the same least receipt-success limit characterizes
RunsAsDescribed. No second need function or alternate success search is introduced. -/
theorem need_exact_runsAsDescribed (fork : Fork) (c : ElaboratedCase) (g : Nat)
    (hSupport : Supported fork c) (hBranch : NoIfGas c) (hCatch : NoCatch c)
    (hArgs : NoWrappingGasArgs c) (hSender : NoSenderValueTransfer c) :
    RunsAsDescribed fork c g ↔ GasDomain fork c g ∧ MeetsNeed (Need.need fork c) g := by
  rw [← need_exact fork c g hSupport hBranch hCatch hArgs hSender]
  constructor
  · rintro ⟨r, hr, hs, _⟩
    exact ⟨r, hr, hs⟩
  · intro hS
    exact runsAsDescribed_of_succeeds_noCatch fork c g hCatch hS

/-- S23: For a path with catch syntax, cleanliness must hold at the actual least
receipt success, not merely at an arbitrary high successful reference. A caught
success below that reference would otherwise falsify exactness for RunsAsDescribed. -/
theorem need_exact_of_clean_trace (fork : Fork) (c : ElaboratedCase) (n g : Nat)
    (hBranch : NoIfGas c) (hArgs : NoWrappingGasArgs c) (hSender : NoSenderValueTransfer c)
    (hNeed : Need.need fork c = .ok (some n)) (hClean : CleanAt fork c n) :
    (Succeeds fork c g ↔ GasDomain fork c g ∧ n ≤ g) ∧
    (RunsAsDescribed fork c g ↔ GasDomain fork c g ∧ n ≤ g) := by
  have hSome := Need.need_some hNeed
  have hSn : Succeeds fork c n := (outcomeAt_isSuccess_iff fork c n).mp hSome.2.2.1
  have hSucceedsIff : Succeeds fork c g ↔ GasDomain fork c g ∧ n ≤ g := by
    constructor
    · intro hS
      refine ⟨succeeds_gasDomain fork c g hS, ?_⟩
      by_cases hng : n ≤ g
      · exact hng
      · exact False.elim (not_succeeds_of_lt_need_some fork c n g hNeed (by omega) hS)
    · rintro ⟨hDom, hng⟩
      exact (success_monotone_of_clean_trace fork c n g hBranch hArgs hSender hng hDom hSn hClean).1
  refine ⟨hSucceedsIff, ?_⟩
  constructor
  · rintro ⟨r, hr, hs, _⟩
    exact hSucceedsIff.mp ⟨r, hr, hs⟩
  · rintro ⟨hDom, hng⟩
    obtain ⟨⟨r, hr, hs⟩, ⟨r', hr', hclean⟩⟩ :=
      success_monotone_of_clean_trace fork c n g hBranch hArgs hSender hng hDom hSn hClean
    cases hr'.symm.trans hr
    exact ⟨r, hr, hs, (noCaughtFailure_iff_clean fork c g r hr hs).mpr hclean⟩

private theorem maxGasLimit_le_cap (fork : Fork) (c : ElaboratedCase) :
    maxGasLimit fork c ≤ fork.schedule.txGasLimitCap := by
  unfold maxGasLimit
  dsimp only
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.le_refl _
    · exact Nat.min_le_left _ _

/-- S25: The estimator also finds a least receipt success whose lower trace is
clean, even if the syntax allows catching. `hNeed` already entails a supported scan. -/
theorem bisectEstimate_eq_need_of_clean_trace (fork : Fork) (c : ElaboratedCase) (n : Nat)
    (hBranch : NoIfGas c) (hArgs : NoWrappingGasArgs c) (hSender : NoSenderValueTransfer c)
    (hNeed : Need.need fork c = .ok (some n)) (hClean : CleanAt fork c n) :
    bisectEstimate fork c = .ok (some n) := by
  have hSupport : Supported fork c := (need_returns_iff_supported fork c).mp ⟨some n, hNeed⟩
  have hExact := (need_exact_of_clean_trace fork c n · hBranch hArgs hSender hNeed hClean)
  have hSn : Succeeds fork c n := (Need.need_some hNeed).2.2.1 |> (outcomeAt_isSuccess_iff fork c n).mp
  have hDomN : GasDomain fork c n := succeeds_gasDomain fork c n hSn
  have hMaxN := (gasDomain_iff_le_maxGasLimit fork c n).mp hDomN
  apply binarySearchEstimator_eq_threshold (runAt fork c) n (maxGasLimit fork c) hMaxN.2
  intro g hg
  have hCapG : g ≤ fork.schedule.txGasLimitCap := Nat.le_trans hg (maxGasLimit_le_cap fork c)
  obtain ⟨r, hr⟩ := hSupport g hCapG
  have hDomG : GasDomain fork c g := (gasDomain_iff_le_maxGasLimit fork c g).mpr ⟨hMaxN.1, hg⟩
  refine ⟨r, hr, ?_⟩
  constructor
  · intro hs
    exact ((hExact g).1.mp ⟨r, hr, hs⟩).2
  · intro hng
    obtain ⟨r', hr', hs'⟩ := (hExact g).1.mpr ⟨hDomG, hng⟩
    cases hr'.symm.trans hr
    exact hs'

/-- S24: The status-based binary-search estimate equals the exact least success
under the four hypotheses. Supported impossible paths yield `.ok none` on both sides. -/
theorem bisectEstimate_eq_need (fork : Fork) (c : ElaboratedCase)
    (hSupport : Supported fork c) (hBranch : NoIfGas c) (hCatch : NoCatch c)
    (hArgs : NoWrappingGasArgs c) (hSender : NoSenderValueTransfer c) :
    bisectEstimate fork c = Need.need fork c := by
  obtain ⟨opt, hNeed⟩ := (need_returns_iff_supported fork c).mpr hSupport
  cases opt with
  | none =>
    rw [hNeed]
    have hCap := maxGasLimit_le_cap fork c
    obtain ⟨rCap, hrCap⟩ := hSupport (maxGasLimit fork c) hCap
    have hNotS : ¬ Succeeds fork c (maxGasLimit fork c) :=
      not_succeeds_of_need_none fork c (maxGasLimit fork c) hNeed
    have hFalse : Contract.statusSuccess rCap = false := by
      cases hs : Contract.statusSuccess rCap with
      | false => rfl
      | true => exact False.elim (hNotS ⟨rCap, hrCap, hs⟩)
    unfold bisectEstimate Contract.binarySearchEstimator
    simp [hrCap, bind, Except.bind, pure, Except.pure, hFalse]
  | some n =>
    rw [hNeed]
    have hSn : Succeeds fork c n := (Need.need_some hNeed).2.2.1 |> (outcomeAt_isSuccess_iff fork c n).mp
    have hClean : CleanAt fork c n := by
      obtain ⟨r, hr, hs, hn⟩ := runsAsDescribed_of_succeeds_noCatch fork c n hCatch hSn
      exact ⟨r, hr, (noCaughtFailure_iff_clean fork c n r hr hs).mp hn⟩
    exact bisectEstimate_eq_need_of_clean_trace fork c n hBranch hArgs hSender hNeed hClean

#print axioms success_monotone
#print axioms runsAsDescribed_monotone
#print axioms runAt_signature_isSuccess
#print axioms need_exact
#print axioms need_exact_runsAsDescribed
#print axioms need_exact_of_clean_trace
#print axioms bisectEstimate_eq_need_of_clean_trace
#print axioms bisectEstimate_eq_need

end EvmGasSemantics.Spec
