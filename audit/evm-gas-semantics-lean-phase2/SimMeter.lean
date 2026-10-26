import EvmGasSemantics.Theorems.Spec.Monotone
import EvmGasSemantics.Theorems.Meter
import EvmGasSemantics.Theorems.MeterReach

set_option autoImplicit false
namespace EvmGasSemantics.Spec

open EvmGasSemantics

/-- Two meters tracking a lower run `(G₁, R₁)` and a higher run `(G₂, R₂)` that have executed
the exact same clean sequence of frame-local operations (sharing ledger `l` and refund `ref`). -/
structure DualBalanced (G₁ R₁ G₂ R₂ : Nat) (m₁ m₂ : Meter) (l : Ledger) (ref : Int) : Prop where
  le : MeterLE m₁ m₂
  bal₁ : Balanced G₁ R₁ m₁ l
  bal₂ : Balanced G₂ R₂ m₂ l
  ref₁ : m₁.refund = ref
  ref₂ : m₂.refund = ref

theorem dualBalanced_fresh {G₁ R₁ G₂ R₂ : Nat}
    (hG : G₁ ≤ G₂) (hR : R₁ ≤ R₂) :
    DualBalanced G₁ R₁ G₂ R₂ (Meter.fresh G₁ R₁) (Meter.fresh G₂ R₂) {} 0 := by
  refine ⟨?_, Balanced.fresh G₁ R₁, Balanced.fresh G₂ R₂, by simp [Meter.fresh], by simp [Meter.fresh]⟩
  constructor <;> simp [Meter.fresh] <;> omega

theorem dualBalanced_charge {G₁ R₁ G₂ R₂ n : Nat} {m₁ m₂ m₁' : Meter} {l : Ledger} {ref : Int}
    (h : DualBalanced G₁ R₁ G₂ R₂ m₁ m₂ l ref)
    (hc₁ : m₁.charge n = .ok m₁') :
    ∃ m₂', m₂.charge n = .ok m₂' ∧
      DualBalanced G₁ R₁ G₂ R₂ m₁' m₂' (l + { execUsed := n }) ref := by
  obtain ⟨m₂', hc₂, hle⟩ := meterLE_charge h.le hc₁
  refine ⟨m₂', hc₂, ?_⟩
  have ho₁ : FrameOp.apply R₁ (.charge n) m₁ = .ok m₁' := by simpa [FrameOp.apply] using hc₁
  have ho₂ : FrameOp.apply R₂ (.charge n) m₂ = .ok m₂' := by simpa [FrameOp.apply] using hc₂
  have hr₁ : m₁'.refund = ref := by obtain ⟨_, rfl⟩ := charge_ok hc₁; exact h.ref₁
  have hr₂ : m₂'.refund = ref := by obtain ⟨_, rfl⟩ := charge_ok hc₂; exact h.ref₂
  refine ⟨hle, ?_, ?_, hr₁, hr₂⟩
  · simpa [FrameOp.entry] using h.bal₁.step ho₁
  · simpa [FrameOp.entry] using h.bal₂.step ho₂

theorem dualBalanced_chargeState {G₁ R₁ G₂ R₂ n : Nat} {m₁ m₂ m₁' : Meter} {l : Ledger} {ref : Int}
    (h : DualBalanced G₁ R₁ G₂ R₂ m₁ m₂ l ref)
    (hc₁ : m₁.chargeState n = .ok m₁') :
    ∃ m₂', m₂.chargeState n = .ok m₂' ∧
      DualBalanced G₁ R₁ G₂ R₂ m₁' m₂' (l + { stateUsed := n }) ref := by
  obtain ⟨m₂', hc₂, hle⟩ := meterLE_chargeState h.le hc₁
  refine ⟨m₂', hc₂, ?_⟩
  have ho₁ : FrameOp.apply R₁ (.chargeState n) m₁ = .ok m₁' := by simpa [FrameOp.apply] using hc₁
  have ho₂ : FrameOp.apply R₂ (.chargeState n) m₂ = .ok m₂' := by simpa [FrameOp.apply] using hc₂
  have hr₁ : m₁'.refund = ref := by rcases chargeState_ok hc₁ with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> exact h.ref₁
  have hr₂ : m₂'.refund = ref := by rcases chargeState_ok hc₂ with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> exact h.ref₂
  refine ⟨hle, ?_, ?_, hr₁, hr₂⟩
  · simpa [FrameOp.entry] using h.bal₁.step ho₁
  · simpa [FrameOp.entry] using h.bal₂.step ho₂

theorem dualBalanced_creditStateRefund {G₁ R₁ G₂ R₂ n : Nat} {m₁ m₂ : Meter} {l : Ledger} {ref : Int}
    (h : DualBalanced G₁ R₁ G₂ R₂ m₁ m₂ l ref) :
    DualBalanced G₁ R₁ G₂ R₂ (m₁.creditStateRefund n) (m₂.creditStateRefund n)
      (l + { stateUsed := -(n : Int) }) ref := by
  refine ⟨meterLE_creditStateRefund h.le n, ?_, ?_, h.ref₁, h.ref₂⟩
  · obtain ⟨he, hs, hbase⟩ := h.bal₁
    unfold Meter.creditStateRefund
    constructor <;> simp <;> omega

  · obtain ⟨he, hs, hbase⟩ := h.bal₂
    unfold Meter.creditStateRefund
    constructor <;> simp <;> omega

theorem dualBalanced_addRefund {G₁ R₁ G₂ R₂ : Nat} {m₁ m₂ : Meter} {l : Ledger} {ref d : Int}
    (h : DualBalanced G₁ R₁ G₂ R₂ m₁ m₂ l ref) :
    DualBalanced G₁ R₁ G₂ R₂ (m₁.addRefund d) (m₂.addRefund d) l (ref + d) := by
  obtain ⟨hg, hr, hs, hf⟩ := h.le
  have hle : MeterLE (m₁.addRefund d) (m₂.addRefund d) := by
    constructor <;> simp [Meter.addRefund] <;> omega
  refine ⟨hle, ?_, ?_, ?_, ?_⟩
  · obtain ⟨he, hst, hb⟩ := h.bal₁
    exact ⟨by simpa [Meter.addRefund] using he, by simpa [Meter.addRefund] using hst, by simpa [Meter.addRefund] using hb⟩
  · obtain ⟨he, hst, hb⟩ := h.bal₂
    exact ⟨by simpa [Meter.addRefund] using he, by simpa [Meter.addRefund] using hst, by simpa [Meter.addRefund] using hb⟩
  · simpa [Meter.addRefund] using congrArg (fun x => x + d) h.ref₁
  · simpa [Meter.addRefund] using congrArg (fun x => x + d) h.ref₂

theorem dualBalanced_commitState {G₁ R₁ G₂ R₂ : Nat} {m₁ m₂ m₁' : Meter} {l : Ledger} {ref : Int}
    (h : DualBalanced G₁ R₁ G₂ R₂ m₁ m₂ l ref)
    (hc₁ : m₁.commitState = .ok m₁')
    (hcond₂ : m₂.stateLeft ≤ m₂.stateBaseline) :
    ∃ m₂', m₂.commitState = .ok m₂' ∧ DualBalanced G₁ R₁ G₂ R₂ m₁' m₂' l ref := by
  have hc₁_orig := hc₁
  unfold Meter.commitState at hc₁
  split at hc₁
  · simp only [Except.ok.injEq] at hc₁
    subst hc₁
    have hc₂ : m₂.commitState = .ok
        { m₂ with
          stateCommittedSpill := m₂.stateCommittedSpill + m₂.stateSpilled
          stateBaseline := m₂.stateLeft
          stateSpilled := 0 } := by
      simp [Meter.commitState, hcond₂]
    refine ⟨_, hc₂, ?_⟩
    have hle : MeterLE
        { m₁ with
          stateCommittedSpill := m₁.stateCommittedSpill + m₁.stateSpilled
          stateBaseline := m₁.stateLeft
          stateSpilled := 0 }
        { m₂ with
          stateCommittedSpill := m₂.stateCommittedSpill + m₂.stateSpilled
          stateBaseline := m₂.stateLeft
          stateSpilled := 0 } := by
      obtain ⟨hg, hr, hs', hf⟩ := h.le
      constructor <;> dsimp <;> omega
    refine ⟨hle, ?_, ?_, h.ref₁, h.ref₂⟩
    · obtain ⟨he, hst, hb⟩ := h.bal₁
      constructor <;> dsimp <;> omega
    · obtain ⟨he, hst, hb⟩ := h.bal₂
      constructor <;> dsimp <;> omega
  · cases hc₁

theorem dualBalanced_incorporateChild_success
    {G₁ R₁ G₂ R₂ w₁ w₂ stip : Nat} {p₁ p₂ c₁ c₂ p₁' : Meter}
    {lp lc : Ledger} {refp refc : Int}
    (hp : DualBalanced G₁ R₁ G₂ R₂ p₁ p₂ lp refp)
    (hw₁ : w₁ ≤ p₁.gasLeft) (hw₂ : w₂ ≤ p₂.gasLeft)
    (hrem : p₁.gasLeft - w₁ ≤ p₂.gasLeft - w₂)
    (hremRef : p₁.gasLeft - w₁ + p₁.stateSpilled ≤ p₂.gasLeft - w₂ + p₂.stateSpilled)
    (hc : DualBalanced (w₁ + stip) p₁.stateLeft (w₂ + stip) p₂.stateLeft c₁ c₂ lc refc)
    (hComm₂ : c₂.stateCommittedSpill = 0)
    (hm₁ : Meter.incorporateChild { p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } c₁ true = .ok p₁') :
    ∃ p₂', Meter.incorporateChild { p₂ with gasLeft := p₂.gasLeft - w₂, stateLeft := 0 } c₂ true = .ok p₂' ∧
      DualBalanced (G₁ + (w₁ + stip) - w₁) R₁ (G₂ + (w₂ + stip) - w₂) R₂ p₁' p₂' (lp + lc) (refp + refc) := by
  let p₂' : Meter :=
    ({ p₂ with
      gasLeft := ({ p₂ with gasLeft := p₂.gasLeft - w₂, stateLeft := 0 } : Meter).gasLeft + c₂.gasLeft
      stateLeft := ({ p₂ with gasLeft := p₂.gasLeft - w₂, stateLeft := 0 } : Meter).stateLeft + c₂.stateLeft
      stateSpilled := ({ p₂ with gasLeft := p₂.gasLeft - w₂, stateLeft := 0 } : Meter).stateSpilled + c₂.stateSpilled
      refund := ({ p₂ with gasLeft := p₂.gasLeft - w₂, stateLeft := 0 } : Meter).refund + c₂.refund }).repayStateSpill
  have hm₂ : Meter.incorporateChild { p₂ with gasLeft := p₂.gasLeft - w₂, stateLeft := 0 } c₂ true = .ok p₂' := by
    simp [Meter.incorporateChild, p₂', hComm₂]
  have hbal₁ := incorporateChild_balanced hp.bal₁ hw₁ hc.bal₁ hm₁
  have hbal₂ := incorporateChild_balanced hp.bal₂ hw₂ hc.bal₂ hm₂
  refine ⟨p₂', hm₂, ?_⟩
  obtain ⟨hcSpill₁, _, rfl⟩ := incorporateChild_ok hm₁
  obtain ⟨hcg, hcr, hcs, hcf⟩ := hc.le
  obtain ⟨_, _, hps, _⟩ := hp.le
  have hle : MeterLE
      (if true = true then
        ({ p₁ with
          gasLeft := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).gasLeft + c₁.gasLeft
          stateLeft := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).stateLeft + c₁.stateLeft
          stateSpilled := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).stateSpilled + c₁.stateSpilled
          refund := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).refund + c₁.refund }).repayStateSpill
      else
        { p₁ with
          gasLeft := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).gasLeft + c₁.gasLeft
          stateLeft := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).stateLeft + c₁.stateLeft
          stateSpilled := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).stateSpilled + c₁.stateSpilled
          refund := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).refund + c₁.refund })
      p₂' := by
    constructor <;> simp [p₂', Meter.repayStateSpill] <;> omega
  have href₁ : (if true = true then
        ({ p₁ with
          gasLeft := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).gasLeft + c₁.gasLeft
          stateLeft := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).stateLeft + c₁.stateLeft
          stateSpilled := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).stateSpilled + c₁.stateSpilled
          refund := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).refund + c₁.refund }).repayStateSpill
      else
        { p₁ with
          gasLeft := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).gasLeft + c₁.gasLeft
          stateLeft := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).stateLeft + c₁.stateLeft
          stateSpilled := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).stateSpilled + c₁.stateSpilled
          refund := ({ p₁ with gasLeft := p₁.gasLeft - w₁, stateLeft := 0 } : Meter).refund + c₁.refund }).refund =
        refp + refc := by
    simp [Meter.repayStateSpill, hp.ref₁, hc.ref₁]
  have href₂ : p₂'.refund = refp + refc := by
    simp [p₂', Meter.repayStateSpill, hp.ref₂, hc.ref₂]
  exact ⟨hle, hbal₁, hbal₂, href₁, href₂⟩

theorem dualBalanced_stateGasUsed_eq {G₁ R₁ G₂ R₂ : Nat} {m₁ m₂ : Meter} {l : Ledger} {ref : Int}
    (h : DualBalanced G₁ R₁ G₂ R₂ m₁ m₂ l ref) :
    m₁.stateGasUsed R₁ = .ok l.stateUsed ∧ m₂.stateGasUsed R₂ = .ok l.stateUsed :=
  ⟨h.bal₁.stateGasUsed, h.bal₂.stateGasUsed⟩

/-- Sum of execution gas used across the active frame and all suspended parent frames. -/
def stackExecUsed (s : MeterStack.State) : Int :=
  ((s.top :: s.parents).map fun f => f.meter.execUsed f.execution).sum

/-- Sum of signed state gas used across the active frame and all suspended parent frames. -/
def stackStateUsed (s : MeterStack.State) : Int :=
  ((s.top :: s.parents).map MeterStack.Frame.stateUsed).sum

/-- Sum of refund counters across the active frame and all suspended parent frames. -/
def stackRefund (s : MeterStack.State) : Int :=
  ((s.top :: s.parents).map fun f => f.meter.refund).sum

private theorem chain_good {f : MeterStack.Frame} {ps : List MeterStack.Frame}
    (h : MeterStack.Chain f ps) : MeterStack.FrameGood f := by
  cases ps with
  | nil => exact h
  | cons _ _ => exact h.1

private theorem chain_replace {f g : MeterStack.Frame} {ps : List MeterStack.Frame}
    (h : MeterStack.Chain f ps) (hg : MeterStack.FrameGood g)
    (he : g.entryReservoir = f.entryReservoir)
    (hm : ps ≠ [] → g.meter.stateBaseline = f.meter.stateBaseline ∧
      g.meter.stateCommittedSpill = f.meter.stateCommittedSpill) :
    MeterStack.Chain g ps := by
  cases ps with
  | nil => exact hg
  | cons p ps =>
    obtain ⟨hb, hc⟩ := hm (by simp)
    exact ⟨hg, by rw [hb, he]; exact h.2.1, by rw [hc]; exact h.2.2.1,
      h.2.2.2.1, by simpa [he] using h.2.2.2.2.1, h.2.2.2.2.2⟩

private theorem frameGood_charge {f : MeterStack.Frame} {m : Meter} {n : Nat}
    (h : MeterStack.FrameGood f) (hc : f.meter.charge n = .ok m) :
    MeterStack.FrameGood { f with meter := m } := by
  obtain ⟨_, rfl⟩ := charge_ok hc
  exact ⟨h.discipline, h.baseline, by simp; have := h.funding; omega⟩

private theorem frameGood_chargeState {f : MeterStack.Frame} {m : Meter} {n : Nat}
    (h : MeterStack.FrameGood f) (hc : f.meter.chargeState n = .ok m) :
    MeterStack.FrameGood { f with meter := m } := by
  refine ⟨chargeState_discipline h.discipline hc, ?_, ?_⟩
  all_goals rcases chargeState_ok hc with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;>
    simp only <;> have := h.baseline <;> have := h.funding <;> omega

private theorem frameGood_creditStateRefund {f : MeterStack.Frame} (n : Nat)
    (h : MeterStack.FrameGood f) :
    MeterStack.FrameGood { f with meter := f.meter.creditStateRefund n } := by
  refine ⟨creditStateRefund_discipline n h.discipline, h.baseline, ?_⟩
  simp only [Meter.creditStateRefund]; have := h.funding; omega

private theorem frameGood_addRefund {f : MeterStack.Frame} (d : Int)
    (h : MeterStack.FrameGood f) :
    MeterStack.FrameGood { f with meter := f.meter.addRefund d } :=
  ⟨h.discipline, h.baseline, h.funding⟩

private theorem frameGood_commitState {f : MeterStack.Frame} {m : Meter}
    (h : MeterStack.FrameGood f) (hc : f.meter.commitState = .ok m) :
    MeterStack.FrameGood { f with meter := m } := by
  unfold Meter.commitState at hc
  split at hc <;> try contradiction
  simp only [Except.ok.injEq] at hc
  subst hc
  exact ⟨Or.inr rfl, by simp; have := h.baseline; omega, by simp; have := h.funding; omega⟩

private theorem chain_push {s : MeterStack.State} {m : Meter} {w : Nat}
    (h : MeterStack.Chain s.top s.parents) (hc : s.top.meter.charge w = .ok m) (stipend : Nat) :
    MeterStack.Chain (MeterStack.push s m w stipend).top (MeterStack.push s m w stipend).parents := by
  obtain ⟨hw, rfl⟩ := charge_ok hc
  have hg := chain_good h
  have hd := hg.discipline
  have hf := hg.funding
  change MeterStack.FrameGood _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ MeterStack.Chain _ _
  refine ⟨⟨Or.inr rfl, Nat.le_refl _, by simp [MeterStack.push, Meter.fresh]⟩,
    rfl, rfl, rfl, ?_, ?_⟩
  · simpa [MeterStack.push, Meter.drainReservoir] using hd.symm
  · apply chain_replace h
    · exact ⟨Or.inl rfl, hg.baseline, by simp [Meter.drainReservoir]; omega⟩
    · rfl
    · intro _; exact ⟨rfl, rfl⟩

private theorem chain_returnSuccess {s s' : MeterStack.State}
    (h : MeterStack.Chain s.top s.parents)
    (hout : MeterStack.apply .returnSuccess s = .ok s') :
    MeterStack.Chain s'.top s'.parents := by
  have hg := chain_good h
  unfold MeterStack.apply MeterStack.finish at hout
  cases hp : s.parents with
  | nil =>
    simp [hp, pure, Except.pure] at hout
    subst s'
    exact hg
  | cons p ps =>
    have hh := h
    rw [hp] at hh
    simp only [hp, bind, Except.bind] at hout
    split at hout
    · cases hout
    · rename_i m hm
      simp only [pure, Except.pure, Except.ok.injEq] at hout
      subst s'
      obtain ⟨_, _, rfl⟩ := incorporateChild_ok hm
      have hpGood := chain_good hh.2.2.2.2.2
      have hmGood : MeterStack.FrameGood { p with
          meter := ({ p.meter with
            gasLeft := p.meter.gasLeft + s.top.meter.gasLeft
            stateLeft := p.meter.stateLeft + s.top.meter.stateLeft
            stateSpilled := p.meter.stateSpilled + s.top.meter.stateSpilled
            refund := p.meter.refund + s.top.meter.refund }).repayStateSpill
          execution := p.execution + s.top.execution
          reservoir := p.reservoir + s.top.reservoir } := by
        refine ⟨repayStateSpill_zero _, by simp [Meter.repayStateSpill]; exact hpGood.baseline, ?_⟩
        have := hpGood.funding; have := hg.funding
        simp [Meter.repayStateSpill]; omega
      apply chain_replace hh.2.2.2.2.2 hmGood rfl
      intro _
      simp [Meter.repayStateSpill]

/-- Parameter-free global meter-stack simulation invariant. -/
structure MeterStackSim (s₁ s₂ : MeterStack.State) : Prop where
  phase_eq : s₁.phase = s₂.phase
  chain₁ : MeterStack.Chain s₁.top s₁.parents
  chain₂ : MeterStack.Chain s₂.top s₂.parents
  exec_used_eq : stackExecUsed s₁ = stackExecUsed s₂
  state_used_eq : stackStateUsed s₁ = stackStateUsed s₂
  refund_eq : stackRefund s₁ = stackRefund s₂
  stipends_eq : s₁.stipends = s₂.stipends
  parents_len_eq : s₁.parents.length = s₂.parents.length

theorem MeterStackSim.initial (E₁ R₁ E₂ R₂ : Nat) :
    MeterStackSim (MeterStack.initial E₁ R₁) (MeterStack.initial E₂ R₂) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · exact ⟨Or.inr rfl, Nat.le_refl _, by simp [MeterStack.initial, Meter.fresh]⟩
  · exact ⟨Or.inr rfl, Nat.le_refl _, by simp [MeterStack.initial, Meter.fresh]⟩
  · simp [stackExecUsed, MeterStack.initial, Meter.fresh, Meter.execUsed]
  · simp [stackStateUsed, MeterStack.initial, Meter.fresh, MeterStack.Frame.stateUsed, Meter.stateUsed]; omega
  · simp [stackRefund, MeterStack.initial, Meter.fresh]

theorem MeterStackSim.charge {s₁ s₂ : MeterStack.State} {m₁' m₂' : Meter} {n : Nat}
    (h : MeterStackSim s₁ s₂)
    (hc₁ : s₁.top.meter.charge n = .ok m₁')
    (hc₂ : s₂.top.meter.charge n = .ok m₂') :
    MeterStackSim { s₁ with top.meter := m₁' } { s₂ with top.meter := m₂' } := by
  have hg₁ := chain_good h.chain₁
  have hg₂ := chain_good h.chain₂
  obtain ⟨_, rfl⟩ := charge_ok hc₁
  obtain ⟨_, rfl⟩ := charge_ok hc₂
  refine ⟨h.phase_eq,
    chain_replace h.chain₁ (frameGood_charge hg₁ hc₁) rfl (fun _ => ⟨rfl, rfl⟩),
    chain_replace h.chain₂ (frameGood_charge hg₂ hc₂) rfl (fun _ => ⟨rfl, rfl⟩),
    ?_, ?_, ?_, h.stipends_eq, h.parents_len_eq⟩
  · have he := h.exec_used_eq
    have hf₁ := hg₁.funding
    have hf₂ := hg₂.funding
    obtain ⟨_, _⟩ := charge_ok hc₁
    obtain ⟨_, _⟩ := charge_ok hc₂
    simp only [stackExecUsed, List.map_cons, List.sum_cons, Meter.execUsed] at he ⊢
    omega
  · simpa [stackStateUsed, MeterStack.Frame.stateUsed, Meter.stateUsed] using h.state_used_eq
  · simpa [stackRefund] using h.refund_eq

theorem MeterStackSim.chargeState {s₁ s₂ : MeterStack.State} {m₁' m₂' : Meter} {n : Nat}
    (h : MeterStackSim s₁ s₂)
    (hc₁ : s₁.top.meter.chargeState n = .ok m₁')
    (hc₂ : s₂.top.meter.chargeState n = .ok m₂') :
    MeterStackSim { s₁ with top.meter := m₁' } { s₂ with top.meter := m₂' } := by
  have hg₁ := chain_good h.chain₁
  have hg₂ := chain_good h.chain₂
  have hbm₁ : m₁'.stateBaseline = s₁.top.meter.stateBaseline ∧
      m₁'.stateCommittedSpill = s₁.top.meter.stateCommittedSpill ∧
      m₁'.refund = s₁.top.meter.refund ∧
      m₁'.execUsed s₁.top.execution = s₁.top.meter.execUsed s₁.top.execution ∧
      m₁'.stateUsed 0 = s₁.top.meter.stateUsed 0 + (n : Int) := by
    rcases chargeState_ok hc₁ with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;>
      refine ⟨rfl, rfl, rfl, ?_, ?_⟩ <;> simp [Meter.execUsed, Meter.stateUsed] <;> omega
  have hbm₂ : m₂'.stateBaseline = s₂.top.meter.stateBaseline ∧
      m₂'.stateCommittedSpill = s₂.top.meter.stateCommittedSpill ∧
      m₂'.refund = s₂.top.meter.refund ∧
      m₂'.execUsed s₂.top.execution = s₂.top.meter.execUsed s₂.top.execution ∧
      m₂'.stateUsed 0 = s₂.top.meter.stateUsed 0 + (n : Int) := by
    rcases chargeState_ok hc₂ with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;>
      refine ⟨rfl, rfl, rfl, ?_, ?_⟩ <;> simp [Meter.execUsed, Meter.stateUsed] <;> omega
  refine ⟨h.phase_eq,
    chain_replace h.chain₁ (frameGood_chargeState hg₁ hc₁) rfl (fun _ => ⟨hbm₁.1, hbm₁.2.1⟩),
    chain_replace h.chain₂ (frameGood_chargeState hg₂ hc₂) rfl (fun _ => ⟨hbm₂.1, hbm₂.2.1⟩),
    ?_, ?_, ?_, h.stipends_eq, h.parents_len_eq⟩
  · have he := h.exec_used_eq
    simp only [stackExecUsed, List.map_cons, List.sum_cons, hbm₁.2.2.2.1, hbm₂.2.2.2.1] at he ⊢
    exact he
  · have hs := h.state_used_eq
    simp only [stackStateUsed, List.map_cons, List.sum_cons, MeterStack.Frame.stateUsed,
      hbm₁.2.2.2.2, hbm₂.2.2.2.2] at hs ⊢
    omega
  · have hr := h.refund_eq
    simp only [stackRefund, List.map_cons, List.sum_cons, hbm₁.2.2.1, hbm₂.2.2.1] at hr ⊢
    exact hr

theorem MeterStackSim.creditStateRefund {s₁ s₂ : MeterStack.State} (n : Nat)
    (h : MeterStackSim s₁ s₂) :
    MeterStackSim
      { s₁ with top.meter := s₁.top.meter.creditStateRefund n }
      { s₂ with top.meter := s₂.top.meter.creditStateRefund n } := by
  have hg₁ := chain_good h.chain₁
  have hg₂ := chain_good h.chain₂
  refine ⟨h.phase_eq,
    chain_replace h.chain₁ (frameGood_creditStateRefund n hg₁) rfl (fun _ => ⟨rfl, rfl⟩),
    chain_replace h.chain₂ (frameGood_creditStateRefund n hg₂) rfl (fun _ => ⟨rfl, rfl⟩),
    ?_, ?_, ?_, h.stipends_eq, h.parents_len_eq⟩
  · have he := h.exec_used_eq
    simp only [stackExecUsed, List.map_cons, List.sum_cons, Meter.execUsed,
      Meter.creditStateRefund] at he ⊢
    omega
  · have hs := h.state_used_eq
    simp only [stackStateUsed, List.map_cons, List.sum_cons, MeterStack.Frame.stateUsed,
      Meter.stateUsed, Meter.creditStateRefund] at hs ⊢
    omega
  · simpa [stackRefund, Meter.creditStateRefund] using h.refund_eq

theorem MeterStackSim.addRefund {s₁ s₂ : MeterStack.State} (d : Int)
    (h : MeterStackSim s₁ s₂) :
    MeterStackSim
      { s₁ with top.meter := s₁.top.meter.addRefund d }
      { s₂ with top.meter := s₂.top.meter.addRefund d } := by
  have hg₁ := chain_good h.chain₁
  have hg₂ := chain_good h.chain₂
  refine ⟨h.phase_eq,
    chain_replace h.chain₁ (frameGood_addRefund d hg₁) rfl (fun _ => ⟨rfl, rfl⟩),
    chain_replace h.chain₂ (frameGood_addRefund d hg₂) rfl (fun _ => ⟨rfl, rfl⟩),
    ?_, ?_, ?_, h.stipends_eq, h.parents_len_eq⟩
  · simpa [stackExecUsed, Meter.execUsed, Meter.addRefund] using h.exec_used_eq
  · simpa [stackStateUsed, MeterStack.Frame.stateUsed, Meter.stateUsed, Meter.addRefund] using h.state_used_eq
  · have hr := h.refund_eq
    simp only [stackRefund, List.map_cons, List.sum_cons, Meter.addRefund] at hr ⊢
    omega

theorem MeterStackSim.commitState {s₁ s₂ : MeterStack.State} {m₁' m₂' : Meter}
    (h : MeterStackSim s₁ s₂)
    (hp₁ : s₁.parents = [])
    (hc₁ : s₁.top.meter.commitState = .ok m₁')
    (hc₂ : s₂.top.meter.commitState = .ok m₂') :
    MeterStackSim { s₁ with top.meter := m₁' } { s₂ with top.meter := m₂' } := by
  have hg₁ := chain_good h.chain₁
  have hg₂ := chain_good h.chain₂
  have hp₂ : s₂.parents = [] := by
    have hlen := h.parents_len_eq
    rw [hp₁] at hlen
    exact List.eq_nil_of_length_eq_zero hlen.symm
  have hm₁ := hc₁; unfold Meter.commitState at hm₁; split at hm₁ <;> try contradiction
  simp only [Except.ok.injEq] at hm₁; subst hm₁
  have hm₂ := hc₂; unfold Meter.commitState at hm₂; split at hm₂ <;> try contradiction
  simp only [Except.ok.injEq] at hm₂; subst hm₂
  refine ⟨h.phase_eq,
    chain_replace h.chain₁ (frameGood_commitState hg₁ hc₁) rfl (by simp [hp₁]),
    chain_replace h.chain₂ (frameGood_commitState hg₂ hc₂) rfl (by simp [hp₂]),
    ?_, ?_, ?_, h.stipends_eq, h.parents_len_eq⟩
  · have he := h.exec_used_eq
    simp only [stackExecUsed, List.map_cons, List.sum_cons, Meter.execUsed] at he ⊢
    omega
  · have hs := h.state_used_eq
    simp only [stackStateUsed, List.map_cons, List.sum_cons, MeterStack.Frame.stateUsed,
      Meter.stateUsed] at hs ⊢
    omega
  · simpa [stackRefund] using h.refund_eq

theorem MeterStackSim.dispatch {s₁ s₂ : MeterStack.State} (h : MeterStackSim s₁ s₂) :
    MeterStackSim { s₁ with phase := .running } { s₂ with phase := .running } :=
  ⟨rfl, h.chain₁, h.chain₂, h.exec_used_eq, h.state_used_eq, h.refund_eq,
    h.stipends_eq, h.parents_len_eq⟩

private theorem stackExecUsed_push (s : MeterStack.State) (m : Meter) (w stipend : Nat)
    (hc : s.top.meter.charge w = .ok m) (hg : MeterStack.FrameGood s.top) :
    stackExecUsed (MeterStack.push s m w stipend) = stackExecUsed s := by
  obtain ⟨hw, rfl⟩ := charge_ok hc
  have hf := hg.funding
  simp only [stackExecUsed, MeterStack.push, Meter.drainReservoir, Meter.fresh,
    List.map_cons, List.sum_cons, Meter.execUsed]
  omega

private theorem stackStateUsed_push (s : MeterStack.State) (m : Meter) (w stipend : Nat)
    (hc : s.top.meter.charge w = .ok m) :
    stackStateUsed (MeterStack.push s m w stipend) = stackStateUsed s := by
  obtain ⟨_, rfl⟩ := charge_ok hc
  simp only [stackStateUsed, MeterStack.push, Meter.drainReservoir, Meter.fresh,
    List.map_cons, List.sum_cons, MeterStack.Frame.stateUsed, Meter.stateUsed]
  omega

private theorem stackRefund_push (s : MeterStack.State) (m : Meter) (w stipend : Nat)
    (hc : s.top.meter.charge w = .ok m) :
    stackRefund (MeterStack.push s m w stipend) = stackRefund s := by
  obtain ⟨_, rfl⟩ := charge_ok hc
  simp only [stackRefund, MeterStack.push, Meter.drainReservoir, Meter.fresh,
    List.map_cons, List.sum_cons]
  omega

theorem MeterStackSim.spawnCall {s₁ s₂ s₁' s₂' : MeterStack.State} {req₁ req₂ stip : Nat}
    (h : MeterStackSim s₁ s₂)
    (h₁ : MeterStack.apply (.spawnCall req₁ stip) s₁ = .ok s₁')
    (h₂ : MeterStack.apply (.spawnCall req₂ stip) s₂ = .ok s₂') :
    MeterStackSim s₁' s₂' := by
  let w₁ := min req₁ (allButOne64th s₁.top.meter.gasLeft)
  let w₂ := min req₂ (allButOne64th s₂.top.meter.gasLeft)
  have hw₁ : w₁ ≤ s₁.top.meter.gasLeft := Nat.le_trans (Nat.min_le_right _ _) (allButOne64th_le _)
  have hw₂ : w₂ ≤ s₂.top.meter.gasLeft := Nat.le_trans (Nat.min_le_right _ _) (allButOne64th_le _)
  have hc₁ : s₁.top.meter.charge w₁ = .ok { s₁.top.meter with gasLeft := s₁.top.meter.gasLeft - w₁ } := by
    simp [Meter.charge, hw₁]
  have hc₂ : s₂.top.meter.charge w₂ = .ok { s₂.top.meter with gasLeft := s₂.top.meter.gasLeft - w₂ } := by
    simp [Meter.charge, hw₂]
  have hs₁ : s₁' = MeterStack.push s₁ { s₁.top.meter with gasLeft := s₁.top.meter.gasLeft - w₁ } w₁ stip := by
    simpa [MeterStack.apply, w₁, hc₁, bind, Except.bind, pure, Except.pure] using h₁.symm
  have hs₂ : s₂' = MeterStack.push s₂ { s₂.top.meter with gasLeft := s₂.top.meter.gasLeft - w₂ } w₂ stip := by
    simpa [MeterStack.apply, w₂, hc₂, bind, Except.bind, pure, Except.pure] using h₂.symm
  subst hs₁ hs₂
  refine ⟨h.phase_eq, chain_push h.chain₁ hc₁ stip, chain_push h.chain₂ hc₂ stip,
    ?_, ?_, ?_, by simp [MeterStack.push, h.stipends_eq], by simp [MeterStack.push, h.parents_len_eq]⟩
  · rw [stackExecUsed_push _ _ _ _ hc₁ (chain_good h.chain₁),
      stackExecUsed_push _ _ _ _ hc₂ (chain_good h.chain₂), h.exec_used_eq]
  · rw [stackStateUsed_push _ _ _ _ hc₁, stackStateUsed_push _ _ _ _ hc₂, h.state_used_eq]
  · rw [stackRefund_push _ _ _ _ hc₁, stackRefund_push _ _ _ _ hc₂, h.refund_eq]

theorem MeterStackSim.spawnCreate {s₁ s₂ s₁' s₂' : MeterStack.State}
    (h : MeterStackSim s₁ s₂)
    (h₁ : MeterStack.apply .spawnCreate s₁ = .ok s₁')
    (h₂ : MeterStack.apply .spawnCreate s₂ = .ok s₂') :
    MeterStackSim s₁' s₂' := by
  have hw₁ := allButOne64th_le s₁.top.meter.gasLeft
  have hw₂ := allButOne64th_le s₂.top.meter.gasLeft
  have hc₁ : s₁.top.meter.charge (allButOne64th s₁.top.meter.gasLeft) =
      .ok s₁.top.meter.withholdChildGas.1 := by
    simp [Meter.charge, Meter.withholdChildGas, hw₁]
  have hc₂ : s₂.top.meter.charge (allButOne64th s₂.top.meter.gasLeft) =
      .ok s₂.top.meter.withholdChildGas.1 := by
    simp [Meter.charge, Meter.withholdChildGas, hw₂]
  have hs₁ : s₁' = MeterStack.push s₁ s₁.top.meter.withholdChildGas.1 (allButOne64th s₁.top.meter.gasLeft) 0 := by
    simpa [MeterStack.apply, Meter.withholdChildGas, pure, Except.pure] using h₁.symm
  have hs₂ : s₂' = MeterStack.push s₂ s₂.top.meter.withholdChildGas.1 (allButOne64th s₂.top.meter.gasLeft) 0 := by
    simpa [MeterStack.apply, Meter.withholdChildGas, pure, Except.pure] using h₂.symm
  subst hs₁ hs₂
  refine ⟨h.phase_eq, chain_push h.chain₁ hc₁ 0, chain_push h.chain₂ hc₂ 0,
    ?_, ?_, ?_, by simp [MeterStack.push, h.stipends_eq], by simp [MeterStack.push, h.parents_len_eq]⟩
  · rw [stackExecUsed_push _ _ _ _ hc₁ (chain_good h.chain₁),
      stackExecUsed_push _ _ _ _ hc₂ (chain_good h.chain₂), h.exec_used_eq]
  · rw [stackStateUsed_push _ _ _ _ hc₁, stackStateUsed_push _ _ _ _ hc₂, h.state_used_eq]
  · rw [stackRefund_push _ _ _ _ hc₁, stackRefund_push _ _ _ _ hc₂, h.refund_eq]

private theorem stackExecUsed_returnSuccess {s s' : MeterStack.State}
    (h : MeterStack.apply .returnSuccess s = .ok s') :
    stackExecUsed s' = stackExecUsed s := by
  unfold MeterStack.apply MeterStack.finish at h
  cases hp : s.parents with
  | nil =>
    simp [hp, pure, Except.pure] at h
    subst s'
    simp [stackExecUsed, hp]
  | cons p ps =>
    simp only [hp, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i m hm
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst s'
    obtain ⟨hcc, _, rfl⟩ := incorporateChild_ok hm
    simp only [stackExecUsed, hp, List.map_cons, List.sum_cons, Meter.execUsed,
      Meter.repayStateSpill, ↓reduceIte, hcc, Int.natCast_add]
    omega

private theorem stackStateUsed_returnSuccess {s s' : MeterStack.State}
    (h : MeterStack.apply .returnSuccess s = .ok s') :
    stackStateUsed s' = stackStateUsed s := by
  unfold MeterStack.apply MeterStack.finish at h
  cases hp : s.parents with
  | nil =>
    simp [hp, pure, Except.pure] at h
    subst s'
    simp [stackStateUsed, hp]
  | cons p ps =>
    simp only [hp, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i m hm
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst s'
    obtain ⟨hcc, _, rfl⟩ := incorporateChild_ok hm
    simp only [stackStateUsed, hp, List.map_cons, List.sum_cons,
      MeterStack.Frame.stateUsed, Meter.stateUsed, Meter.repayStateSpill,
      ↓reduceIte, hcc, Int.natCast_add]
    omega

private theorem stackRefund_returnSuccess {s s' : MeterStack.State}
    (h : MeterStack.apply .returnSuccess s = .ok s') :
    stackRefund s' = stackRefund s := by
  unfold MeterStack.apply MeterStack.finish at h
  cases hp : s.parents with
  | nil =>
    simp [hp, pure, Except.pure] at h
    subst s'
    simp [stackRefund, hp]
  | cons p ps =>
    simp only [hp, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i m hm
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst s'
    obtain ⟨_, _, rfl⟩ := incorporateChild_ok hm
    simp only [stackRefund, hp, List.map_cons, List.sum_cons, Meter.repayStateSpill, ↓reduceIte]
    omega

theorem MeterStackSim.returnSuccess {s₁ s₂ s₁' : MeterStack.State}
    (h : MeterStackSim s₁ s₂)
    (hLive : LiveStackLE 0 0 (s₁.top.meter :: s₁.parents.map (·.meter))
      (s₂.top.meter :: s₂.parents.map (·.meter)))
    (h₁ : MeterStack.apply .returnSuccess s₁ = .ok s₁') :
    ∃ s₂', MeterStack.apply .returnSuccess s₂ = .ok s₂' ∧
      LiveStackLE 0 0 (s₁'.top.meter :: s₁'.parents.map (·.meter))
        (s₂'.top.meter :: s₂'.parents.map (·.meter)) ∧
      MeterStackSim s₁' s₂' := by
  obtain ⟨s₂', h₂, hLive'⟩ := liveStackLE_returnSuccess hLive h₁
  refine ⟨s₂', h₂, hLive', ?_⟩
  have hphase_len : s₁'.phase = s₂'.phase ∧ s₁'.stipends = s₂'.stipends ∧
      s₁'.parents.length = s₂'.parents.length := by
    have h₁' := h₁; have h₂' := h₂
    unfold MeterStack.apply MeterStack.finish at h₁' h₂'
    cases hp₁ : s₁.parents with
    | nil =>
      have hp₂ : s₂.parents = [] := by
        have hlen := h.parents_len_eq; rw [hp₁] at hlen
        exact List.eq_nil_of_length_eq_zero hlen.symm
      simp [hp₁, pure, Except.pure] at h₁'
      simp [hp₂, pure, Except.pure] at h₂'
      subst h₁' h₂'
      exact ⟨rfl, h.stipends_eq, by simp [hp₁, hp₂]⟩
    | cons p₁ ps₁ =>
      cases hp₂ : s₂.parents with
      | nil =>
        have hlen := h.parents_len_eq; rw [hp₁, hp₂] at hlen; simp at hlen
      | cons p₂ ps₂ =>
        simp only [hp₁, bind, Except.bind] at h₁'
        simp only [hp₂, bind, Except.bind] at h₂'
        split at h₁' <;> try contradiction
        split at h₂' <;> try contradiction
        simp only [pure, Except.pure, Except.ok.injEq] at h₁' h₂'
        subst h₁' h₂'
        have hlen := h.parents_len_eq; rw [hp₁, hp₂] at hlen; simp at hlen
        exact ⟨h.phase_eq, h.stipends_eq, hlen⟩
  refine ⟨hphase_len.1, chain_returnSuccess h.chain₁ h₁, chain_returnSuccess h.chain₂ h₂,
    ?_, ?_, ?_, hphase_len.2.1, hphase_len.2.2⟩
  · rw [stackExecUsed_returnSuccess h₁, stackExecUsed_returnSuccess h₂, h.exec_used_eq]
  · rw [stackStateUsed_returnSuccess h₁, stackStateUsed_returnSuccess h₂, h.state_used_eq]
  · rw [stackRefund_returnSuccess h₁, stackRefund_returnSuccess h₂, h.refund_eq]

end EvmGasSemantics.Spec
