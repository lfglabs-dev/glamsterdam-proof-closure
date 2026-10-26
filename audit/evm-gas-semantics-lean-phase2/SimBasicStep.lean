import EvmGasSemantics.Theorems.Spec.Monotone
import EvmGasSemantics.Theorems.Spec.SimWorld
import EvmGasSemantics.Theorems.Spec.SimMeter

set_option autoImplicit false
namespace EvmGasSemantics.Spec

open EvmGasSemantics

@[simp] theorem stateT_run_eq {σ ε α : Type} (x : StateT σ (Except ε) α) (s : σ) :
    x.run s = x s := rfl

@[simp] theorem stateT_bind_eq {σ ε α β : Type}
    (x : StateT σ (Except ε) α) (f : α → StateT σ (Except ε) β) (s : σ) :
    (x >>= f) s = match x s with | .error e => .error e | .ok (a, s') => f a s' := by
  change StateT.bind x f s = _
  unfold StateT.bind
  cases x s <;> rfl

@[simp] theorem stateT_bind_raw {σ ε α β : Type}
    (x : StateT σ (Except ε) α) (f : α → StateT σ (Except ε) β) (s : σ) :
    (StateT.bind x f) s = match x s with | .error e => .error e | .ok (a, s') => f a s' := by
  unfold StateT.bind
  cases x s <;> rfl

@[simp] theorem stateT_pure_eq {σ ε α : Type} (a : α) (s : σ) :
    (pure a : StateT σ (Except ε) α) s = .ok (a, s) := rfl

@[simp] theorem stateT_pure_raw {σ ε α : Type} (a : α) (s : σ) :
    (StateT.pure a : StateT σ (Except ε) α) s = .ok (a, s) := rfl

@[simp] theorem stateT_get_eq {σ ε : Type} (s : σ) :
    (get : StateT σ (Except ε) σ) s = .ok (s, s) := rfl

@[simp] theorem stateT_set_eq {σ ε : Type} (s' s : σ) :
    (set s' : StateT σ (Except ε) PUnit) s = .ok ((), s') := rfl

@[simp] theorem stateT_modify_eq {σ ε : Type} (f : σ → σ) (s : σ) :
    (modify f : StateT σ (Except ε) PUnit) s = .ok ((), f s) := rfl

@[simp] theorem stateT_throw_eq {σ ε α : Type} (e : ε) (s : σ) :
    (throw e : StateT σ (Except ε) α) s = .error e := rfl

@[simp] theorem ofExcept_eq {σ ε α : Type} (v : Except ε α) (s : σ) :
    (ofExcept v : StateT σ (Except ε) α) s = v.map (fun a => (a, s)) := by
  cases v <;> rfl

/-- Two machines on the same fork/context/world with `MeterLE` on the top meter. -/
structure TopMeterSim (s₁ s₂ : Exec.Machine) : Prop where
  fork_eq : s₁.fork = s₂.fork
  ctx_eq : s₁.ctx = s₂.ctx
  world_eq : s₁.world = s₂.world
  top_le : MeterLE s₁.meters.top.meter s₂.meters.top.meter
  parents_eq : s₁.meters.parents = s₂.meters.parents
  phase_eq : s₁.meters.phase = s₂.meters.phase

/-! The full machine relation used by the transaction simulation proof. -/
structure ExecSim (sender : Nat) (s₁ s₂ : Exec.Machine) : Prop where
  fork_eq : s₁.fork = s₂.fork
  ctx_eq : s₁.ctx = s₂.ctx
  world_sim : WorldSim sender s₁.world s₂.world
  live_stack_le :
    LiveStackLE 0 0
      (s₁.meters.top.meter :: s₁.meters.parents.map (·.meter))
      (s₂.meters.top.meter :: s₂.meters.parents.map (·.meter))
  phase_eq : MeterStackSim s₁.meters s₂.meters
  sites_eq : s₁.sites = s₂.sites
  branches_eq : s₁.branches = s₂.branches
  frames_size_eq : s₁.frames.size = s₂.frames.size

theorem meterLE_addRefund {a b : Meter} (h : MeterLE a b) (d : Int) :
    MeterLE (a.addRefund d) (b.addRefund d) := by
  obtain ⟨hg, hr, hs, hf⟩ := h
  exact ⟨hg, hr, hs, hf⟩

theorem meterOp_preserves_halt {op : MeterStack.Op} {s s' : Exec.Machine}
    (h : (Exec.meterOp op).run s = .ok ((), s'))
    (hHalt : s.ctx.outcome = some .halt) :
    s'.ctx.outcome = some .halt := by
  simp only [Exec.meterOp, Exec.running, stateT_run_eq, stateT_bind_eq,
    stateT_get_eq, stateT_pure_eq, hHalt, Option.isNone, Bool.false_eq_true, ↓reduceIte] at h
  cases h
  exact hHalt

theorem cost_preserves_halt {c : Cost} {s s' : Exec.Machine}
    (h : (Exec.cost c).run s = .ok ((), s'))
    (hHalt : s.ctx.outcome = some .halt) :
    s'.ctx.outcome = some .halt := by
  simp only [Exec.cost, Exec.running, stateT_run_eq, stateT_bind_eq,
    stateT_get_eq, stateT_pure_eq, hHalt, Option.isNone, Bool.false_eq_true, ↓reduceIte] at h
  cases h
  exact hHalt

theorem meterOp_charge_topMeterSim {s₁ s₂ s₁' : Exec.Machine} {n : Nat}
    (hSim : TopMeterSim s₁ s₂)
    (h₁ : (Exec.meterOp (.charge n)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.meterOp (.charge n)).run s₂ = .ok ((), s₂') ∧ TopMeterSim s₁' s₂' := by
  simp only [Exec.meterOp, Exec.running, stateT_run_eq, stateT_bind_eq,
    stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte, stateT_bind_raw, stateT_get_eq, MeterStack.apply,
      bind, Except.bind, pure, Except.pure] at h₁ ⊢
    cases hc₁ : s₁.meters.top.meter.charge n with
    | error e =>
      rw [hc₁] at h₁
      cases e with
      | outOfGas =>
        simp only [Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
        rcases h₁ with ⟨_, rfl⟩
        exact absurd rfl hNoHalt
      | assertion a =>
        simp only [stateT_throw_eq] at h₁
        cases h₁
    | ok m₁' =>
      rw [hc₁] at h₁
      simp only [stateT_set_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
      rcases h₁ with ⟨_, rfl⟩
      obtain ⟨m₂', hc₂, hle⟩ := meterLE_charge hSim.top_le hc₁
      rw [hc₂]
      refine ⟨_, rfl, ?_⟩
      exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_eq, hle, hSim.parents_eq, hSim.phase_eq⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem meterOp_chargeState_topMeterSim {s₁ s₂ s₁' : Exec.Machine} {n : Nat}
    (hSim : TopMeterSim s₁ s₂)
    (h₁ : (Exec.meterOp (.chargeState n)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.meterOp (.chargeState n)).run s₂ = .ok ((), s₂') ∧ TopMeterSim s₁' s₂' := by
  simp only [Exec.meterOp, Exec.running, stateT_run_eq, stateT_bind_eq,
    stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte, stateT_bind_raw, stateT_get_eq, MeterStack.apply,
      bind, Except.bind, pure, Except.pure] at h₁ ⊢
    cases hc₁ : s₁.meters.top.meter.chargeState n with
    | error e =>
      rw [hc₁] at h₁
      cases e with
      | outOfGas =>
        simp only [Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
        rcases h₁ with ⟨_, rfl⟩
        exact absurd rfl hNoHalt
      | assertion a =>
        simp only [stateT_throw_eq] at h₁
        cases h₁
    | ok m₁' =>
      rw [hc₁] at h₁
      simp only [stateT_set_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
      rcases h₁ with ⟨_, rfl⟩
      obtain ⟨m₂', hc₂, hle⟩ := meterLE_chargeState hSim.top_le hc₁
      rw [hc₂]
      refine ⟨_, rfl, ?_⟩
      exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_eq, hle, hSim.parents_eq, hSim.phase_eq⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem meterOp_creditStateRefund_topMeterSim {s₁ s₂ s₁' : Exec.Machine} {n : Nat}
    (hSim : TopMeterSim s₁ s₂)
    (h₁ : (Exec.meterOp (.creditStateRefund n)).run s₁ = .ok ((), s₁')) :
    ∃ s₂', (Exec.meterOp (.creditStateRefund n)).run s₂ = .ok ((), s₂') ∧ TopMeterSim s₁' s₂' := by
  simp only [Exec.meterOp, Exec.running, stateT_run_eq, stateT_bind_eq,
    stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte, MeterStack.apply, pure, Except.pure] at h₁ ⊢
    cases h₁
    refine ⟨_, rfl, ?_⟩
    exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_eq,
      meterLE_creditStateRefund hSim.top_le n, hSim.parents_eq, hSim.phase_eq⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem meterOp_addRefund_topMeterSim {s₁ s₂ s₁' : Exec.Machine} {d : Int}
    (hSim : TopMeterSim s₁ s₂)
    (h₁ : (Exec.meterOp (.addRefund d)).run s₁ = .ok ((), s₁')) :
    ∃ s₂', (Exec.meterOp (.addRefund d)).run s₂ = .ok ((), s₂') ∧ TopMeterSim s₁' s₂' := by
  simp only [Exec.meterOp, Exec.running, stateT_run_eq, stateT_bind_eq,
    stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte, MeterStack.apply, pure, Except.pure] at h₁ ⊢
    cases h₁
    refine ⟨_, rfl, ?_⟩
    exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_eq,
      meterLE_addRefund hSim.top_le d, hSim.parents_eq, hSim.phase_eq⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

private theorem if_addRefund_preserves_halt {cond : Bool} {d : Int} {s s' : Exec.Machine}
    (h : (if cond then Exec.meterOp (.addRefund d) else pure ()).run s = .ok ((), s'))
    (hHalt : s.ctx.outcome = some .halt) :
    s'.ctx.outcome = some .halt := by
  cases cond
  · simp only [Bool.false_eq_true, ↓reduceIte, stateT_run_eq, stateT_pure_eq] at h
    cases h; exact hHalt
  · simp only [↓reduceIte] at h
    exact meterOp_preserves_halt h hHalt

private theorem if_addRefund_topMeterSim {cond : Bool} {s₁ s₂ s₁' : Exec.Machine} {d : Int}
    (hSim : TopMeterSim s₁ s₂)
    (h₁ : (if cond then Exec.meterOp (.addRefund d) else pure ()).run s₁ = .ok ((), s₁')) :
    ∃ s₂', (if cond then Exec.meterOp (.addRefund d) else pure ()).run s₂ = .ok ((), s₂') ∧
      TopMeterSim s₁' s₂' := by
  cases cond
  · simp only [Bool.false_eq_true, ↓reduceIte, stateT_run_eq, stateT_pure_eq] at h₁ ⊢
    cases h₁; exact ⟨s₂, rfl, hSim⟩
  · simp only [↓reduceIte] at h₁ ⊢
    exact meterOp_addRefund_topMeterSim hSim h₁

private theorem seq_preserves_halt {m₁ m₂ : Exec.M Unit} {s s' : Exec.Machine}
    (hm₁ : ∀ {a b : Exec.Machine}, m₁.run a = .ok ((), b) → a.ctx.outcome = some .halt → b.ctx.outcome = some .halt)
    (hm₂ : ∀ {a b : Exec.Machine}, m₂.run a = .ok ((), b) → a.ctx.outcome = some .halt → b.ctx.outcome = some .halt)
    (h : (do m₁; m₂).run s = .ok ((), s'))
    (hHalt : s.ctx.outcome = some .halt) :
    s'.ctx.outcome = some .halt := by
  simp only [stateT_run_eq, stateT_bind_eq] at h
  cases hr₁ : m₁ s with
  | error e => rw [hr₁] at h; cases h
  | ok p =>
    rcases p with ⟨⟨⟩, s_mid⟩
    rw [hr₁] at h
    exact hm₂ h (hm₁ hr₁ hHalt)

theorem seq_topMeterSim {m₁ m₂ : Exec.M Unit} {s₁ s₂ s₁' : Exec.Machine}
    (_hSim : TopMeterSim s₁ s₂)
    (h₁ : (do m₁; m₂).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt)
    (hPres : ∀ {a b : Exec.Machine}, m₂.run a = .ok ((), b) → a.ctx.outcome = some .halt → b.ctx.outcome = some .halt)
    (hm₁ : ∀ {s₁_mid : Exec.Machine}, m₁.run s₁ = .ok ((), s₁_mid) → s₁_mid.ctx.outcome ≠ some .halt →
      ∃ s₂_mid, m₁.run s₂ = .ok ((), s₂_mid) ∧ TopMeterSim s₁_mid s₂_mid)
    (hm₂ : ∀ {s₁_mid s₂_mid : Exec.Machine}, TopMeterSim s₁_mid s₂_mid →
      m₂.run s₁_mid = .ok ((), s₁') → s₁'.ctx.outcome ≠ some .halt →
      ∃ s₂', m₂.run s₂_mid = .ok ((), s₂') ∧ TopMeterSim s₁' s₂') :
    ∃ s₂', (do m₁; m₂).run s₂ = .ok ((), s₂') ∧ TopMeterSim s₁' s₂' := by
  simp only [stateT_run_eq, stateT_bind_eq] at h₁ ⊢
  cases hr₁ : m₁ s₁ with
  | error e => rw [hr₁] at h₁; cases h₁
  | ok p =>
    rcases p with ⟨⟨⟩, s₁_mid⟩
    rw [hr₁] at h₁
    have hMidNoHalt : s₁_mid.ctx.outcome ≠ some .halt := fun hH => hNoHalt (hPres h₁ hH)
    obtain ⟨s₂_mid, hr₂, hSimMid⟩ := hm₁ hr₁ hMidNoHalt
    obtain ⟨s₂', hr₂', hSim'⟩ := hm₂ hSimMid h₁ hNoHalt
    rw [show m₁ s₂ = .ok ((), s₂_mid) from hr₂]
    exact ⟨s₂', hr₂', hSim'⟩

theorem cost_topMeterSim {s₁ s₂ s₁' : Exec.Machine} {c : Cost}
    (hSim : TopMeterSim s₁ s₂)
    (h₁ : (Exec.cost c).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.cost c).run s₂ = .ok ((), s₂') ∧ TopMeterSim s₁' s₂' := by
  unfold Exec.cost at h₁ ⊢
  simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte] at h₁ ⊢
    change (do
      if c.check != 0 && (← (get : Exec.M Exec.Machine)).meters.top.meter.gasLeft ≤ c.check then Exec.halt
      Exec.meterOp (.charge c.exec)
      Exec.meterOp (.chargeState c.state)
      if c.stateRefill != 0 then Exec.meterOp (.creditStateRefund c.stateRefill)
      if c.refund != 0 then Exec.meterOp (.addRefund c.refund)).run s₁ = .ok ((), s₁') at h₁
    change ∃ s₂', (do
      if c.check != 0 && (← (get : Exec.M Exec.Machine)).meters.top.meter.gasLeft ≤ c.check then Exec.halt
      Exec.meterOp (.charge c.exec)
      Exec.meterOp (.chargeState c.state)
      if c.stateRefill != 0 then Exec.meterOp (.creditStateRefund c.stateRefill)
      if c.refund != 0 then Exec.meterOp (.addRefund c.refund)).run s₂ = .ok ((), s₂') ∧ TopMeterSim s₁' s₂'
    have hp4 : ∀ {a b : Exec.Machine},
        (do
          if c.stateRefill != 0 then Exec.meterOp (.creditStateRefund c.stateRefill)
          if c.refund != 0 then Exec.meterOp (.addRefund c.refund)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt := by
      intro a b h4 hH
      dsimp at h4
      cases hc1 : c.stateRefill != 0 <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte] at h4
      · exact if_addRefund_preserves_halt h4 hH
      · exact seq_preserves_halt meterOp_preserves_halt if_addRefund_preserves_halt h4 hH
    have hp3 : ∀ {a b : Exec.Machine},
        (do
          Exec.meterOp (.chargeState c.state)
          if c.stateRefill != 0 then Exec.meterOp (.creditStateRefund c.stateRefill)
          if c.refund != 0 then Exec.meterOp (.addRefund c.refund)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt :=
      seq_preserves_halt meterOp_preserves_halt hp4
    have hp2 : ∀ {a b : Exec.Machine},
        (do
          Exec.meterOp (.charge c.exec)
          Exec.meterOp (.chargeState c.state)
          if c.stateRefill != 0 then Exec.meterOp (.creditStateRefund c.stateRefill)
          if c.refund != 0 then Exec.meterOp (.addRefund c.refund)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt :=
      seq_preserves_halt meterOp_preserves_halt hp3
    dsimp only at h₁ ⊢
    simp only [stateT_run_eq, stateT_bind_eq, stateT_get_eq] at h₁ ⊢
    by_cases hChk₁ : (c.check != 0 && decide (s₁.meters.top.meter.gasLeft ≤ c.check)) = true
    · simp only [hChk₁, ↓reduceIte, Exec.halt] at h₁
      rw [stateT_bind_eq, stateT_modify_eq] at h₁
      exact absurd (hp2 h₁ rfl) hNoHalt
    · have hGasLE := hSim.top_le.gas
      have hChk₂ : (c.check != 0 && decide (s₂.meters.top.meter.gasLeft ≤ c.check)) = false := by
        cases hc0 : c.check != 0 <;> simp_all
        omega
      simp only [hChk₁, hChk₂, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
      refine seq_topMeterSim hSim h₁ hNoHalt hp3 (fun hr hnh => meterOp_charge_topMeterSim hSim hr hnh) ?_
      intro s₁_2 s₂_2 hSim2 hRest2 hNoHalt2
      refine seq_topMeterSim hSim2 hRest2 hNoHalt2 hp4 (fun hr hnh => meterOp_chargeState_topMeterSim hSim2 hr hnh) ?_
      intro s₁_3 s₂_3 hSim3 hRest3 hNoHalt3
      cases hc1 : c.stateRefill != 0 <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hRest3 ⊢
      · exact if_addRefund_topMeterSim hSim3 hRest3
      · exact seq_topMeterSim hSim3 hRest3 hNoHalt3 if_addRefund_preserves_halt
          (fun hr _ => meterOp_creditStateRefund_topMeterSim hSim3 hr)
          (fun hSim4 hr _ => if_addRefund_topMeterSim hSim4 hr)
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem costs_preserves_halt {cs : Cost.Seq} {s s' : Exec.Machine}
    (h : (Exec.costs cs).run s = .ok ((), s'))
    (hHalt : s.ctx.outcome = some .halt) :
    s'.ctx.outcome = some .halt := by
  induction cs generalizing s s' with
  | nil =>
    change (pure () : Exec.M Unit).run s = .ok ((), s') at h
    simp only [stateT_run_eq, stateT_pure_eq] at h
    cases h
    exact hHalt
  | cons c cs ih =>
    change (do Exec.cost c; Exec.costs cs).run s = .ok ((), s') at h
    exact seq_preserves_halt cost_preserves_halt ih h hHalt

theorem costs_topMeterSim {s₁ s₂ s₁' : Exec.Machine} {cs : Cost.Seq}
    (hSim : TopMeterSim s₁ s₂)
    (h₁ : (Exec.costs cs).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.costs cs).run s₂ = .ok ((), s₂') ∧ TopMeterSim s₁' s₂' := by
  induction cs generalizing s₁ s₂ with
  | nil =>
    change (pure () : Exec.M Unit).run s₁ = .ok ((), s₁') at h₁
    simp only [stateT_run_eq, stateT_pure_eq] at h₁
    cases h₁
    exact ⟨s₂, rfl, hSim⟩
  | cons c cs ih =>
    change (do Exec.cost c; Exec.costs cs).run s₁ = .ok ((), s₁') at h₁
    exact seq_topMeterSim hSim h₁ hNoHalt
      (fun hr hH => costs_preserves_halt hr hH)
      (fun hr hnh => cost_topMeterSim hSim hr hnh)
      (fun hSimMid hr hnh => ih hSimMid hr)

theorem memory_topMeterSim {s₁ s₂ s₁' : Exec.Machine} {n : Nat}
    (hSim : TopMeterSim s₁ s₂)
    (h₁ : (Exec.memory n).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.memory n).run s₂ = .ok ((), s₂') ∧ TopMeterSim s₁' s₂' := by
  have h₁' : (do
      Exec.cost { exec := Rules.memoryExpansion s₁.fork s₁.ctx.memory n }
      if ← Exec.running then modify fun (s : Exec.Machine) =>
        { s with ctx.memory := max s.ctx.memory (32 * Rules.wordsForBytes n) }).run s₁ = .ok ((), s₁') := by
    simpa [Exec.memory] using h₁
  suffices ∃ s₂', (do
      Exec.cost { exec := Rules.memoryExpansion s₂.fork s₂.ctx.memory n }
      if ← Exec.running then modify fun (s : Exec.Machine) =>
        { s with ctx.memory := max s.ctx.memory (32 * Rules.wordsForBytes n) }).run s₂ = .ok ((), s₂') ∧ TopMeterSim s₁' s₂' by
    simpa [Exec.memory] using this
  rw [← hSim.fork_eq, ← hSim.ctx_eq]
  refine seq_topMeterSim hSim h₁' hNoHalt ?_
    (fun hr hnh => cost_topMeterSim hSim hr hnh) ?_
  · intro a b hMod hH
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
      hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hMod
    cases hMod
    exact hH
  · intro s₁_mid s₂_mid hSimMid hMod _
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hMod ⊢
    rw [← hSimMid.ctx_eq]
    by_cases hRun : s₁_mid.ctx.outcome.isNone = true
    · simp only [hRun, ↓reduceIte, stateT_modify_eq] at hMod ⊢
      cases hMod
      refine ⟨_, rfl, ?_⟩
      exact ⟨hSimMid.fork_eq, by simp [hSimMid.ctx_eq], hSimMid.world_eq,
        hSimMid.top_le, hSimMid.parents_eq, hSimMid.phase_eq⟩
    · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hMod ⊢
      cases hMod
      exact ⟨s₂_mid, rfl, hSimMid⟩

theorem terminate_topMeterSim {s₁ s₂ s₁' : Exec.Machine} {e : Terminator}
    (hSim : TopMeterSim s₁ s₂)
    (h₁ : (Exec.terminate e).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.terminate e).run s₂ = .ok ((), s₂') ∧ TopMeterSim s₁' s₂' := by
  unfold Exec.terminate at h₁ ⊢
  simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte] at h₁ ⊢
    cases e with
    | invalid =>
      simp only [Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
      rcases h₁ with ⟨_, rfl⟩
      exact absurd rfl hNoHalt
    | stop =>
      simp only [stateT_modify_eq] at h₁ ⊢
      cases h₁
      refine ⟨_, rfl, ?_⟩
      exact ⟨hSim.fork_eq, by simp [hSim.ctx_eq], hSim.world_eq,
        hSim.top_le, hSim.parents_eq, hSim.phase_eq⟩
    | «return» n =>
      refine seq_topMeterSim hSim h₁ hNoHalt ?_ (fun hr hnh => memory_topMeterSim hSim hr hnh) ?_
      · intro a b hMod hH
        simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
          hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hMod
        cases hMod; exact hH
      · intro s₁_mid s₂_mid hSimMid hMod _
        simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hMod ⊢
        rw [← hSimMid.ctx_eq]
        by_cases hRun2 : s₁_mid.ctx.outcome.isNone = true
        · simp only [hRun2, ↓reduceIte, stateT_modify_eq] at hMod ⊢
          cases hMod
          refine ⟨_, rfl, ?_⟩
          exact ⟨hSimMid.fork_eq, by simp [hSimMid.ctx_eq], hSimMid.world_eq,
            hSimMid.top_le, hSimMid.parents_eq, hSimMid.phase_eq⟩
        · simp only [hRun2, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hMod ⊢
          cases hMod
          exact ⟨s₂_mid, rfl, hSimMid⟩
    | revert n =>
      refine seq_topMeterSim hSim h₁ hNoHalt ?_ (fun hr hnh => memory_topMeterSim hSim hr hnh) ?_
      · intro a b hMod hH
        simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
          hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hMod
        cases hMod; exact hH
      · intro s₁_mid s₂_mid hSimMid hMod _
        simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hMod ⊢
        rw [← hSimMid.ctx_eq]
        by_cases hRun2 : s₁_mid.ctx.outcome.isNone = true
        · simp only [hRun2, ↓reduceIte, stateT_modify_eq] at hMod ⊢
          cases hMod
          refine ⟨_, rfl, ?_⟩
          exact ⟨hSimMid.fork_eq, by simp [hSimMid.ctx_eq], hSimMid.world_eq,
            hSimMid.top_le, hSimMid.parents_eq, hSimMid.phase_eq⟩
        · simp only [hRun2, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hMod ⊢
          cases hMod
          exact ⟨s₂_mid, rfl, hSimMid⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem liveStackLE_head_meterLE {a b : Meter} {as bs : List Meter}
    (h : LiveStackLE 0 0 (a :: as) (b :: bs)) : MeterLE a b := by
  cases h with
  | cons hb hg hr hs hc ht =>
    have hf : 0 + (a.gasLeft : Int) + a.stateSpilled ≤ 0 + (b.gasLeft : Int) + b.stateSpilled := by
      cases ht <;> assumption
    exact ⟨hg, hr, hs, by omega⟩

theorem liveStackLE_addRefund {a b : Meter} {as bs : List Meter} (d : Int)
    (h : LiveStackLE 0 0 (a :: as) (b :: bs)) :
    LiveStackLE 0 0 (a.addRefund d :: as) (b.addRefund d :: bs) := by
  cases h with
  | cons hxy hg hr hs hc ht =>
    exact .cons hxy hg hr hs hc ht

theorem meterOp_charge_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {n : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.meterOp (.charge n)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.meterOp (.charge n)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  simp only [Exec.meterOp, Exec.running, stateT_run_eq, stateT_bind_eq,
    stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte, stateT_bind_raw, stateT_get_eq, MeterStack.apply,
      bind, Except.bind, pure, Except.pure] at h₁ ⊢
    cases hc₁ : s₁.meters.top.meter.charge n with
    | error e =>
      rw [hc₁] at h₁
      cases e with
      | outOfGas =>
        simp only [Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
        rcases h₁ with ⟨_, rfl⟩
        exact absurd rfl hNoHalt
      | assertion a =>
        simp only [stateT_throw_eq] at h₁
        cases h₁
    | ok m₁' =>
      rw [hc₁] at h₁
      simp only [stateT_set_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
      rcases h₁ with ⟨_, rfl⟩
      obtain ⟨m₂', hc₂, hstack⟩ := liveStackLE_charge hSim.live_stack_le hc₁
      rw [hc₂]
      refine ⟨_, rfl, ?_⟩
      exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_sim, hstack,
        hSim.phase_eq.charge hc₁ hc₂, hSim.sites_eq, hSim.branches_eq, hSim.frames_size_eq⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem meterOp_chargeState_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {n : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.meterOp (.chargeState n)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.meterOp (.chargeState n)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  simp only [Exec.meterOp, Exec.running, stateT_run_eq, stateT_bind_eq,
    stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte, stateT_bind_raw, stateT_get_eq, MeterStack.apply,
      bind, Except.bind, pure, Except.pure] at h₁ ⊢
    cases hc₁ : s₁.meters.top.meter.chargeState n with
    | error e =>
      rw [hc₁] at h₁
      cases e with
      | outOfGas =>
        simp only [Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
        rcases h₁ with ⟨_, rfl⟩
        exact absurd rfl hNoHalt
      | assertion a =>
        simp only [stateT_throw_eq] at h₁
        cases h₁
    | ok m₁' =>
      rw [hc₁] at h₁
      simp only [stateT_set_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
      rcases h₁ with ⟨_, rfl⟩
      obtain ⟨m₂', hc₂, hstack⟩ := liveStackLE_chargeState hSim.live_stack_le hc₁
      rw [hc₂]
      refine ⟨_, rfl, ?_⟩
      exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_sim, hstack,
        hSim.phase_eq.chargeState hc₁ hc₂, hSim.sites_eq, hSim.branches_eq, hSim.frames_size_eq⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem meterOp_creditStateRefund_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {n : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.meterOp (.creditStateRefund n)).run s₁ = .ok ((), s₁')) :
    ∃ s₂', (Exec.meterOp (.creditStateRefund n)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  simp only [Exec.meterOp, Exec.running, stateT_run_eq, stateT_bind_eq,
    stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte, MeterStack.apply, pure, Except.pure] at h₁ ⊢
    cases h₁
    refine ⟨_, rfl, ?_⟩
    exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_sim,
      liveStackLE_creditStateRefund n hSim.live_stack_le,
      hSim.phase_eq.creditStateRefund n, hSim.sites_eq, hSim.branches_eq, hSim.frames_size_eq⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem meterOp_addRefund_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {d : Int}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.meterOp (.addRefund d)).run s₁ = .ok ((), s₁')) :
    ∃ s₂', (Exec.meterOp (.addRefund d)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  simp only [Exec.meterOp, Exec.running, stateT_run_eq, stateT_bind_eq,
    stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte, MeterStack.apply, pure, Except.pure] at h₁ ⊢
    cases h₁
    refine ⟨_, rfl, ?_⟩
    exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_sim,
      liveStackLE_addRefund d hSim.live_stack_le,
      hSim.phase_eq.addRefund d, hSim.sites_eq, hSim.branches_eq, hSim.frames_size_eq⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

private theorem if_addRefund_execSim {sender : Nat} {cond : Bool} {s₁ s₂ s₁' : Exec.Machine} {d : Int}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (if cond then Exec.meterOp (.addRefund d) else pure ()).run s₁ = .ok ((), s₁')) :
    ∃ s₂', (if cond then Exec.meterOp (.addRefund d) else pure ()).run s₂ = .ok ((), s₂') ∧
      ExecSim sender s₁' s₂' := by
  cases cond
  · simp only [Bool.false_eq_true, ↓reduceIte, stateT_run_eq, stateT_pure_eq] at h₁ ⊢
    cases h₁; exact ⟨s₂, rfl, hSim⟩
  · simp only [↓reduceIte] at h₁ ⊢
    exact meterOp_addRefund_execSim hSim h₁

theorem seq_execSim {sender : Nat} {m₁ m₂ : Exec.M Unit} {s₁ s₂ s₁' : Exec.Machine}
    (_hSim : ExecSim sender s₁ s₂)
    (h₁ : (do m₁; m₂).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt)
    (hPres : ∀ {a b : Exec.Machine}, m₂.run a = .ok ((), b) → a.ctx.outcome = some .halt → b.ctx.outcome = some .halt)
    (hm₁ : ∀ {s₁_mid : Exec.Machine}, m₁.run s₁ = .ok ((), s₁_mid) → s₁_mid.ctx.outcome ≠ some .halt →
      ∃ s₂_mid, m₁.run s₂ = .ok ((), s₂_mid) ∧ ExecSim sender s₁_mid s₂_mid)
    (hm₂ : ∀ {s₁_mid s₂_mid : Exec.Machine}, ExecSim sender s₁_mid s₂_mid →
      m₂.run s₁_mid = .ok ((), s₁') → s₁'.ctx.outcome ≠ some .halt →
      ∃ s₂', m₂.run s₂_mid = .ok ((), s₂') ∧ ExecSim sender s₁' s₂') :
    ∃ s₂', (do m₁; m₂).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  simp only [stateT_run_eq, stateT_bind_eq] at h₁ ⊢
  cases hr₁ : m₁ s₁ with
  | error e => rw [hr₁] at h₁; cases h₁
  | ok p =>
    rcases p with ⟨⟨⟩, s₁_mid⟩
    rw [hr₁] at h₁
    have hMidNoHalt : s₁_mid.ctx.outcome ≠ some .halt := fun hH => hNoHalt (hPres h₁ hH)
    obtain ⟨s₂_mid, hr₂, hSimMid⟩ := hm₁ hr₁ hMidNoHalt
    obtain ⟨s₂', hr₂', hSim'⟩ := hm₂ hSimMid h₁ hNoHalt
    rw [show m₁ s₂ = .ok ((), s₂_mid) from hr₂]
    exact ⟨s₂', hr₂', hSim'⟩

theorem cost_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {c : Cost}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.cost c).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.cost c).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.cost at h₁ ⊢
  simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte] at h₁ ⊢
    change (do
      if c.check != 0 && (← (get : Exec.M Exec.Machine)).meters.top.meter.gasLeft ≤ c.check then Exec.halt
      Exec.meterOp (.charge c.exec)
      Exec.meterOp (.chargeState c.state)
      if c.stateRefill != 0 then Exec.meterOp (.creditStateRefund c.stateRefill)
      if c.refund != 0 then Exec.meterOp (.addRefund c.refund)).run s₁ = .ok ((), s₁') at h₁
    change ∃ s₂', (do
      if c.check != 0 && (← (get : Exec.M Exec.Machine)).meters.top.meter.gasLeft ≤ c.check then Exec.halt
      Exec.meterOp (.charge c.exec)
      Exec.meterOp (.chargeState c.state)
      if c.stateRefill != 0 then Exec.meterOp (.creditStateRefund c.stateRefill)
      if c.refund != 0 then Exec.meterOp (.addRefund c.refund)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂'
    have hp4 : ∀ {a b : Exec.Machine},
        (do
          if c.stateRefill != 0 then Exec.meterOp (.creditStateRefund c.stateRefill)
          if c.refund != 0 then Exec.meterOp (.addRefund c.refund)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt := by
      intro a b h4 hH
      dsimp at h4
      cases hc1 : c.stateRefill != 0 <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte] at h4
      · exact if_addRefund_preserves_halt h4 hH
      · exact seq_preserves_halt meterOp_preserves_halt if_addRefund_preserves_halt h4 hH
    have hp3 : ∀ {a b : Exec.Machine},
        (do
          Exec.meterOp (.chargeState c.state)
          if c.stateRefill != 0 then Exec.meterOp (.creditStateRefund c.stateRefill)
          if c.refund != 0 then Exec.meterOp (.addRefund c.refund)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt :=
      seq_preserves_halt meterOp_preserves_halt hp4
    have hp2 : ∀ {a b : Exec.Machine},
        (do
          Exec.meterOp (.charge c.exec)
          Exec.meterOp (.chargeState c.state)
          if c.stateRefill != 0 then Exec.meterOp (.creditStateRefund c.stateRefill)
          if c.refund != 0 then Exec.meterOp (.addRefund c.refund)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt :=
      seq_preserves_halt meterOp_preserves_halt hp3
    dsimp only at h₁ ⊢
    simp only [stateT_run_eq, stateT_bind_eq, stateT_get_eq] at h₁ ⊢
    by_cases hChk₁ : (c.check != 0 && decide (s₁.meters.top.meter.gasLeft ≤ c.check)) = true
    · simp only [hChk₁, ↓reduceIte, Exec.halt] at h₁
      rw [stateT_bind_eq, stateT_modify_eq] at h₁
      exact absurd (hp2 h₁ rfl) hNoHalt
    · have hGasLE := (liveStackLE_head_meterLE hSim.live_stack_le).gas
      have hChk₂ : (c.check != 0 && decide (s₂.meters.top.meter.gasLeft ≤ c.check)) = false := by
        cases hc0 : c.check != 0 <;> simp_all
        omega
      simp only [hChk₁, hChk₂, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
      refine seq_execSim hSim h₁ hNoHalt hp3 (fun hr hnh => meterOp_charge_execSim hSim hr hnh) ?_
      intro s₁_2 s₂_2 hSim2 hRest2 hNoHalt2
      refine seq_execSim hSim2 hRest2 hNoHalt2 hp4 (fun hr hnh => meterOp_chargeState_execSim hSim2 hr hnh) ?_
      intro s₁_3 s₂_3 hSim3 hRest3 hNoHalt3
      cases hc1 : c.stateRefill != 0 <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hRest3 ⊢
      · exact if_addRefund_execSim hSim3 hRest3
      · exact seq_execSim hSim3 hRest3 hNoHalt3 if_addRefund_preserves_halt
          (fun hr _ => meterOp_creditStateRefund_execSim hSim3 hr)
          (fun hSim4 hr _ => if_addRefund_execSim hSim4 hr)
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem costs_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {cs : Cost.Seq}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.costs cs).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.costs cs).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  induction cs generalizing s₁ s₂ with
  | nil =>
    change (pure () : Exec.M Unit).run s₁ = .ok ((), s₁') at h₁
    simp only [stateT_run_eq, stateT_pure_eq] at h₁
    cases h₁
    exact ⟨s₂, rfl, hSim⟩
  | cons c cs ih =>
    change (do Exec.cost c; Exec.costs cs).run s₁ = .ok ((), s₁') at h₁
    exact seq_execSim hSim h₁ hNoHalt
      (fun hr hH => costs_preserves_halt hr hH)
      (fun hr hnh => cost_execSim hSim hr hnh)
      (fun hSimMid hr _ => ih hSimMid hr)

theorem memory_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {n : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.memory n).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.memory n).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  have h₁' : (do
      Exec.cost { exec := Rules.memoryExpansion s₁.fork s₁.ctx.memory n }
      if ← Exec.running then modify fun (s : Exec.Machine) =>
        { s with ctx.memory := max s.ctx.memory (32 * Rules.wordsForBytes n) }).run s₁ = .ok ((), s₁') := by
    simpa [Exec.memory] using h₁
  suffices ∃ s₂', (do
      Exec.cost { exec := Rules.memoryExpansion s₂.fork s₂.ctx.memory n }
      if ← Exec.running then modify fun (s : Exec.Machine) =>
        { s with ctx.memory := max s.ctx.memory (32 * Rules.wordsForBytes n) }).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' by
    simpa [Exec.memory] using this
  rw [← hSim.fork_eq, ← hSim.ctx_eq]
  refine seq_execSim hSim h₁' hNoHalt ?_
    (fun hr hnh => cost_execSim hSim hr hnh) ?_
  · intro a b hMod hH
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
      hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hMod
    cases hMod
    exact hH
  · intro s₁_mid s₂_mid hSimMid hMod _
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hMod ⊢
    rw [← hSimMid.ctx_eq]
    by_cases hRun : s₁_mid.ctx.outcome.isNone = true
    · simp only [hRun, ↓reduceIte, stateT_modify_eq] at hMod ⊢
      cases hMod
      refine ⟨_, rfl, ?_⟩
      exact ⟨hSimMid.fork_eq, by simp [hSimMid.ctx_eq], hSimMid.world_sim,
        hSimMid.live_stack_le, hSimMid.phase_eq, hSimMid.sites_eq,
        hSimMid.branches_eq, hSimMid.frames_size_eq⟩
    · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hMod ⊢
      cases hMod
      exact ⟨s₂_mid, rfl, hSimMid⟩

theorem terminate_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {e : Terminator}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.terminate e).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.terminate e).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.terminate at h₁ ⊢
  simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte] at h₁ ⊢
    cases e with
    | invalid =>
      simp only [Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
      rcases h₁ with ⟨_, rfl⟩
      exact absurd rfl hNoHalt
    | stop =>
      simp only [stateT_modify_eq] at h₁ ⊢
      cases h₁
      refine ⟨_, rfl, ?_⟩
      exact ⟨hSim.fork_eq, by simp [hSim.ctx_eq], hSim.world_sim,
        hSim.live_stack_le, hSim.phase_eq, hSim.sites_eq,
        hSim.branches_eq, hSim.frames_size_eq⟩
    | «return» n =>
      refine seq_execSim hSim h₁ hNoHalt ?_ (fun hr hnh => memory_execSim hSim hr hnh) ?_
      · intro a b hMod hH
        simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
          hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hMod
        cases hMod; exact hH
      · intro s₁_mid s₂_mid hSimMid hMod _
        simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hMod ⊢
        rw [← hSimMid.ctx_eq]
        by_cases hRun2 : s₁_mid.ctx.outcome.isNone = true
        · simp only [hRun2, ↓reduceIte, stateT_modify_eq] at hMod ⊢
          cases hMod
          refine ⟨_, rfl, ?_⟩
          exact ⟨hSimMid.fork_eq, by simp [hSimMid.ctx_eq], hSimMid.world_sim,
            hSimMid.live_stack_le, hSimMid.phase_eq, hSimMid.sites_eq,
            hSimMid.branches_eq, hSimMid.frames_size_eq⟩
        · simp only [hRun2, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hMod ⊢
          cases hMod
          exact ⟨s₂_mid, rfl, hSimMid⟩
    | revert n =>
      refine seq_execSim hSim h₁ hNoHalt ?_ (fun hr hnh => memory_execSim hSim hr hnh) ?_
      · intro a b hMod hH
        simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
          hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hMod
        cases hMod; exact hH
      · intro s₁_mid s₂_mid hSimMid hMod _
        simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hMod ⊢
        rw [← hSimMid.ctx_eq]
        by_cases hRun2 : s₁_mid.ctx.outcome.isNone = true
        · simp only [hRun2, ↓reduceIte, stateT_modify_eq] at hMod ⊢
          cases hMod
          refine ⟨_, rfl, ?_⟩
          exact ⟨hSimMid.fork_eq, by simp [hSimMid.ctx_eq], hSimMid.world_sim,
            hSimMid.live_stack_le, hSimMid.phase_eq, hSimMid.sites_eq,
            hSimMid.branches_eq, hSimMid.frames_size_eq⟩
        · simp only [hRun2, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hMod ⊢
          cases hMod
          exact ⟨s₂_mid, rfl, hSimMid⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem site_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {id : Nat} {entered : Bool}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.site id entered).run s₁ = .ok ((), s₁')) :
    ∃ s₂', (Exec.site id entered).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  simp only [Exec.site, stateT_run_eq, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at h₁ ⊢
  rcases h₁ with ⟨_, rfl⟩
  let s₂' : Exec.Machine := { s₂ with sites := s₂.sites.map fun x =>
    if x.frame == id then { x with executed := true, entered := entered || x.entered } else x }
  refine ⟨s₂', ?_, ?_⟩
  · constructor <;> trivial
  · have hs : s₁.sites.map (fun x =>
        if x.frame == id then { x with executed := true, entered := entered || x.entered } else x) =
      s₂.sites.map (fun x =>
        if x.frame == id then { x with executed := true, entered := entered || x.entered } else x) :=
      congrArg (fun xs => xs.map (fun x =>
        if x.frame == id then { x with executed := true, entered := entered || x.entered } else x)) hSim.sites_eq
    exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_sim, hSim.live_stack_le,
      hSim.phase_eq, hs, hSim.branches_eq, hSim.frames_size_eq⟩

private def PureOrThrow (m : Exec.M Unit) : Prop :=
  ∀ {a b : Exec.Machine}, m a = .ok ((), b) → b = a ∧ ∀ c, m c = .ok ((), c)

private theorem pureOrThrow_pure : PureOrThrow (pure ()) := by
  intro a b h
  simp only [stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨h.2.symm, fun _ => rfl⟩

private theorem pureOrThrow_throw (e : ExecError) : PureOrThrow (throw e) := by
  intro a b h
  simp [stateT_throw_eq] at h

private theorem pureOrThrow_unsupported (msg : String) : PureOrThrow (Exec.unsupported msg) :=
  pureOrThrow_throw (.unsupported msg)

private theorem pureOrThrow_if {cond : Bool} {m₁ m₂ : Exec.M Unit}
    (h₁ : PureOrThrow m₁) (h₂ : PureOrThrow m₂) :
    PureOrThrow (if cond then m₁ else m₂) := by
  cases cond <;> simpa

private theorem pureOrThrow_ite {p : Prop} [Decidable p] {m₁ m₂ : Exec.M Unit}
    (h₁ : PureOrThrow m₁) (h₂ : PureOrThrow m₂) :
    PureOrThrow (if p then m₁ else m₂) := by
  split <;> assumption

private theorem pureOrThrow_opt {α : Type} {opt : Option α} {m₁ : α → Exec.M Unit} {m₂ : Exec.M Unit}
    (h₁ : ∀ x, PureOrThrow (m₁ x)) (h₂ : PureOrThrow m₂) :
    PureOrThrow (match opt with | some x => m₁ x | none => m₂) := by
  cases opt with
  | none => exact h₂
  | some x => exact h₁ x

private theorem pureOrThrow_seq {m₁ m₂ : Exec.M Unit}
    (h₁ : PureOrThrow m₁) (h₂ : PureOrThrow m₂) :
    PureOrThrow (do m₁; m₂) := by
  intro a b h
  simp only [stateT_bind_eq] at h ⊢
  cases hr₁ : m₁ a with
  | error e => rw [hr₁] at h; cases h
  | ok p =>
    rcases p with ⟨⟨⟩, mid⟩
    rw [hr₁] at h
    obtain ⟨rfl, hc₁⟩ := h₁ hr₁
    obtain ⟨rfl, hc₂⟩ := h₂ h
    refine ⟨rfl, fun c => ?_⟩
    rw [hc₁ c]
    exact hc₂ c

private theorem stateT_get_bind {σ ε α : Type} (f : σ → StateT σ (Except ε) α) (s : σ) :
    (get >>= f) s = f s s := rfl

private theorem unsupported_bind {α β : Type} (msg : String) (k : α → Exec.M β) :
    (Exec.unsupported msg >>= k) = Exec.unsupported msg := rfl

theorem checkTransfer_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {src dst amount : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (hSafe : amount = 0 ∨ src ≠ sender ∨ amount ≤ (s₂.world.getAccount src).balance)
    (h₁ : (Exec.checkTransfer src dst amount).run s₁ = .ok ((), s₁')) :
    (Exec.checkTransfer src dst amount).run s₂ = .ok ((), s₂) ∧ s₁' = s₁ := by
  unfold Exec.checkTransfer at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
  by_cases hc : (src != dst && amount != 0) = true
  · simp only [hc, ↓reduceIte] at h₁ ⊢
    by_cases hbad₁ : (decide ((s₁.world.getAccount src).balance < amount) ||
        decide ((s₁.world.getAccount dst).balance + amount ≥ 2^256)) = true
    · simp [hbad₁, Exec.unsupported, stateT_throw_eq] at h₁
    · simp only [hbad₁, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
      have hbad₁' : ¬ ((s₁.world.getAccount src).balance < amount) ∧
          ¬ ((s₁.world.getAccount dst).balance + amount ≥ 2^256) := by
        simpa [Bool.or_eq_true, decide_eq_true_eq] using hbad₁
      have hdst_le := hSim.world_sim.balance_le dst
      have hsrc_ok : ¬ ((s₂.world.getAccount src).balance < amount) := by
        rcases hSafe with rfl | hne | hle
        · omega
        · rw [← hSim.world_sim.getAccount_ne hne]; exact hbad₁'.1
        · omega
      have hbad₂ : (decide ((s₂.world.getAccount src).balance < amount) ||
          decide ((s₂.world.getAccount dst).balance + amount ≥ 2^256)) = false := by
        simp [Bool.or_eq_false_iff, decide_eq_false_iff_not, hsrc_ok]
        omega
      simp only [hbad₂, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq]
      exact ⟨trivial, h₁.2.symm⟩
  · simp only [hc, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq]
    simp only [hc, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
    exact ⟨trivial, h₁.2.symm⟩

theorem validateFrame_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    {f : Frame} {syntheticNative : Bool}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.validateFrame f syntheticNative).run s₁ = .ok ((), s₁')) :
    (Exec.validateFrame f syntheticNative).run s₂ = .ok ((), s₂) ∧ s₁' = s₁ := by
  unfold Exec.validateFrame at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind, unsupported_bind] at h₁ ⊢
  rw [← hSim.ctx_eq, ← hSim.fork_eq]
  have hcode : ∀ a, (s₂.world.getAccount a).code = (s₁.world.getAccount a).code :=
    fun a => (hSim.world_sim.code_eq a).symm
  simp only [hcode]
  have hP : ∀ {m : Exec.M Unit}, PureOrThrow m → m s₁ = .ok ((), s₁') → m s₂ = .ok ((), s₂) ∧ s₁' = s₁ := by
    intro m hm h
    obtain ⟨rfl, hc⟩ := hm h
    exact ⟨hc s₂, rfl⟩
  refine hP ?_ h₁
  cases f.info.account <;> cases f.info.codeAddress <;> cases s₁.ctx.codeAddress <;> dsimp only <;>
    repeat first
      | apply pureOrThrow_if
      | apply pureOrThrow_ite
      | apply pureOrThrow_unsupported
      | apply pureOrThrow_throw
      | exact pureOrThrow_pure

private theorem throw_bind {α β : Type} (e : ExecError) (k : α → Exec.M β) :
    (throw e >>= k) = throw e := rfl

theorem precompile_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    {addr len : Nat} {output : Observed OutputFacts}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.precompile addr len output).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.precompile addr len output).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.precompile at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind, unsupported_bind, throw_bind] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hBad : (s₁.ctx.disablePrecompiles || s₁.ctx.codeAddress != some addr) = true
  · simp [hBad, stateT_throw_eq] at h₁
  · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
    have hcharge : ∀ (charge : Nat),
        (do
          Exec.cost { exec := charge }
          if ← Exec.running then
            let facts ← Exec.required "precompile.output" (output.lookup (← get).fork)
            if (addr == 1 && facts.len != 0 && facts.len != 32) ||
                (addr == 2 && facts.len != 32) || (addr == 4 && facts.len != len) then
              Exec.unsupported "inconsistent precompile output length"
            modify fun (s : Exec.Machine) => { s with ctx := { s.ctx with
              outputLen := facts.len, outcome := some .success } }) s₁ = .ok ((), s₁') →
        ∃ s₂', (do
          Exec.cost { exec := charge }
          if ← Exec.running then
            let facts ← Exec.required "precompile.output" (output.lookup (← get).fork)
            if (addr == 1 && facts.len != 0 && facts.len != 32) ||
                (addr == 2 && facts.len != 32) || (addr == 4 && facts.len != len) then
              Exec.unsupported "inconsistent precompile output length"
            modify fun (s : Exec.Machine) => { s with ctx := { s.ctx with
              outputLen := facts.len, outcome := some .success } }) s₂ = .ok ((), s₂') ∧
          ExecSim sender s₁' s₂' := by
      intro charge hc₁
      refine seq_execSim hSim hc₁ hNoHalt ?_ (fun hr hnh => cost_execSim hSim hr hnh) ?_
      · intro a b hRest hH
        simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
          hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hRest
        cases hRest; exact hH
      · intro s₁_mid s₂_mid hSimMid hRest _
        simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hRest ⊢
        rw [← hSimMid.ctx_eq]
        by_cases hRun : s₁_mid.ctx.outcome.isNone = true
        · simp only [hRun, ↓reduceIte, stateT_bind_eq, stateT_get_eq] at hRest ⊢
          rw [← hSimMid.fork_eq]
          cases hreq : output.lookup s₁_mid.fork with
          | none =>
            simp [hreq, Exec.required, Exec.unsupported, stateT_bind_eq, stateT_throw_eq] at hRest
          | some facts =>
            simp only [hreq, Exec.required, stateT_bind_eq, stateT_pure_eq, unsupported_bind] at hRest ⊢
            by_cases hLen : ((addr == 1 && facts.len != 0 && facts.len != 32) ||
                (addr == 2 && facts.len != 32) || (addr == 4 && facts.len != len)) = true
            · simp [hLen, Exec.unsupported, stateT_throw_eq] at hRest
            · simp only [hLen, Bool.false_eq_true, ↓reduceIte, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hRest ⊢
              rcases hRest with ⟨_, rfl⟩
              refine ⟨_, ⟨trivial, rfl⟩, ?_⟩
              exact ⟨hSimMid.fork_eq, by simp [hSimMid.ctx_eq], hSimMid.world_sim,
                hSimMid.live_stack_le, hSimMid.phase_eq, hSimMid.sites_eq,
                hSimMid.branches_eq, hSimMid.frames_size_eq⟩
        · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hRest ⊢
          cases hRest
          exact ⟨s₂_mid, rfl, hSimMid⟩
    cases addr with
    | zero => simp [Exec.unsupported, unsupported_bind, stateT_throw_eq] at h₁
    | succ n =>
      cases n with
      | zero => exact hcharge 3000 h₁
      | succ n =>
        cases n with
        | zero => exact hcharge (60 + 12 * Rules.wordsForBytes len) h₁
        | succ n =>
          cases n with
          | zero => simp [Exec.unsupported, unsupported_bind, stateT_throw_eq] at h₁
          | succ n =>
            cases n with
            | zero => exact hcharge (15 + 3 * Rules.wordsForBytes len) h₁
            | succ _ => simp [Exec.unsupported, unsupported_bind, stateT_throw_eq] at h₁

theorem deposit_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    {outputFacts : Observed OutputFacts}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.deposit outputFacts).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.deposit outputFacts).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.deposit at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind, unsupported_bind] at h₁ ⊢
  rw [← hSim.ctx_eq, ← hSim.fork_eq]
  by_cases hSucc : (s₁.ctx.outcome == some .success) = true
  · simp only [hSucc, ↓reduceIte, stateT_bind_eq, stateT_modify_eq] at h₁ ⊢
    cases hreq : outputFacts.lookup s₁.fork with
    | none =>
      simp [hreq, Exec.required, Exec.unsupported, stateT_throw_eq] at h₁
    | some output =>
      simp only [hreq, Exec.required, stateT_pure_eq, unsupported_bind] at h₁ ⊢
      by_cases hLen : (output.len != s₁.ctx.outputLen) = true
      · simp [hLen, Exec.unsupported, stateT_throw_eq] at h₁
      · simp only [hLen, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
        by_cases hEF : output.startsWithEF = true
        · simp only [hEF, ↓reduceIte, Exec.halt, stateT_modify_eq, Exec.running, stateT_get_eq,
            stateT_pure_eq, Option.isNone, Bool.false_eq_true, Except.ok.injEq, Prod.mk.injEq] at h₁
          rcases h₁ with ⟨_, rfl⟩
          exact absurd rfl hNoHalt
        · simp only [hEF, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
          by_cases hAllow : (!Create.codeDepositAllowed s₁.fork.schedule s₁.ctx.outputLen false) = true
          · simp only [hAllow, ↓reduceIte, Exec.halt, stateT_modify_eq, Exec.running, stateT_get_eq,
              stateT_pure_eq, Option.isNone, Bool.false_eq_true, Except.ok.injEq, Prod.mk.injEq] at h₁
            rcases h₁ with ⟨_, rfl⟩
            exact absurd rfl hNoHalt
          · simp only [hAllow, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
            let s₁_0 : Exec.Machine := { s₁ with ctx.outcome := none }
            let s₂_0 : Exec.Machine := { s₂ with ctx.outcome := none }
            have hSim0 : ExecSim sender s₁_0 s₂_0 :=
              ⟨hSim.fork_eq, by simp [s₁_0, s₂_0, hSim.ctx_eq], hSim.world_sim,
                hSim.live_stack_le, hSim.phase_eq, hSim.sites_eq,
                hSim.branches_eq, hSim.frames_size_eq⟩
            refine seq_execSim hSim0 h₁ hNoHalt ?_
              (fun hr hnh => cost_execSim hSim0 hr hnh) ?_
            · intro a b hRest hH
              simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
                hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hRest
              cases hRest; exact hH
            · intro s₁_mid s₂_mid hSimMid hRest _
              simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hRest ⊢
              rw [← hSimMid.ctx_eq]
              by_cases hRun : s₁_mid.ctx.outcome.isNone = true
              · simp only [hRun, ↓reduceIte, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hRest ⊢
                rcases hRest with ⟨_, rfl⟩
                refine ⟨_, ⟨trivial, rfl⟩, ?_⟩
                refine ⟨hSimMid.fork_eq, by simp [hSimMid.ctx_eq], ?_,
                  hSimMid.live_stack_le, hSimMid.phase_eq, hSimMid.sites_eq,
                  hSimMid.branches_eq, hSimMid.frames_size_eq⟩
                rw [← hSimMid.ctx_eq]
                exact hSimMid.world_sim.modifyAccount_code_preserves _ _
              · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hRest ⊢
                cases hRest
                exact ⟨s₂_mid, rfl, hSimMid⟩
  · simp only [hSucc, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem selfdestruct_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {addr : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (hAccNe : s₁.ctx.account ≠ sender)
    (h₁ : (Exec.selfdestruct addr).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.selfdestruct addr).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.selfdestruct at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
  have hbal : (s₂.world.getAccount s₂.ctx.account).balance = (s₁.world.getAccount s₁.ctx.account).balance := by
    rw [← hSim.ctx_eq, hSim.world_sim.getAccount_ne hAccNe]
  have hwarm : s₂.world.isAddressWarm addr = s₁.world.isAddressWarm addr :=
    (hSim.world_sim.warmAddr addr).symm
  have halive : s₂.world.isAlive addr = s₁.world.isAlive addr :=
    (hSim.world_sim.isAlive_eq addr).symm
  rw [hbal, hwarm, halive, ← hSim.ctx_eq, ← hSim.fork_eq]
  by_cases hStaticAms : (s₁.fork == .amsterdam && s₁.ctx.isStatic) = true
  · simp only [hStaticAms, ↓reduceIte, Exec.halt, stateT_bind_eq, stateT_modify_eq,
      stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
    rcases h₁ with ⟨_, rfl⟩
    exact absurd rfl hNoHalt
  · simp only [hStaticAms, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
    refine seq_execSim hSim h₁ hNoHalt ?_
      (fun hr hnh => cost_execSim hSim hr hnh) ?_
    · intro a b hRest hH
      simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
        hH, Option.isNone, Bool.false_eq_true, ↓reduceIte, Bool.false_and] at hRest
      cases hRest; exact hH
    · intro s₁_mid s₂_mid hSimMid hRest _
      simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hRest ⊢
      rw [← hSimMid.ctx_eq]
      cases hRun : s₁_mid.ctx.outcome.isNone with
      | false =>
        simp only [hRun, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          stateT_bind_eq, stateT_get_eq, stateT_pure_eq, ← hSimMid.ctx_eq] at hRest ⊢
        cases hRest
        exact ⟨s₂_mid, rfl, hSimMid⟩
      | true =>
        simp only [hRun, Bool.true_and, ↓reduceIte] at hRest ⊢
        by_cases hStat : s₁.ctx.isStatic = true
        · simp only [hStat, ↓reduceIte, Exec.halt, stateT_bind_eq, stateT_modify_eq,
            stateT_get_eq, stateT_pure_eq, Option.isNone, Bool.false_eq_true,
            Except.ok.injEq, Prod.mk.injEq] at hRest
          rcases hRest with ⟨_, rfl⟩
          exact absurd rfl hNoHalt
        · simp only [hStat, Bool.false_eq_true, ↓reduceIte, stateT_bind_eq,
            stateT_get_eq, stateT_pure_eq, ← hSimMid.ctx_eq, hRun] at hRest ⊢
          cases hct : (Exec.checkTransfer s₁.ctx.account addr (s₁.world.getAccount s₁.ctx.account).balance).run s₁_mid with
          | error e =>
            simp only [stateT_run_eq] at hct
            rw [hct] at hRest; cases hRest
          | ok p =>
            rcases p with ⟨⟨⟩, s₁_ct⟩
            obtain ⟨hct₂, hct_eq⟩ := checkTransfer_execSim hSimMid (Or.inr (Or.inl hAccNe)) hct
            subst s₁_ct
            simp only [stateT_run_eq] at hct hct₂
            rw [hct] at hRest
            rw [hct₂]
            simp only [stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hRest ⊢
            rcases hRest with ⟨_, rfl⟩
            refine ⟨_, ⟨trivial, rfl⟩, ?_⟩
            have hcr : ∀ a, s₂_mid.world.isCreated a = s₁_mid.world.isCreated a :=
              fun a => (hSimMid.world_sim.isCreated_eq a).symm
            have hmov : CommittedEffects.movement s₂_mid.fork s₂_mid.world s₂_mid.ctx.account addr (s₁.world.getAccount s₁.ctx.account).balance true =
                CommittedEffects.movement s₂_mid.fork s₁_mid.world s₂_mid.ctx.account addr (s₁.world.getAccount s₁.ctx.account).balance true :=
              (hSimMid.world_sim.movement_eq _ _ _ _ true).symm
            refine ⟨hSimMid.fork_eq, by simp [hSimMid.ctx_eq, hSimMid.fork_eq, hcr, hmov], ?_,
              hSimMid.live_stack_le, hSimMid.phase_eq, hSimMid.sites_eq,
              hSimMid.branches_eq, hSimMid.frames_size_eq⟩
            rw [← hSimMid.fork_eq, ← hSimMid.ctx_eq, hcr]
            have hm := hSimMid.world_sim.moveEther_preserves s₁_mid.ctx.account addr (s₁.world.getAccount s₁.ctx.account).balance
            split
            · refine (hm.modifyAccount_preserves s₁_mid.ctx.account _ ?_).warmAddress_preserves addr
              intro hd; subst hd
              exact ⟨hm.sender_nonce, hm.sender_code, hm.sender_nonce_nz, Nat.le_refl 0⟩
            · exact hm.warmAddress_preserves addr

theorem memory_preserves_halt {n : Nat} {s s' : Exec.Machine}
    (h : (Exec.memory n).run s = .ok ((), s'))
    (hHalt : s.ctx.outcome = some .halt) :
    s'.ctx.outcome = some .halt := by
  have h' : (do
      Exec.cost { exec := Rules.memoryExpansion s.fork s.ctx.memory n }
      if ← Exec.running then modify fun (s : Exec.Machine) =>
        { s with ctx.memory := max s.ctx.memory (32 * Rules.wordsForBytes n) }).run s = .ok ((), s') := by
    simpa [Exec.memory] using h
  refine seq_preserves_halt cost_preserves_halt ?_ h' hHalt
  intro a b hMod hH
  simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
    hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hMod
  cases hMod; exact hH

private theorem meterOp_outcome_eq {op : MeterStack.Op} {s s' : Exec.Machine}
    (h : (Exec.meterOp op).run s = .ok ((), s'))
    (hNoHalt : s'.ctx.outcome ≠ some .halt) :
    s'.ctx.outcome = s.ctx.outcome := by
  unfold Exec.meterOp Exec.running at h
  simp only [stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at h
  by_cases hRun : s.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte, stateT_bind_eq, stateT_bind_raw, stateT_get_eq] at h
    cases hm : MeterStack.apply op s.meters with
    | error e =>
      rw [hm] at h
      cases e with
      | outOfGas =>
        simp only [Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl⟩
        exact absurd rfl hNoHalt
      | assertion a =>
        simp only [stateT_throw_eq] at h; cases h
    | ok m' =>
      rw [hm] at h
      simp only [stateT_set_eq, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩; rfl
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩; rfl

private theorem if_addRefund_outcome_eq {cond : Bool} {d : Int} {s s' : Exec.Machine}
    (h : (if cond then Exec.meterOp (.addRefund d) else pure ()).run s = .ok ((), s'))
    (hNoHalt : s'.ctx.outcome ≠ some .halt) :
    s'.ctx.outcome = s.ctx.outcome := by
  cases cond
  · simp only [Bool.false_eq_true, ↓reduceIte, stateT_run_eq, stateT_pure_eq] at h
    cases h; rfl
  · simp only [↓reduceIte] at h
    exact meterOp_outcome_eq h hNoHalt

private theorem seq_outcome_eq {m₁ m₂ : Exec.M Unit} {s s' : Exec.Machine}
    (hPres : ∀ {a b : Exec.Machine}, m₂.run a = .ok ((), b) → a.ctx.outcome = some .halt → b.ctx.outcome = some .halt)
    (hm₁ : ∀ {a b : Exec.Machine}, m₁.run a = .ok ((), b) → b.ctx.outcome ≠ some .halt → b.ctx.outcome = a.ctx.outcome)
    (hm₂ : ∀ {a b : Exec.Machine}, m₂.run a = .ok ((), b) → b.ctx.outcome ≠ some .halt → b.ctx.outcome = a.ctx.outcome)
    (h : (do m₁; m₂).run s = .ok ((), s'))
    (hNoHalt : s'.ctx.outcome ≠ some .halt) :
    s'.ctx.outcome = s.ctx.outcome := by
  simp only [stateT_run_eq, stateT_bind_eq] at h
  cases hr₁ : m₁ s with
  | error e => rw [hr₁] at h; cases h
  | ok p =>
    rcases p with ⟨⟨⟩, s_mid⟩
    rw [hr₁] at h
    have hMidNoHalt : s_mid.ctx.outcome ≠ some .halt := fun hH => hNoHalt (hPres h hH)
    exact (hm₂ h hNoHalt).trans (hm₁ hr₁ hMidNoHalt)

private theorem cost_outcome_eq {c : Cost} {s s' : Exec.Machine}
    (h : (Exec.cost c).run s = .ok ((), s'))
    (hNoHalt : s'.ctx.outcome ≠ some .halt) :
    s'.ctx.outcome = s.ctx.outcome := by
  unfold Exec.cost at h
  simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at h
  by_cases hRun : s.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte] at h
    change (do
      if c.check != 0 && (← (get : Exec.M Exec.Machine)).meters.top.meter.gasLeft ≤ c.check then Exec.halt
      Exec.meterOp (.charge c.exec)
      Exec.meterOp (.chargeState c.state)
      if c.stateRefill != 0 then Exec.meterOp (.creditStateRefund c.stateRefill)
      if c.refund != 0 then Exec.meterOp (.addRefund c.refund)).run s = .ok ((), s') at h
    have hp4 : ∀ {a b : Exec.Machine},
        (do
          if c.stateRefill != 0 then Exec.meterOp (.creditStateRefund c.stateRefill)
          if c.refund != 0 then Exec.meterOp (.addRefund c.refund)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt := by
      intro a b h4 hH
      dsimp at h4
      cases hc1 : c.stateRefill != 0 <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte] at h4
      · exact if_addRefund_preserves_halt h4 hH
      · exact seq_preserves_halt meterOp_preserves_halt if_addRefund_preserves_halt h4 hH
    have hp3 : ∀ {a b : Exec.Machine},
        (do
          Exec.meterOp (.chargeState c.state)
          if c.stateRefill != 0 then Exec.meterOp (.creditStateRefund c.stateRefill)
          if c.refund != 0 then Exec.meterOp (.addRefund c.refund)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt :=
      seq_preserves_halt meterOp_preserves_halt hp4
    have hp2 : ∀ {a b : Exec.Machine},
        (do
          Exec.meterOp (.charge c.exec)
          Exec.meterOp (.chargeState c.state)
          if c.stateRefill != 0 then Exec.meterOp (.creditStateRefund c.stateRefill)
          if c.refund != 0 then Exec.meterOp (.addRefund c.refund)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt :=
      seq_preserves_halt meterOp_preserves_halt hp3
    dsimp only at h
    simp only [stateT_run_eq, stateT_bind_eq, stateT_get_eq] at h
    by_cases hChk : (c.check != 0 && decide (s.meters.top.meter.gasLeft ≤ c.check)) = true
    · simp only [hChk, ↓reduceIte, Exec.halt] at h
      rw [stateT_bind_eq, stateT_modify_eq] at h
      exact absurd (hp2 h rfl) hNoHalt
    · simp only [hChk, Bool.false_eq_true, ↓reduceIte] at h
      refine seq_outcome_eq hp3 meterOp_outcome_eq ?_ h hNoHalt
      intro a2 b2 h2 hnh2
      refine seq_outcome_eq hp4 meterOp_outcome_eq ?_ h2 hnh2
      intro a3 b3 h3 hnh3
      cases hc1 : c.stateRefill != 0 <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte] at h3
      · exact if_addRefund_outcome_eq h3 hnh3
      · exact seq_outcome_eq if_addRefund_preserves_halt meterOp_outcome_eq if_addRefund_outcome_eq h3 hnh3
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩; rfl

private theorem memory_outcome_eq {n : Nat} {s s' : Exec.Machine}
    (h : (Exec.memory n).run s = .ok ((), s'))
    (hNoHalt : s'.ctx.outcome ≠ some .halt) :
    s'.ctx.outcome = s.ctx.outcome := by
  have h' : (do
      Exec.cost { exec := Rules.memoryExpansion s.fork s.ctx.memory n }
      if ← Exec.running then modify fun (s : Exec.Machine) =>
        { s with ctx.memory := max s.ctx.memory (32 * Rules.wordsForBytes n) }).run s = .ok ((), s') := by
    simpa [Exec.memory] using h
  refine seq_outcome_eq ?_ cost_outcome_eq ?_ h' hNoHalt
  · intro a b hMod hH
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
      hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hMod
    cases hMod; exact hH
  · intro a b hMod _
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hMod
    by_cases hRun : a.ctx.outcome.isNone = true
    · simp only [hRun, ↓reduceIte, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hMod
      rcases hMod with ⟨_, rfl⟩; rfl
    · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at hMod
      rcases hMod with ⟨_, rfl⟩; rfl

private theorem terminate_revert_preserves_halt {len : Nat} {s s' : Exec.Machine}
    (h : (Exec.terminate (.revert len)).run s = .ok ((), s'))
    (hHalt : s.ctx.outcome = some .halt) :
    s'.ctx.outcome = some .halt := by
  unfold Exec.terminate Exec.running at h
  simp only [stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
    hHalt, Option.isNone, Bool.false_eq_true, ↓reduceIte] at h
  cases h; exact hHalt

private theorem terminate_revert_of_none {len : Nat} {s s' : Exec.Machine}
    (h : (Exec.terminate (.revert len)).run s = .ok ((), s'))
    (hNone : s.ctx.outcome = none)
    (hNoHalt : s'.ctx.outcome ≠ some .halt) :
    s'.ctx.outcome = some .revert := by
  unfold Exec.terminate at h
  simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
    hNone, Option.isNone, ↓reduceIte] at h
  cases hm : (Exec.memory len).run s with
  | error e =>
    simp only [stateT_run_eq] at hm
    rw [hm] at h; cases h
  | ok p =>
    rcases p with ⟨⟨⟩, s_mid⟩
    have hm' : Exec.memory len s = .ok ((), s_mid) := hm
    rw [hm'] at h
    have hMidNoHalt : s_mid.ctx.outcome ≠ some .halt := by
      intro hH
      simp only [hH, Option.isNone, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      exact hNoHalt hH
    have hMidNone : s_mid.ctx.outcome = none := (memory_outcome_eq hm hMidNoHalt).trans hNone
    simp only [hMidNone, Option.isNone, ↓reduceIte, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩; simp

theorem basic_native_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    {addr : Address} {input : Precompile.Input} {failure : Option String} {output : Observed OutputFacts}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.basic (.native addr input failure output)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.basic (.native addr input failure output)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.basic at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind, throw_bind] at h₁ ⊢
  rw [← hSim.ctx_eq, ← hSim.fork_eq]
  by_cases hBad : (s₁.ctx.codeAddress != some (Exec.Address.decode addr) ||
      s₁.ctx.disablePrecompiles || !(Exec.Address.decode addr ∈ State.precompileAddresses s₁.fork)) = true
  · simp [hBad, stateT_throw_eq] at h₁
  · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
    cases hq : Precompile.quote s₁.fork (Exec.Address.decode addr) input with
    | error e =>
      simp only [hq, Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
      rcases h₁ with ⟨_, rfl⟩
      exact absurd rfl hNoHalt
    | ok n =>
      simp only [hq] at h₁ ⊢
      refine seq_execSim hSim h₁ hNoHalt ?_ (fun hr hnh => cost_execSim hSim hr hnh) ?_
      · intro a b hRest hH
        simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
          hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hRest
        cases hRest; exact hH
      · intro s₁_mid s₂_mid hSimMid hRest _
        simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hRest ⊢
        rw [← hSimMid.ctx_eq]
        by_cases hRun : s₁_mid.ctx.outcome.isNone = true
        · simp only [hRun, ↓reduceIte] at hRest ⊢
          cases failure with
          | some err =>
            simp only [Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hRest
            rcases hRest with ⟨_, rfl⟩
            exact absurd rfl hNoHalt
          | none =>
            simp only [stateT_bind_eq] at hRest ⊢
            cases hreq : output.lookup s₁.fork with
            | none =>
              simp [hreq, Exec.required, Exec.unsupported, stateT_throw_eq] at hRest
            | some facts =>
              simp only [hreq, Exec.required, stateT_pure_eq, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hRest ⊢
              rcases hRest with ⟨_, rfl⟩
              refine ⟨_, ⟨trivial, rfl⟩, ?_⟩
              exact ⟨hSimMid.fork_eq, by simp [hSimMid.ctx_eq], hSimMid.world_sim,
                hSimMid.live_stack_le, hSimMid.phase_eq, hSimMid.sites_eq,
                hSimMid.branches_eq, hSimMid.frames_size_eq⟩
        · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hRest ⊢
          cases hRest
          exact ⟨s₂_mid, rfl, hSimMid⟩

private theorem seq_terminate_revert_of_none {m₁ m₂ : Exec.M Unit}
    (hPres : ∀ {a b : Exec.Machine}, m₂.run a = .ok ((), b) → a.ctx.outcome = some .halt → b.ctx.outcome = some .halt)
    (hm₁ : ∀ {a b : Exec.Machine}, m₁.run a = .ok ((), b) → b.ctx.outcome ≠ some .halt → b.ctx.outcome = a.ctx.outcome)
    (hm₂ : ∀ {a b : Exec.Machine}, m₂.run a = .ok ((), b) → a.ctx.outcome = none → b.ctx.outcome ≠ some .halt → b.ctx.outcome = some .revert)
    {s s' : Exec.Machine}
    (h : (do m₁; m₂).run s = .ok ((), s'))
    (hNone : s.ctx.outcome = none)
    (hNoHalt : s'.ctx.outcome ≠ some .halt) :
    s'.ctx.outcome = some .revert := by
  simp only [stateT_run_eq, stateT_bind_eq] at h
  cases hr₁ : m₁ s with
  | error e => rw [hr₁] at h; cases h
  | ok p =>
    rcases p with ⟨⟨⟩, s_mid⟩
    rw [hr₁] at h
    have hMidNoHalt : s_mid.ctx.outcome ≠ some .halt := fun hH => hNoHalt (hPres h hH)
    exact hm₂ h ((hm₁ hr₁ hMidNoHalt).trans hNone) hNoHalt

theorem basic_gasGuard_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {k : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (hNone : s₁.ctx.outcome = none)
    (h₁ : (Exec.basic (.gasGuard k)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt)
    (hNoRev : s₁'.ctx.outcome ≠ some .revert) :
    ∃ s₂', (Exec.basic (.gasGuard k)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.basic at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
  by_cases hUnder₁ : s₁.meters.top.meter.gasLeft < k + 29
  · simp only [hUnder₁, ↓reduceIte] at h₁
    have hp5 : ∀ {a b : Exec.Machine},
        (do Exec.cost { exec := 6 }; Exec.terminate (.revert 36)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt :=
      seq_preserves_halt cost_preserves_halt terminate_revert_preserves_halt
    have hp4 : ∀ {a b : Exec.Machine},
        (do Exec.memory 36; Exec.cost { exec := 6 }; Exec.terminate (.revert 36)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt :=
      seq_preserves_halt memory_preserves_halt hp5
    have hp3 : ∀ {a b : Exec.Machine},
        (do Exec.cost { exec := 9 }; Exec.memory 36; Exec.cost { exec := 6 }; Exec.terminate (.revert 36)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt :=
      seq_preserves_halt cost_preserves_halt hp4
    have hp2 : ∀ {a b : Exec.Machine},
        (do Exec.memory 32; Exec.cost { exec := 9 }; Exec.memory 36; Exec.cost { exec := 6 }; Exec.terminate (.revert 36)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt :=
      seq_preserves_halt memory_preserves_halt hp3
    have hp1 : ∀ {a b : Exec.Machine},
        (do Exec.cost { exec := 15 }; Exec.memory 32; Exec.cost { exec := 9 }; Exec.memory 36; Exec.cost { exec := 6 }; Exec.terminate (.revert 36)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt :=
      seq_preserves_halt cost_preserves_halt hp2
    have hr5 : ∀ {a b : Exec.Machine},
        (do Exec.cost { exec := 6 }; Exec.terminate (.revert 36)).run a = .ok ((), b) →
        a.ctx.outcome = none → b.ctx.outcome ≠ some .halt → b.ctx.outcome = some .revert :=
      seq_terminate_revert_of_none terminate_revert_preserves_halt cost_outcome_eq terminate_revert_of_none
    have hr4 : ∀ {a b : Exec.Machine},
        (do Exec.memory 36; Exec.cost { exec := 6 }; Exec.terminate (.revert 36)).run a = .ok ((), b) →
        a.ctx.outcome = none → b.ctx.outcome ≠ some .halt → b.ctx.outcome = some .revert :=
      seq_terminate_revert_of_none hp5 memory_outcome_eq hr5
    have hr3 : ∀ {a b : Exec.Machine},
        (do Exec.cost { exec := 9 }; Exec.memory 36; Exec.cost { exec := 6 }; Exec.terminate (.revert 36)).run a = .ok ((), b) →
        a.ctx.outcome = none → b.ctx.outcome ≠ some .halt → b.ctx.outcome = some .revert :=
      seq_terminate_revert_of_none hp4 cost_outcome_eq hr4
    have hr2 : ∀ {a b : Exec.Machine},
        (do Exec.memory 32; Exec.cost { exec := 9 }; Exec.memory 36; Exec.cost { exec := 6 }; Exec.terminate (.revert 36)).run a = .ok ((), b) →
        a.ctx.outcome = none → b.ctx.outcome ≠ some .halt → b.ctx.outcome = some .revert :=
      seq_terminate_revert_of_none hp3 memory_outcome_eq hr3
    have hr1 : ∀ {a b : Exec.Machine},
        (do Exec.cost { exec := 15 }; Exec.memory 32; Exec.cost { exec := 9 }; Exec.memory 36; Exec.cost { exec := 6 }; Exec.terminate (.revert 36)).run a = .ok ((), b) →
        a.ctx.outcome = none → b.ctx.outcome ≠ some .halt → b.ctx.outcome = some .revert :=
      seq_terminate_revert_of_none hp2 cost_outcome_eq hr2
    have hr0 : ∀ {a b : Exec.Machine},
        (do Exec.cost { exec := 25 }; Exec.cost { exec := 15 }; Exec.memory 32; Exec.cost { exec := 9 }; Exec.memory 36; Exec.cost { exec := 6 }; Exec.terminate (.revert 36)).run a = .ok ((), b) →
        a.ctx.outcome = none → b.ctx.outcome ≠ some .halt → b.ctx.outcome = some .revert :=
      seq_terminate_revert_of_none hp1 cost_outcome_eq hr1
    exact absurd (hr0 h₁ hNone hNoHalt) hNoRev
  · have hGasLE := (liveStackLE_head_meterLE hSim.live_stack_le).gas
    have hUnder₂ : ¬ (s₂.meters.top.meter.gasLeft < k + 29) := by omega
    simp only [hUnder₁, hUnder₂, ↓reduceIte] at h₁ ⊢
    exact seq_execSim hSim h₁ hNoHalt cost_preserves_halt
      (fun hr hnh => cost_execSim hSim hr hnh)
      (fun hSimMid hr hnh => cost_execSim hSimMid hr hnh)

theorem basic_returndataCopy_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {offset len : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.basic (.returndataCopy offset len)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.basic (.returndataCopy offset len)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.basic at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
  rw [← hSim.fork_eq, ← hSim.ctx_eq]
  have hpTail : ∀ {a b : Exec.Machine},
      (do if (← Exec.running) && decide (offset + len > s₁.ctx.returnLen) then Exec.halt "OutOfBoundsRead").run a = .ok ((), b) →
      a.ctx.outcome = some .halt → b.ctx.outcome = some .halt := by
    intro a b hRest hH
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
      hH, Option.isNone, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hRest
    cases hRest; exact hH
  refine seq_execSim hSim h₁ hNoHalt (seq_preserves_halt memory_preserves_halt hpTail)
    (fun hr hnh => cost_execSim hSim hr hnh) ?_
  intro s₁_1 s₂_1 hSim1 hRest1 hnh1
  refine seq_execSim hSim1 hRest1 hnh1 hpTail
    (fun hr hnh => memory_execSim hSim1 hr hnh) ?_
  intro s₁_2 s₂_2 hSim2 hRest2 _
  simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hRest2 ⊢
  rw [← hSim2.ctx_eq]
  by_cases hCond : (s₁_2.ctx.outcome.isNone && decide (offset + len > s₁.ctx.returnLen)) = true
  · simp only [hCond, ↓reduceIte, Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hRest2
    rcases hRest2 with ⟨_, rfl⟩
    exact absurd rfl hNoHalt
  · simp only [hCond, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hRest2 ⊢
    cases hRest2
    exact ⟨s₂_2, rfl, hSim2⟩

theorem basic_sload_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {slot : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.basic (.sload slot)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.basic (.sload slot)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.basic at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
  have hwarm : s₂.world.isSlotWarm s₂.ctx.account slot = s₁.world.isSlotWarm s₁.ctx.account slot := by
    rw [← hSim.ctx_eq]
    exact (hSim.world_sim.warmSlot s₁.ctx.account slot).symm
  rw [hwarm, ← hSim.fork_eq, ← hSim.ctx_eq]
  refine seq_execSim hSim h₁ hNoHalt ?_ (fun hr hnh => cost_execSim hSim hr hnh) ?_
  · intro a b hRest hH
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
      hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hRest
    cases hRest; exact hH
  · intro s₁_mid s₂_mid hSimMid hRest _
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hRest ⊢
    rw [← hSimMid.ctx_eq]
    by_cases hRun : s₁_mid.ctx.outcome.isNone = true
    · simp only [hRun, ↓reduceIte, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hRest ⊢
      rcases hRest with ⟨_, rfl⟩
      refine ⟨_, ⟨trivial, rfl⟩, ?_⟩
      exact ⟨hSimMid.fork_eq, hSimMid.ctx_eq, hSimMid.world_sim.warmSlot_preserves s₁.ctx.account slot,
        hSimMid.live_stack_le, hSimMid.phase_eq, hSimMid.sites_eq,
        hSimMid.branches_eq, hSimMid.frames_size_eq⟩
    · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hRest ⊢
      cases hRest
      exact ⟨s₂_mid, rfl, hSimMid⟩

theorem basic_sstore_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {slot value : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.basic (.sstore slot value)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.basic (.sstore slot value)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.basic at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
  have hwarm : s₂.world.isSlotWarm s₂.ctx.account slot = s₁.world.isSlotWarm s₁.ctx.account slot := by
    rw [← hSim.ctx_eq]; exact (hSim.world_sim.warmSlot s₁.ctx.account slot).symm
  have horig : s₂.world.getStorageOriginal s₂.ctx.account slot = s₁.world.getStorageOriginal s₁.ctx.account slot := by
    rw [← hSim.ctx_eq]; exact (hSim.world_sim.getStorageOriginal_eq s₁.ctx.account slot).symm
  have hcur : s₂.world.getStorage s₂.ctx.account slot = s₁.world.getStorage s₁.ctx.account slot := by
    rw [← hSim.ctx_eq]; exact (hSim.world_sim.storage s₁.ctx.account slot).symm
  rw [hwarm, horig, hcur, ← hSim.fork_eq, ← hSim.ctx_eq]
  by_cases hStatAms : (s₁.fork == .amsterdam && s₁.ctx.isStatic) = true
  · simp only [hStatAms, ↓reduceIte, Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
    rcases h₁ with ⟨_, rfl⟩
    exact absurd rfl hNoHalt
  · simp only [hStatAms, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
    refine seq_execSim hSim h₁ hNoHalt ?_ (fun hr hnh => costs_execSim hSim hr hnh) ?_
    · intro a b hRest hH
      simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
        hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hRest
      cases hRest; exact hH
    · intro s₁_mid s₂_mid hSimMid hRest _
      simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hRest ⊢
      rw [← hSimMid.ctx_eq]
      by_cases hRun : s₁_mid.ctx.outcome.isNone = true
      · simp only [hRun, ↓reduceIte] at hRest ⊢
        by_cases hStat : s₁.ctx.isStatic = true
        · simp only [hStat, ↓reduceIte, Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hRest
          rcases hRest with ⟨_, rfl⟩
          exact absurd rfl hNoHalt
        · simp only [hStat, Bool.false_eq_true, ↓reduceIte, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hRest ⊢
          rcases hRest with ⟨_, rfl⟩
          refine ⟨_, ⟨trivial, rfl⟩, ?_⟩
          exact ⟨hSimMid.fork_eq, by simp [hSimMid.ctx_eq],
            (hSimMid.world_sim.warmSlot_preserves s₁.ctx.account slot).setStorage_preserves s₁.ctx.account slot value,
            hSimMid.live_stack_le, hSimMid.phase_eq, hSimMid.sites_eq,
            hSimMid.branches_eq, hSimMid.frames_size_eq⟩
      · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hRest ⊢
        cases hRest
        exact ⟨s₂_mid, rfl, hSimMid⟩

theorem basic_tstore_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {slot value : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.basic (.tstore slot value)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.basic (.tstore slot value)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.basic at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
  rw [← hSim.fork_eq, ← hSim.ctx_eq]
  have hpTail : ∀ {a b : Exec.Machine},
      (do if ← Exec.running then
        if s₁.ctx.isStatic then Exec.halt "WriteInStaticContext" else
          modify fun (s : Exec.Machine) => { s with world := s.world.setTransient s₁.ctx.account slot value }).run a = .ok ((), b) →
      a.ctx.outcome = some .halt → b.ctx.outcome = some .halt := by
    intro a b hRest hH
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
      hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hRest
    cases hRest; exact hH
  by_cases hStatAms : (s₁.fork == .amsterdam && s₁.ctx.isStatic) = true
  · simp only [hStatAms, ↓reduceIte, Exec.halt] at h₁
    rw [stateT_bind_eq, stateT_modify_eq] at h₁
    exact absurd (seq_preserves_halt cost_preserves_halt hpTail h₁ rfl) hNoHalt
  · simp only [hStatAms, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
    refine seq_execSim hSim h₁ hNoHalt hpTail (fun hr hnh => cost_execSim hSim hr hnh) ?_
    intro s₁_mid s₂_mid hSimMid hRest _
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hRest ⊢
    rw [← hSimMid.ctx_eq]
    by_cases hRun : s₁_mid.ctx.outcome.isNone = true
    · simp only [hRun, ↓reduceIte] at hRest ⊢
      by_cases hStat : s₁.ctx.isStatic = true
      · simp only [hStat, ↓reduceIte, Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hRest
        rcases hRest with ⟨_, rfl⟩
        exact absurd rfl hNoHalt
      · simp only [hStat, Bool.false_eq_true, ↓reduceIte, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hRest ⊢
        rcases hRest with ⟨_, rfl⟩
        refine ⟨_, ⟨trivial, rfl⟩, ?_⟩
        exact ⟨hSimMid.fork_eq, hSimMid.ctx_eq, hSimMid.world_sim.setTransient_preserves s₁.ctx.account slot value,
          hSimMid.live_stack_le, hSimMid.phase_eq, hSimMid.sites_eq,
          hSimMid.branches_eq, hSimMid.frames_size_eq⟩
    · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hRest ⊢
      cases hRest
      exact ⟨s₂_mid, rfl, hSimMid⟩

theorem basic_selfbalance_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {addr : Option Address}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.basic (.selfbalance addr)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.basic (.selfbalance addr)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.basic at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
  rw [← hSim.fork_eq, ← hSim.ctx_eq]
  cases addr with
  | none =>
    simp only [stateT_bind_eq, stateT_pure_eq] at h₁ ⊢
    exact cost_execSim hSim h₁ hNoHalt
  | some target =>
    simp only at h₁ ⊢
    by_cases hNe : (Exec.Address.decode target != s₁.ctx.account) = true
    · simp [hNe, Exec.unsupported, unsupported_bind, stateT_throw_eq] at h₁
    · simp only [hNe, Bool.false_eq_true, ↓reduceIte, stateT_bind_eq, stateT_pure_eq] at h₁ ⊢
      exact cost_execSim hSim h₁ hNoHalt

theorem basic_account_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    {k : AccountKind} {addr : Address} {len : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.basic (.account k addr len)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.basic (.account k addr len)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.basic at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
  have hwarm : s₂.world.isAddressWarm (Exec.Address.decode addr) = s₁.world.isAddressWarm (Exec.Address.decode addr) :=
    (hSim.world_sim.warmAddr (Exec.Address.decode addr)).symm
  rw [hwarm, ← hSim.fork_eq]
  have hpTail : ∀ {a b : Exec.Machine},
      (do if ← Exec.running then modify fun (s : Exec.Machine) =>
        { s with world := s.world.warmAddress (Exec.Address.decode addr) }).run a = .ok ((), b) →
      a.ctx.outcome = some .halt → b.ctx.outcome = some .halt := by
    intro a b hRest hH
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
      hH, Option.isNone, Bool.false_eq_true, ↓reduceIte] at hRest
    cases hRest; exact hH
  have hpMid : ∀ {a b : Exec.Machine},
      (do
        if k == AccountKind.extcodecopy then Exec.memory len
        if ← Exec.running then modify fun (s : Exec.Machine) =>
          { s with world := s.world.warmAddress (Exec.Address.decode addr) }).run a = .ok ((), b) →
      a.ctx.outcome = some .halt → b.ctx.outcome = some .halt := by
    intro a b hRest hH
    by_cases hk : (k == AccountKind.extcodecopy) = true
    · simp only [hk, ↓reduceIte] at hRest
      exact seq_preserves_halt memory_preserves_halt hpTail hRest hH
    · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hRest
      exact hpTail hRest hH
  refine seq_execSim hSim h₁ hNoHalt hpMid (fun hr hnh => cost_execSim hSim hr hnh) ?_
  intro s₁_1 s₂_1 hSim1 hRest1 hnh1
  have hWarmStep : ∀ {s₁_m s₂_m : Exec.Machine},
      ExecSim sender s₁_m s₂_m →
      (do if ← Exec.running then modify fun (s : Exec.Machine) =>
        { s with world := s.world.warmAddress (Exec.Address.decode addr) }).run s₁_m = .ok ((), s₁') →
      ∃ s₂', (do if ← Exec.running then modify fun (s : Exec.Machine) =>
        { s with world := s.world.warmAddress (Exec.Address.decode addr) }).run s₂_m = .ok ((), s₂') ∧
        ExecSim sender s₁' s₂' := by
    intro s₁_m s₂_m hSimM hRestM
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hRestM ⊢
    rw [← hSimM.ctx_eq]
    by_cases hRun : s₁_m.ctx.outcome.isNone = true
    · simp only [hRun, ↓reduceIte, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hRestM ⊢
      rcases hRestM with ⟨_, rfl⟩
      refine ⟨_, ⟨trivial, rfl⟩, ?_⟩
      exact ⟨hSimM.fork_eq, hSimM.ctx_eq, hSimM.world_sim.warmAddress_preserves (Exec.Address.decode addr),
        hSimM.live_stack_le, hSimM.phase_eq, hSimM.sites_eq,
        hSimM.branches_eq, hSimM.frames_size_eq⟩
    · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hRestM ⊢
      cases hRestM
      exact ⟨s₂_m, rfl, hSimM⟩
  by_cases hk : (k == AccountKind.extcodecopy) = true
  · simp only [hk, ↓reduceIte] at hRest1 ⊢
    exact seq_execSim hSim1 hRest1 hnh1 hpTail
      (fun hr hnh => memory_execSim hSim1 hr hnh)
      (fun hSim2 hr _ => hWarmStep hSim2 hr)
  · simp only [hk, Bool.false_eq_true, ↓reduceIte] at hRest1 ⊢
    exact hWarmStep hSim1 hRest1

theorem basic_copy_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {k : CopyKind} {len : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.basic (.copy k len)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.basic (.copy k len)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.basic at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
  rw [← hSim.fork_eq, ← hSim.ctx_eq]
  have hpTail : ∀ {a b : Exec.Machine},
      (do if (← Exec.running) && k == CopyKind.returndatacopy && decide (len > s₁.ctx.returnLen) then Exec.halt "OutOfBoundsRead").run a = .ok ((), b) →
      a.ctx.outcome = some .halt → b.ctx.outcome = some .halt := by
    intro a b hRest hH
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
      hH, Option.isNone, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hRest
    cases hRest; exact hH
  refine seq_execSim hSim h₁ hNoHalt (seq_preserves_halt memory_preserves_halt hpTail)
    (fun hr hnh => cost_execSim hSim hr hnh) ?_
  intro s₁_1 s₂_1 hSim1 hRest1 hnh1
  refine seq_execSim hSim1 hRest1 hnh1 hpTail
    (fun hr hnh => memory_execSim hSim1 hr hnh) ?_
  intro s₁_2 s₂_2 hSim2 hRest2 _
  simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hRest2 ⊢
  rw [← hSim2.ctx_eq]
  by_cases hCond : (s₁_2.ctx.outcome.isNone && k == CopyKind.returndatacopy && decide (len > s₁.ctx.returnLen)) = true
  · simp only [hCond, ↓reduceIte, Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hRest2
    rcases hRest2 with ⟨_, rfl⟩
    exact absurd rfl hNoHalt
  · simp only [hCond, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hRest2 ⊢
    cases hRest2
    exact ⟨s₂_2, rfl, hSim2⟩

theorem basic_keccak_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {len : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.basic (.keccak len)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.basic (.keccak len)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.basic at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
  rw [← hSim.fork_eq]
  exact seq_execSim hSim h₁ hNoHalt memory_preserves_halt
    (fun hr hnh => cost_execSim hSim hr hnh)
    (fun hSimMid hr hnh => memory_execSim hSimMid hr hnh)

theorem basic_log_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {topics len : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.basic (.log topics len)).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.basic (.log topics len)).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  unfold Exec.basic at h₁ ⊢
  simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
  rw [← hSim.fork_eq, ← hSim.ctx_eq]
  split at h₁
  · rename_i hlt
    simp only [hlt, ↓reduceDIte]
    have hpTail1 : ∀ {a b : Exec.Machine},
        (do
          if (← Exec.running) && s₁.ctx.isStatic then Exec.halt "WriteInStaticContext"
          if ← Exec.running then modify fun (s : Exec.Machine) =>
            { s with ctx.committed.logs := s.ctx.committed.logs ++ ([⟨Exec.Address.encode s₁.ctx.account, topics, len⟩] : List CommittedLog) }).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt := by
      intro a b hRest hH
      simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
        hH, Option.isNone, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hRest
      cases hRest; exact hH
    refine seq_execSim hSim h₁ hNoHalt (seq_preserves_halt memory_preserves_halt hpTail1)
      (fun hr hnh => cost_execSim hSim hr hnh) ?_
    intro s₁_1 s₂_1 hSim1 hRest1 hnh1
    refine seq_execSim hSim1 hRest1 hnh1 hpTail1
      (fun hr hnh => memory_execSim hSim1 hr hnh) ?_
    intro s₁_2 s₂_2 hSim2 hRest2 _
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hRest2 ⊢
    rw [← hSim2.ctx_eq]
    cases hRun : s₁_2.ctx.outcome.isNone with
    | false =>
      simp only [hRun, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        stateT_bind_eq, stateT_get_eq, stateT_pure_eq, ← hSim2.ctx_eq] at hRest2 ⊢
      cases hRest2
      exact ⟨s₂_2, rfl, hSim2⟩
    | true =>
      simp only [hRun, Bool.true_and, ↓reduceIte] at hRest2 ⊢
      by_cases hStat : s₁.ctx.isStatic = true
      · simp only [hStat, ↓reduceIte, Exec.halt, stateT_bind_eq, stateT_modify_eq,
          stateT_get_eq, stateT_pure_eq, Option.isNone, Bool.false_eq_true,
          Except.ok.injEq, Prod.mk.injEq] at hRest2
        rcases hRest2 with ⟨_, rfl⟩
        exact absurd rfl hNoHalt
      · simp only [hStat, Bool.false_eq_true, ↓reduceIte, stateT_bind_eq,
          stateT_get_eq, stateT_pure_eq, ← hSim2.ctx_eq, hRun,
          stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hRest2 ⊢
        rcases hRest2 with ⟨_, rfl⟩
        refine ⟨_, ⟨trivial, rfl⟩, ?_⟩
        exact ⟨hSim2.fork_eq, by simp [hSim2.ctx_eq], hSim2.world_sim,
          hSim2.live_stack_le, hSim2.phase_eq, hSim2.sites_eq,
          hSim2.branches_eq, hSim2.frames_size_eq⟩
  · simp [Exec.unsupported, stateT_throw_eq] at h₁

theorem basic_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {e : Effect}
    (hSim : ExecSim sender s₁ s₂)
    (hNone : s₁.ctx.outcome = none)
    (hNoGas : (match e with | .ifGas .. | .gasRead .. => false | _ => true) = true)
    (hSenderSafe : senderSafeNode s₁.fork sender s₁.ctx.account e = true)
    (h₁ : (Exec.basic e).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt)
    (hNoRev : s₁'.ctx.outcome ≠ some .revert) :
    ∃ s₂', (Exec.basic e).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  cases e with
  | work n _ =>
    unfold Exec.basic at h₁ ⊢
    simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
    exact cost_execSim hSim h₁ hNoHalt
  | native addr input failure output =>
    exact basic_native_execSim hSim h₁ hNoHalt
  | gasGuard k =>
    exact basic_gasGuard_execSim hSim hNone h₁ hNoHalt hNoRev
  | gasRead _ _ =>
    simp at hNoGas
  | fault error =>
    unfold Exec.basic Exec.halt at h₁
    simp only [stateT_run_eq, stateT_get_bind, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
    rcases h₁ with ⟨_, rfl⟩
    exact absurd rfl hNoHalt
  | returndataCopy offset len =>
    exact basic_returndataCopy_execSim hSim h₁ hNoHalt
  | mem n _ =>
    unfold Exec.basic at h₁ ⊢
    simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
    exact memory_execSim hSim h₁ hNoHalt
  | sload slot =>
    exact basic_sload_execSim hSim h₁ hNoHalt
  | sstore slot value =>
    exact basic_sstore_execSim hSim h₁ hNoHalt
  | tload _ =>
    unfold Exec.basic at h₁ ⊢
    simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
    rw [← hSim.fork_eq]
    exact cost_execSim hSim h₁ hNoHalt
  | tstore slot value =>
    exact basic_tstore_execSim hSim h₁ hNoHalt
  | selfbalance addr =>
    exact basic_selfbalance_execSim hSim h₁ hNoHalt
  | account k addr len =>
    exact basic_account_execSim hSim h₁ hNoHalt
  | copy k len =>
    exact basic_copy_execSim hSim h₁ hNoHalt
  | keccak len =>
    exact basic_keccak_execSim hSim h₁ hNoHalt
  | log topics len =>
    exact basic_log_execSim hSim h₁ hNoHalt
  | selfdestruct addr =>
    unfold Exec.basic at h₁ ⊢
    simp only [stateT_run_eq, stateT_get_bind] at h₁ ⊢
    simp only [senderSafeNode, bne_iff_ne, ne_eq] at hSenderSafe
    exact selfdestruct_execSim hSim hSenderSafe h₁ hNoHalt
  | call =>
    unfold Exec.basic at h₁
    simp [Exec.unsupported, stateT_run_eq, stateT_get_bind, stateT_throw_eq] at h₁
  | create =>
    unfold Exec.basic at h₁
    simp [Exec.unsupported, stateT_run_eq, stateT_get_bind, stateT_throw_eq] at h₁
  | precompile =>
    unfold Exec.basic at h₁
    simp [Exec.unsupported, stateT_run_eq, stateT_get_bind, stateT_throw_eq] at h₁
  | ifGas =>
    unfold Exec.basic at h₁
    simp [Exec.unsupported, stateT_run_eq, stateT_get_bind, stateT_throw_eq] at h₁

end EvmGasSemantics.Spec
