import EvmGasSemantics.Theorems.Spec.Monotone
import EvmGasSemantics.Theorems.Meter
import EvmGasSemantics.Theorems.Spec.SimWorld
import EvmGasSemantics.Theorems.Spec.SimBasicStep

set_option autoImplicit false
namespace EvmGasSemantics.Spec

open EvmGasSemantics

/-- The transfer-domain guard of `checkTransfer`. -/
def checkTransferGuard (w : State) (src dst amount : Nat) : Bool :=
  (src != dst && amount != 0) &&
    ((w.getAccount src).balance < amount || (w.getAccount dst).balance + amount ≥ 2^256)

theorem checkTransfer_run (src dst amount : Nat) (s : Exec.Machine) :
    Exec.checkTransfer src dst amount s =
      if checkTransferGuard s.world src dst amount then
        .error (.unsupported "value transfer outside the U256 balance domain")
      else .ok ((), s) := by
  unfold Exec.checkTransfer checkTransferGuard
  simp only [Exec.unsupported, stateT_bind_eq, stateT_get_eq]
  by_cases h₁ : (src != dst && amount != 0) = true
  · by_cases h₂ : ((s.world.getAccount src).balance < amount ||
      (s.world.getAccount dst).balance + amount ≥ 2^256) = true
    · simp only [h₁, h₂, Bool.and_self, ↓reduceIte]; rfl
    · have h₂' : ((s.world.getAccount src).balance < amount ||
          (s.world.getAccount dst).balance + amount ≥ 2^256) = false := by simpa using h₂
      simp only [h₁, h₂', Bool.and_false, ↓reduceIte, Bool.false_eq_true]; rfl
  · have h₁' : (src != dst && amount != 0) = false := by simpa using h₁
    simp only [h₁', Bool.false_and, ↓reduceIte, Bool.false_eq_true]; rfl

theorem WorldSim.checkTransferGuard_eq {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (src dst amount : Nat)
    (hsafe : amount = 0 ∨ (src ≠ sender ∧ dst ≠ sender)) :
    checkTransferGuard w₁ src dst amount = checkTransferGuard w₂ src dst amount := by
  unfold checkTransferGuard
  rcases hsafe with h0 | ⟨hs, hd⟩
  · subst h0; simp
  · rw [h.getAccount_ne hs, h.getAccount_ne hd]

/-! ### Meter-stack CALL/CREATE lemmas -/

/-- CALL forwarding with a nonwrapping operand. The operand is evaluated at the pre-charge gas
`G`, the grant is capped at the post-charge gas `G'`. Side 2 has at least as much gas both before
and after, and loses no more to the charges. A checked operand passed its guard on side 1. -/
theorem call_grant_and_retained_monotone (arg : GasArg)
    {G₁ G₂ G₁' G₂' : Nat} (hNoWrap : NoWrappingGasArg arg = true)
    (hG : G₁ ≤ G₂) (hG' : G₁' ≤ G₂') (hle₁ : G₁' ≤ G₁) (hle₂ : G₂' ≤ G₂)
    (hdrop : G₂ - G₂' ≤ G₁ - G₁')
    (hguard : ∀ k, arg = .gasMinusChecked k → k ≤ G₁) :
    min (Exec.gasArg arg G₁) (allButOne64th G₁') ≤ min (Exec.gasArg arg G₂) (allButOne64th G₂') ∧
      G₁' - min (Exec.gasArg arg G₁) (allButOne64th G₁') ≤
        G₂' - min (Exec.gasArg arg G₂) (allButOne64th G₂') := by
  cases arg with
  | gasMinus k => simp [NoWrappingGasArg] at hNoWrap
  | const n => simp only [Exec.gasArg]; unfold allButOne64th; omega
  | all => simp only [Exec.gasArg]; unfold allButOne64th; omega
  | gasMinusChecked k =>
    have hk := hguard k rfl
    simp only [Exec.gasArg]; unfold allButOne64th; omega

private theorem LiveStackLE.budget' {x y : Int} {as bs : List Meter}
    (h : LiveStackLE x y as bs) : x ≤ y := by
  cases h <;> assumption

private theorem LiveStackLE.shift' {x y dx dy : Int} {as bs : List Meter}
    (h : LiveStackLE x y as bs) (hd : dx ≤ dy) :
    LiveStackLE (x + dx) (y + dy) as bs := by
  induction h with
  | nil hb => exact .nil (by omega)
  | @cons x y a b as bs hb hg hr hs hc ht ih =>
    apply LiveStackLE.cons (by omega) hg hr hs hc
    have e₁ : x + dx + ↑a.gasLeft + ↑a.stateSpilled = x + ↑a.gasLeft + ↑a.stateSpilled + dx := by
      omega
    have e₂ : y + dy + ↑b.gasLeft + ↑b.stateSpilled = y + ↑b.gasLeft + ↑b.stateSpilled + dy := by
      omega
    rw [e₁, e₂]; exact ih

/-- Preflight abort (depth, balance) returns the whole child grant to the parent. -/
theorem liveStackLE_abortChild_meters {a b pa pb : Meter} {as bs : List Meter}
    (h : LiveStackLE 0 0 (a :: pa :: as) (b :: pb :: bs)) :
    LiveStackLE 0 0 (pa.restoreChildGas a.gasLeft a.stateLeft :: as)
      (pb.restoreChildGas b.gasLeft b.stateLeft :: bs) := by
  cases h with
  | cons hxy hg hr hs hc ht =>
    cases ht with
    | cons hxy' hpg hpr hps hpc htt =>
      refine .cons (by omega) (by simp only [Meter.restoreChildGas]; omega)
        (by simp only [Meter.restoreChildGas]; omega) hps hpc ?_
      have := htt.shift' (dx := -(a.stateSpilled : Int)) (dy := -(b.stateSpilled : Int))
        (by omega)
      simp only [Meter.restoreChildGas]
      have e₁ : (0 : Int) + ↑(pa.gasLeft + a.gasLeft) + ↑pa.stateSpilled =
          0 + ↑a.gasLeft + ↑a.stateSpilled + ↑pa.gasLeft + ↑pa.stateSpilled +
            -(a.stateSpilled : Int) := by omega
      have e₂ : (0 : Int) + ↑(pb.gasLeft + b.gasLeft) + ↑pb.stateSpilled =
          0 + ↑b.gasLeft + ↑b.stateSpilled + ↑pb.gasLeft + ↑pb.stateSpilled +
            -(b.stateSpilled : Int) := by omega
      rw [e₁, e₂]; exact this

theorem liveStackLE_abortChild {a b a' : MeterStack.State}
    (h : LiveStackLE 0 0 (a.top.meter :: a.parents.map (·.meter))
      (b.top.meter :: b.parents.map (·.meter)))
    (ha : MeterStack.apply .abortChild a = .ok a') :
    ∃ b', MeterStack.apply .abortChild b = .ok b' ∧
      LiveStackLE 0 0 (a'.top.meter :: a'.parents.map (·.meter))
        (b'.top.meter :: b'.parents.map (·.meter)) := by
  cases hap : a.parents with
  | nil =>
    simp only [MeterStack.apply, hap] at ha
    cases ha
  | cons p ps =>
    cases hbp : b.parents with
    | nil =>
      rw [hap, hbp] at h
      cases h with
      | cons _ _ _ _ _ ht => cases ht
    | cons q qs =>
      rw [hap, hbp] at h
      simp only [List.map_cons] at h
      simp only [MeterStack.apply, hap, pure, Except.pure, Except.ok.injEq] at ha
      subst ha
      refine ⟨_, by simp only [MeterStack.apply, hbp]; rfl, ?_⟩
      exact liveStackLE_abortChild_meters h

/-- The state transformer applied by `Exec.resume` before its failure refill. -/
def resumeUpdate (parent : Exec.Context) (saved : State.Snapshot) (result : FrameResult)
    (outputLen : Nat) (isCreate : Bool) (s : Exec.Machine) : Exec.Machine :=
  { s with
    world := s.world.finishFrame saved (result.outcome == .success)
    ctx := { parent with
      pendingDeletion := if result.outcome == .success then
        parent.pendingDeletion ++ s.ctx.pendingDeletion else parent.pendingDeletion
      committed := if result.outcome == .success then
        parent.committed.merge result.committed else parent.committed
      returnLen := if isCreate && result.outcome == .success then 0 else outputLen } }

theorem resume_run (parent : Exec.Context) (saved : State.Snapshot) (refill : Nat)
    (result : FrameResult) (outputLen : Nat) (isCreate : Bool) (s : Exec.Machine) :
    Exec.resume parent saved refill result outputLen isCreate s =
      if result.outcome != .success then
        Exec.cost { stateRefill := refill } (resumeUpdate parent saved result outputLen isCreate s)
      else .ok ((), resumeUpdate parent saved result outputLen isCreate s) := by
  unfold Exec.resume
  rw [stateT_bind_eq]
  change (if result.outcome != .success then Exec.cost { stateRefill := refill } else pure ())
    (resumeUpdate parent saved result outputLen isCreate s) = _
  split <;> rfl

/-- `resume` after a successful child on both sides: the world relation carries over and the
contexts agree when the parent contexts, child contexts and committed results agree. -/
theorem resumeUpdate_success_sim {sender : Nat} {s₁ s₂ : Exec.Machine}
    (parent : Exec.Context) (saved₁ saved₂ : State.Snapshot) (r₁ r₂ : FrameResult)
    (outputLen : Nat) (isCreate : Bool)
    (hw : WorldSim sender s₁.world s₂.world) (hctx : s₁.ctx = s₂.ctx)
    (hr₁ : r₁.outcome = .success) (hr₂ : r₂.outcome = .success)
    (hcomm : r₁.committed = r₂.committed) :
    WorldSim sender (resumeUpdate parent saved₁ r₁ outputLen isCreate s₁).world
        (resumeUpdate parent saved₂ r₂ outputLen isCreate s₂).world ∧
      (resumeUpdate parent saved₁ r₁ outputLen isCreate s₁).ctx =
        (resumeUpdate parent saved₂ r₂ outputLen isCreate s₂).ctx ∧
      (resumeUpdate parent saved₁ r₁ outputLen isCreate s₁).meters = s₁.meters ∧
      (resumeUpdate parent saved₂ r₂ outputLen isCreate s₂).meters = s₂.meters := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp only [resumeUpdate, hr₁, hr₂]
    exact hw.finishFrame_success_preserves saved₁ saved₂
  · simp only [resumeUpdate, hr₁, hr₂, hcomm, hctx]

/-- `resume` after a failed child on both sides: rollback to related entry worlds. -/
theorem resumeUpdate_failure_sim {sender : Nat} {s₁ s₂ : Exec.Machine} {p₁ p₂ : State}
    (parent : Exec.Context) (r₁ r₂ : FrameResult) (outputLen : Nat) (isCreate : Bool)
    (hw : WorldSim sender s₁.world s₂.world) (hp : WorldSim sender p₁ p₂)
    (hpre₁ : p₁.pre = s₁.world.pre) (hpre₂ : p₂.pre = s₂.world.pre)
    (hr₁ : r₁.outcome ≠ .success) (hr₂ : r₂.outcome ≠ .success) :
    WorldSim sender (resumeUpdate parent p₁.snapshot r₁ outputLen isCreate s₁).world
        (resumeUpdate parent p₂.snapshot r₂ outputLen isCreate s₂).world ∧
      (resumeUpdate parent p₁.snapshot r₁ outputLen isCreate s₁).ctx =
        (resumeUpdate parent p₂.snapshot r₂ outputLen isCreate s₂).ctx := by
  have e₁ : (r₁.outcome == .success) = false := by simpa using hr₁
  have e₂ : (r₂.outcome == .success) = false := by simpa using hr₂
  simp only [resumeUpdate, e₁, e₂, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  exact ⟨hw.rollback_preserves hp hpre₁ hpre₂, trivial⟩

theorem gasArg_mono_of_noWrapping (arg : GasArg) {g₁ g₂ : Nat}
    (hNoWrap : NoWrappingGasArg arg = true) (hOrder : g₁ ≤ g₂) :
    Exec.gasArg arg g₁ ≤ Exec.gasArg arg g₂ := by
  cases arg <;> simp [Exec.gasArg, NoWrappingGasArg] at hNoWrap ⊢ <;> omega

theorem spawnCall_meterLE {s₁ s₂ s₁' : MeterStack.State} {req₁ req₂ stip : Nat}
    (hLE : MeterLE s₁.top.meter s₂.top.meter)
    (hReq : req₁ ≤ req₂)
    (h₁ : MeterStack.apply (.spawnCall req₁ stip) s₁ = .ok s₁') :
    ∃ s₂', MeterStack.apply (.spawnCall req₂ stip) s₂ = .ok s₂' ∧
      MeterLE s₁'.top.meter s₂'.top.meter := by
  obtain ⟨hg, hr, hs, hf⟩ := hLE
  have h64 : allButOne64th s₁.top.meter.gasLeft ≤ allButOne64th s₂.top.meter.gasLeft :=
    allButOne64th_mono hg
  have hw₁ : min req₁ (allButOne64th s₁.top.meter.gasLeft) ≤ s₁.top.meter.gasLeft :=
    Nat.le_trans (Nat.min_le_right _ _) (allButOne64th_le _)
  have hw₂ : min req₂ (allButOne64th s₂.top.meter.gasLeft) ≤ s₂.top.meter.gasLeft :=
    Nat.le_trans (Nat.min_le_right _ _) (allButOne64th_le _)
  simp only [MeterStack.apply, Meter.charge, hw₁, hw₂, ↓reduceIte,
    bind, Except.bind, pure, Except.pure,
    MeterStack.push, Meter.drainReservoir, Except.ok.injEq] at h₁ ⊢
  subst h₁
  refine ⟨_, rfl, ?_⟩
  constructor <;> simp [Meter.fresh] <;> omega

theorem spawnCreate_meterLE {s₁ s₂ s₁' : MeterStack.State}
    (hLE : MeterLE s₁.top.meter s₂.top.meter)
    (h₁ : MeterStack.apply .spawnCreate s₁ = .ok s₁') :
    ∃ s₂', MeterStack.apply .spawnCreate s₂ = .ok s₂' ∧
      MeterLE s₁'.top.meter s₂'.top.meter := by
  obtain ⟨hg, hr, hs, hf⟩ := hLE
  have h64 : allButOne64th s₁.top.meter.gasLeft ≤ allButOne64th s₂.top.meter.gasLeft :=
    allButOne64th_mono hg
  simp only [MeterStack.apply, MeterStack.push, Meter.withholdChildGas,
    Meter.drainReservoir, pure, Except.pure, Except.ok.injEq] at h₁ ⊢
  subst h₁
  refine ⟨_, rfl, ?_⟩
  constructor <;> simp [Meter.fresh] <;> omega

theorem incorporateChild_success_meterLE {p₁ p₂ c₁ c₂ p₁' : Meter}
    (hp : MeterLE p₁ p₂) (hc : MeterLE c₁ c₂)
    (hComm : c₂.stateCommittedSpill = c₁.stateCommittedSpill)
    (h₁ : Meter.incorporateChild p₁ c₁ true = .ok p₁') :
    ∃ p₂', Meter.incorporateChild p₂ c₂ true = .ok p₂' ∧ MeterLE p₁' p₂' := by
  obtain ⟨hpg, hpr, hps, hpf⟩ := hp
  obtain ⟨hcg, hcr, hcs, hcf⟩ := hc
  obtain ⟨hcSpill₁, _, rfl⟩ := incorporateChild_ok h₁
  have hcSpill₂ : c₂.stateCommittedSpill = 0 := hComm.trans hcSpill₁
  unfold Meter.incorporateChild
  simp only [hcSpill₂, ↓reduceIte]
  refine ⟨_, rfl, ?_⟩
  constructor <;> simp [Meter.repayStateSpill] <;> omega

theorem returnSuccess_meterLE {s₁ s₂ s₁' : MeterStack.State}
    {p₁ p₂ : MeterStack.Frame} {ps₁ ps₂ : List MeterStack.Frame}
    (hParents₁ : s₁.parents = p₁ :: ps₁)
    (hParents₂ : s₂.parents = p₂ :: ps₂)
    (hPhase₁ : s₁.phase = .running)
    (hPhase₂ : s₂.phase = .running)
    (hp : MeterLE p₁.meter p₂.meter)
    (hc : MeterLE s₁.top.meter s₂.top.meter)
    (hComm : s₂.top.meter.stateCommittedSpill = s₁.top.meter.stateCommittedSpill)
    (h₁ : MeterStack.apply .returnSuccess s₁ = .ok s₁') :
    ∃ s₂', MeterStack.apply .returnSuccess s₂ = .ok s₂' ∧
      MeterLE s₁'.top.meter s₂'.top.meter := by
  unfold MeterStack.apply MeterStack.finish at h₁ ⊢
  rw [hPhase₁, hParents₁] at h₁
  rw [hPhase₂, hParents₂]
  simp only [bind, Except.bind, pure, Except.pure] at h₁ ⊢
  split at h₁ <;> try contradiction
  rename_i p₁' hm₁
  simp only [Except.ok.injEq] at h₁
  subst h₁
  obtain ⟨p₂', hm₂, hle⟩ := incorporateChild_success_meterLE hp hc hComm hm₁
  rw [hm₂]
  exact ⟨_, rfl, hle⟩

theorem enterFrame_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine} {entry₁ : Nat × Nat × Nat}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : Exec.enterFrame.run s₁ = .ok (entry₁, s₁')) :
    ∃ entry₂ s₂', Exec.enterFrame.run s₂ = .ok (entry₂, s₂') ∧
      ExecSim sender s₁' s₂' ∧
      entry₁ = (s₁.frames.size, s₁.meters.top.meter.gasLeft, s₁.meters.top.entryReservoir) ∧
      entry₂ = (s₂.frames.size, s₂.meters.top.meter.gasLeft, s₂.meters.top.entryReservoir) ∧
      entry₁.1 = entry₂.1 := by
  unfold Exec.enterFrame at h₁ ⊢
  simp only [stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_set_eq,
    stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at h₁ ⊢
  rcases h₁ with ⟨hEntry₁, rfl⟩
  refine ⟨(s₂.frames.size, s₂.meters.top.meter.gasLeft, s₂.meters.top.entryReservoir),
    { s₂ with frames := s₂.frames.push none }, ⟨rfl, rfl⟩, ?_, hEntry₁.symm, rfl, ?_⟩
  · exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_sim, hSim.live_stack_le,
      hSim.phase_eq, hSim.sites_eq, hSim.branches_eq, by simp [hSim.frames_size_eq]⟩
  · rw [← hEntry₁, hSim.frames_size_eq]

private theorem chain_good' {f : MeterStack.Frame} {ps : List MeterStack.Frame}
    (h : MeterStack.Chain f ps) : MeterStack.FrameGood f := by
  cases ps with
  | nil => exact h
  | cons _ _ => exact h.1

theorem finishFrame_outcome {entry : Nat × Nat × Nat} {cs : Option CodeStart} {entered : Bool}
    {s s' : Exec.Machine} {r : FrameResult}
    (h : (Exec.finishFrame entry cs entered).run s = .ok (r, s')) :
    s.ctx.outcome.getD .success = r.outcome ∧
      s'.frames = s.frames.set! entry.1 (some r) := by
  unfold Exec.finishFrame at h
  simp only [stateT_run_eq, stateT_bind_eq, stateT_get_eq] at h
  cases hOut : s.ctx.outcome.getD Outcome.success
  · simp only [hOut, beq_self_eq_true, ↓reduceIte,
      show (Outcome.success == Outcome.halt) = false from rfl,
      Bool.false_eq_true, stateT_pure_eq, stateT_bind_eq, ofExcept_eq] at h
    cases hSt : s.meters.top.meter.stateGasUsed entry.2.2 with
    | error _ => simp [hSt, Except.mapError, Except.map] at h
    | ok used =>
      simp only [hSt, Except.mapError, Except.map, stateT_bind_eq] at h
      cases hFin : (s.meters.phase == .finished)
      · simp only [hFin, Bool.false_eq_true, ↓reduceIte, stateT_bind_eq, ofExcept_eq] at h
        cases hM : MeterStack.apply .returnSuccess s.meters with
        | error _ => simp [hM, Except.mapError, Except.map] at h
        | ok meters =>
          simp only [hM, Except.mapError, Except.map, stateT_bind_eq, stateT_set_eq, stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
      · simp only [hFin, ↓reduceIte, stateT_pure_eq, stateT_bind_eq, stateT_set_eq, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩
  · simp only [hOut, beq_self_eq_true, ↓reduceIte,
      show (Outcome.revert == Outcome.halt) = false from rfl,
      show (Outcome.revert == Outcome.success) = false from rfl,
      Bool.false_eq_true, stateT_pure_eq, stateT_bind_eq, ofExcept_eq] at h
    cases hSt : s.meters.top.meter.restoreState.stateGasUsed entry.2.2 with
    | error _ => simp [hSt, Except.mapError, Except.map] at h
    | ok used =>
      simp only [hSt, Except.mapError, Except.map, stateT_bind_eq] at h
      cases hFin : (s.meters.phase == .finished)
      · simp only [hFin, Bool.false_eq_true, ↓reduceIte, stateT_bind_eq, ofExcept_eq] at h
        cases hM : MeterStack.apply .returnRevert s.meters with
        | error _ => simp [hM, Except.mapError, Except.map] at h
        | ok meters =>
          simp only [hM, Except.mapError, Except.map, stateT_bind_eq, stateT_set_eq, stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩
      · simp only [hFin, ↓reduceIte, stateT_pure_eq, stateT_bind_eq, stateT_set_eq, Except.ok.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl⟩
  · simp only [hOut, beq_self_eq_true, ↓reduceIte,
      show (Outcome.halt == Outcome.success) = false from rfl,
      Bool.false_eq_true, stateT_pure_eq, stateT_bind_eq, ofExcept_eq] at h
    cases hForf : s.meters.top.meter.restoreState.forfeit with
    | error _ => simp [hForf, Except.mapError, Except.map] at h
    | ok m =>
      simp only [hForf, Except.mapError, Except.map, stateT_bind_eq, ofExcept_eq] at h
      cases hSt : m.stateGasUsed entry.2.2 with
      | error _ => simp [hSt, Except.mapError, Except.map] at h
      | ok used =>
        simp only [hSt, Except.mapError, Except.map, stateT_bind_eq] at h
        cases hFin : (s.meters.phase == .finished)
        · simp only [hFin, Bool.false_eq_true, ↓reduceIte, stateT_bind_eq, ofExcept_eq] at h
          cases hM : MeterStack.apply .returnHalt s.meters with
          | error _ => simp [hM, Except.mapError, Except.map] at h
          | ok meters =>
            simp only [hM, Except.mapError, Except.map, stateT_bind_eq, stateT_set_eq, stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            exact ⟨rfl, rfl⟩
        · simp only [hFin, ↓reduceIte, stateT_pure_eq, stateT_bind_eq, stateT_set_eq, Except.ok.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl⟩

theorem finishFrame_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    {entry₁ entry₂ : Nat × Nat × Nat} {cs₁ cs₂ : Option CodeStart} {entered : Bool}
    {r₁ : FrameResult}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.finishFrame entry₁ cs₁ entered).run s₁ = .ok (r₁, s₁'))
    (hSucc : r₁.outcome = .success)
    (hRes₂ : entry₂.2.2 = s₂.meters.top.entryReservoir) :
    ∃ r₂ s₂', (Exec.finishFrame entry₂ cs₂ entered).run s₂ = .ok (r₂, s₂') ∧
      ExecSim sender s₁' s₂' ∧
      r₂.outcome = .success ∧
      r₂.committed = r₁.committed ∧
      r₂.gasExit = s₂.meters.top.meter.gasLeft ∧
      r₂.reservoirExit = s₂.meters.top.meter.stateLeft ∧
      r₂.executionGasUsed = entry₂.2.1 - s₂.meters.top.meter.gasLeft -
        s₂.meters.top.meter.stateSpilled - s₂.meters.top.meter.stateCommittedSpill ∧
      r₂.stateGasUsed = s₂.meters.top.meter.stateUsed entry₂.2.2 ∧
      r₂.refund = s₂.meters.top.meter.refund := by
  have hOut₁ : s₁.ctx.outcome.getD .success = .success := (finishFrame_outcome h₁).1.trans hSucc
  have hOut₂ : s₂.ctx.outcome.getD .success = .success := by rw [← hSim.ctx_eq]; exact hOut₁
  unfold Exec.finishFrame at h₁ ⊢
  simp only [stateT_run_eq, stateT_bind_eq, stateT_get_eq,
    hOut₁, hOut₂, beq_self_eq_true, ↓reduceIte,
    show (Outcome.success == Outcome.halt) = false from rfl, Bool.false_eq_true,
    stateT_pure_eq, ofExcept_eq] at h₁ ⊢
  cases h_st₁ : s₁.meters.top.meter.stateGasUsed entry₁.2.2 with
  | error e => simp [h_st₁, Except.mapError, Except.map] at h₁
  | ok used₁ =>
    have hBase₂ : s₂.meters.top.meter.stateBaseline ≤ entry₂.2.2 := by
      rw [hRes₂]
      exact (chain_good' hSim.phase_eq.chain₂).baseline
    have h_st₂ : s₂.meters.top.meter.stateGasUsed entry₂.2.2 =
        .ok (s₂.meters.top.meter.stateUsed entry₂.2.2) := by
      simp [Meter.stateGasUsed, Meter.stateUsed, hBase₂]
    simp only [h_st₁, h_st₂, Except.mapError, Except.map, stateT_bind_eq] at h₁ ⊢
    have hWrites : (s₂.ctx.committed.storage.filterMap fun w =>
        let address := Exec.Address.decode w.address
        if address ∈ s₂.ctx.pendingDeletion || !(s₂.world.frame.storage.any fun (key, _) => key == (address, w.slot)) then none
        else some { w with value := s₂.world.getStorage address w.slot }) =
      (s₁.ctx.committed.storage.filterMap fun w =>
        let address := Exec.Address.decode w.address
        if address ∈ s₁.ctx.pendingDeletion || !(s₁.world.frame.storage.any fun (key, _) => key == (address, w.slot)) then none
        else some { w with value := s₁.world.getStorage address w.slot }) := by
      rw [← hSim.ctx_eq, ← hSim.world_sim.frame_storage]
      congr 1; funext w
      dsimp only
      rw [hSim.world_sim.storage]
    rw [← hSim.phase_eq.phase_eq]
    by_cases hFin : (s₁.meters.phase == .finished) = true
    · simp only [hFin, ↓reduceIte, stateT_pure_eq, stateT_bind_eq, stateT_set_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
      simp only [hFin, ↓reduceIte, stateT_pure_eq, stateT_bind_eq, stateT_set_eq]
      rcases h₁ with ⟨rfl, rfl⟩
      refine ⟨_, _, rfl, ?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_sim, hSim.live_stack_le,
          hSim.phase_eq, hSim.sites_eq, hSim.branches_eq, by simp [hSim.frames_size_eq]⟩
      · simp [hWrites, hSim.ctx_eq]
    · simp only [hFin, Bool.false_eq_true, ↓reduceIte, stateT_bind_eq, ofExcept_eq] at h₁ ⊢
      cases hm₁ : MeterStack.apply .returnSuccess s₁.meters with
      | error e => simp [hm₁, Except.mapError, Except.map] at h₁
      | ok meters₁ =>
        simp only [hm₁, Except.mapError, Except.map, stateT_bind_eq, stateT_set_eq, stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
        rcases h₁ with ⟨rfl, rfl⟩
        obtain ⟨meters₂, hm₂, hLive', hPhase'⟩ := hSim.phase_eq.returnSuccess hSim.live_stack_le hm₁
        simp only [hm₂, Except.mapError, Except.map, stateT_bind_eq, stateT_set_eq, stateT_pure_eq]
        refine ⟨_, _, rfl, ?_, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
        · exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_sim, hLive',
            hPhase', hSim.sites_eq, hSim.branches_eq, by simp [hSim.frames_size_eq]⟩
        · simp [hWrites, hSim.ctx_eq]

theorem resume_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    {parent : Exec.Context} {saved₁ saved₂ : State.Snapshot} {refill : Nat}
    {r₁ r₂ : FrameResult} {outputLen : Nat} {isCreate : Bool}
    (hSim : ExecSim sender s₁ s₂)
    (hr₁ : r₁.outcome = .success) (hr₂ : r₂.outcome = .success)
    (hcomm : r₁.committed = r₂.committed)
    (h₁ : (Exec.resume parent saved₁ refill r₁ outputLen isCreate).run s₁ = .ok ((), s₁')) :
    ∃ s₂', (Exec.resume parent saved₂ refill r₂ outputLen isCreate).run s₂ = .ok ((), s₂') ∧
      ExecSim sender s₁' s₂' := by
  simp only [stateT_run_eq, resume_run, hr₁, hr₂, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at h₁ ⊢
  rcases h₁ with ⟨_, rfl⟩
  obtain ⟨hw, hctx, hm₁, hm₂⟩ :=
    resumeUpdate_success_sim parent saved₁ saved₂ r₁ r₂ outputLen isCreate
      hSim.world_sim hSim.ctx_eq hr₁ hr₂ hcomm
  refine ⟨_, ⟨trivial, rfl⟩, ?_⟩
  refine ⟨by simp [resumeUpdate, hSim.fork_eq], hctx, hw, ?_, ?_,
    by simp [resumeUpdate, hSim.sites_eq],
    by simp [resumeUpdate, hSim.branches_eq],
    by simp [resumeUpdate, hSim.frames_size_eq]⟩
  · rw [hm₁, hm₂]; exact hSim.live_stack_le
  · rw [hm₁, hm₂]; exact hSim.phase_eq

theorem afterChild_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    {id : Nat} {success : Bool} {onFail : OnFail} {after : After}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.afterChild id success onFail after).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt)
    (hNoRev : s₁'.ctx.outcome ≠ some .revert) :
    ∃ s₂', (Exec.afterChild id success onFail after).run s₂ = .ok ((), s₂') ∧
      ExecSim sender s₁' s₂' := by
  unfold Exec.afterChild at h₁ ⊢
  simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte] at h₁ ⊢
    have hpTail : ∀ {a b : Exec.Machine},
        (do if (← Exec.running) && !success && onFail == OnFail.bubble then
          modify fun (s : Exec.Machine) => { s with frames := s.frames.map fun r => Option.map (fun (r : FrameResult) =>
            if r.id == id then { r with caught := some false } else r) r }
          Exec.terminate (.revert 0)).run a = .ok ((), b) →
        a.ctx.outcome = some .halt → b.ctx.outcome = some .halt := by
      intro a b hRest hH
      simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq,
        hH, Option.isNone, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hRest
      cases hRest; exact hH
    refine seq_execSim hSim h₁ hNoHalt hpTail (fun hr hnh => cost_execSim hSim hr hnh) ?_
    intro s₁_mid s₂_mid hSimMid hRest _
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_get_eq, stateT_pure_eq] at hRest ⊢
    rw [← hSimMid.ctx_eq]
    by_cases hCond : (s₁_mid.ctx.outcome.isNone && !success && onFail == OnFail.bubble) = true
    · have hOutNone : s₁_mid.ctx.outcome = none := by
        cases ho : s₁_mid.ctx.outcome <;> simp_all
      simp only [hCond, ↓reduceIte, stateT_modify_eq, stateT_bind_eq] at hRest
      have hTerm := Core.terminate_revert_zero
        { s₁_mid with frames := s₁_mid.frames.map fun r => Option.map (fun (r : FrameResult) =>
          if r.id == id then { r with caught := some false } else r) r }
        hOutNone
      rw [hTerm] at hRest
      cases hRest
      exact absurd rfl hNoRev
    · simp only [hCond, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hRest ⊢
      cases hRest
      exact ⟨s₂_mid, rfl, hSimMid⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem liveStackLE_commitState_root {a b : MeterStack.State} {m₁' : Meter}
    (h : LiveStackLE 0 0 (a.top.meter :: a.parents.map (·.meter))
      (b.top.meter :: b.parents.map (·.meter)))
    (hp₁ : a.parents = [])
    (hBase₂ : b.top.meter.stateLeft ≤ b.top.meter.stateBaseline)
    (hc₁ : a.top.meter.commitState = .ok m₁') :
    ∃ m₂', b.top.meter.commitState = .ok m₂' ∧
      LiveStackLE 0 0 (m₁' :: a.parents.map (·.meter))
        (m₂' :: b.parents.map (·.meter)) := by
  cases hbp : b.parents with
  | cons _ _ =>
    rw [hp₁, hbp] at h
    cases h with
    | cons _ _ _ _ _ ht => cases ht
  | nil =>
    rw [hp₁] at h ⊢
    rw [hbp] at h
    simp only [List.map_nil] at h ⊢
    cases h with
    | cons hxy hg hr hs hc ht =>
      unfold Meter.commitState at hc₁
      split at hc₁
      · simp only [Except.ok.injEq] at hc₁
        subst hc₁
        let bm := b.top.meter
        refine ⟨{ bm with
          stateCommittedSpill := bm.stateCommittedSpill + bm.stateSpilled
          stateBaseline := bm.stateLeft
          stateSpilled := 0 }, ?_, ?_⟩
        · simp [Meter.commitState, bm, hBase₂]
        · refine .cons (by omega) hg hr (Nat.le_refl 0) (by dsimp [bm]; omega) (.nil ?_)
          dsimp only [bm]
          omega
      · cases hc₁

theorem meterOp_commitState_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    (hSim : ExecSim sender s₁ s₂)
    (hp₁ : s₁.meters.parents = [])
    (hBase₂ : s₂.meters.top.meter.stateLeft ≤ s₂.meters.top.meter.stateBaseline)
    (h₁ : (Exec.meterOp .commitState).run s₁ = .ok ((), s₁'))
    (hNoHalt : s₁'.ctx.outcome ≠ some .halt) :
    ∃ s₂', (Exec.meterOp .commitState).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  simp only [Exec.meterOp, Exec.running, stateT_run_eq, stateT_bind_eq,
    stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte, stateT_bind_raw, stateT_get_eq, MeterStack.apply,
      bind, Except.bind, pure, Except.pure] at h₁ ⊢
    cases hc₁ : s₁.meters.top.meter.commitState with
    | error e =>
      rw [hc₁] at h₁
      cases e with
      | outOfGas =>
        simp only [Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
        rcases h₁ with ⟨_, rfl⟩
        exact absurd rfl hNoHalt
      | assertion a =>
        simp only [stateT_throw_eq] at h₁; cases h₁
    | ok m₁' =>
      rw [hc₁] at h₁
      simp only [stateT_set_eq, Except.ok.injEq, Prod.mk.injEq] at h₁
      rcases h₁ with ⟨_, rfl⟩
      obtain ⟨m₂', hc₂, hLive'⟩ := liveStackLE_commitState_root hSim.live_stack_le hp₁ hBase₂ hc₁
      rw [hc₂]
      refine ⟨_, rfl, ?_⟩
      exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_sim, hLive',
        hSim.phase_eq.commitState hp₁ hc₁ hc₂, hSim.sites_eq, hSim.branches_eq, hSim.frames_size_eq⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem meterOp_dispatch_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.meterOp .dispatch).run s₁ = .ok ((), s₁')) :
    ∃ s₂', (Exec.meterOp .dispatch).run s₂ = .ok ((), s₂') ∧ ExecSim sender s₁' s₂' := by
  simp only [Exec.meterOp, Exec.running, stateT_run_eq, stateT_bind_eq,
    stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte, stateT_bind_raw, stateT_get_eq, MeterStack.apply, pure, Except.pure,
      stateT_set_eq] at h₁ ⊢
    cases h₁
    refine ⟨_, rfl, ?_⟩
    exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_sim, hSim.live_stack_le,
      hSim.phase_eq.dispatch, hSim.sites_eq, hSim.branches_eq, hSim.frames_size_eq⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem meterOp_spawnCall_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    {ra rb stipend : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (hw : min ra (allButOne64th s₁.meters.top.meter.gasLeft) ≤
      min rb (allButOne64th s₂.meters.top.meter.gasLeft))
    (hr : s₁.meters.top.meter.gasLeft - min ra (allButOne64th s₁.meters.top.meter.gasLeft) ≤
      s₂.meters.top.meter.gasLeft - min rb (allButOne64th s₂.meters.top.meter.gasLeft))
    (h₁ : (Exec.meterOp (.spawnCall ra stipend)).run s₁ = .ok ((), s₁')) :
    ∃ s₂', (Exec.meterOp (.spawnCall rb stipend)).run s₂ = .ok ((), s₂') ∧
      ExecSim sender s₁' s₂' := by
  simp only [Exec.meterOp, Exec.running, stateT_run_eq, stateT_bind_eq,
    stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte, stateT_bind_eq, stateT_bind_raw, stateT_get_eq] at h₁ ⊢
    obtain ⟨m₁', m₂', hm₁, hm₂, hLive'⟩ := liveStackLE_spawnCall ra rb stipend hSim.live_stack_le hw hr
    rw [hm₁] at h₁
    rw [hm₂]
    simp only [stateT_set_eq] at h₁ ⊢
    cases h₁
    refine ⟨_, rfl, ?_⟩
    exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_sim, hLive',
      hSim.phase_eq.spawnCall hm₁ hm₂, hSim.sites_eq, hSim.branches_eq, hSim.frames_size_eq⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem meterOp_spawnCreate_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    (hSim : ExecSim sender s₁ s₂)
    (h₁ : (Exec.meterOp .spawnCreate).run s₁ = .ok ((), s₁')) :
    ∃ s₂', (Exec.meterOp .spawnCreate).run s₂ = .ok ((), s₂') ∧
      ExecSim sender s₁' s₂' := by
  simp only [Exec.meterOp, Exec.running, stateT_run_eq, stateT_bind_eq,
    stateT_get_eq, stateT_pure_eq] at h₁ ⊢
  rw [← hSim.ctx_eq]
  by_cases hRun : s₁.ctx.outcome.isNone = true
  · simp only [hRun, ↓reduceIte, stateT_bind_eq, stateT_bind_raw, stateT_get_eq] at h₁ ⊢
    obtain ⟨m₁', m₂', hm₁, hm₂, hLive'⟩ := liveStackLE_spawnCreate hSim.live_stack_le
    rw [hm₁] at h₁
    rw [hm₂]
    simp only [stateT_set_eq] at h₁ ⊢
    cases h₁
    refine ⟨_, rfl, ?_⟩
    exact ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_sim, hLive',
      hSim.phase_eq.spawnCreate hm₁ hm₂, hSim.sites_eq, hSim.branches_eq, hSim.frames_size_eq⟩
  · simp only [hRun, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at h₁ ⊢
    cases h₁
    exact ⟨s₂, rfl, hSim⟩

theorem cost_exec_only_gas {ov : Nat} {s s' : Exec.Machine}
    (h : (Exec.cost { exec := ov }).run s = .ok ((), s'))
    (hNone : s.ctx.outcome = none)
    (hNoHalt : s'.ctx.outcome ≠ some .halt) :
    ov ≤ s.meters.top.meter.gasLeft ∧
      s'.meters.top.meter.gasLeft = s.meters.top.meter.gasLeft - ov ∧
      s'.meters.top.meter.stateLeft = s.meters.top.meter.stateLeft ∧
      s'.ctx = s.ctx ∧ s'.world = s.world ∧ s'.fork = s.fork := by
  simp only [Exec.cost, Exec.running, stateT_run_eq, stateT_bind_eq, stateT_bind_raw, stateT_get_eq, stateT_pure_eq, stateT_pure_raw,
    hNone, Option.isNone, ↓reduceIte,
    show ((0 : Nat) != 0) = false from rfl, Bool.false_and, Bool.false_eq_true,
    show ((0 : Int) != 0) = false from rfl] at h
  simp only [Exec.meterOp, Exec.running, stateT_bind_eq, stateT_bind_raw, stateT_get_eq, stateT_pure_eq, stateT_pure_raw,
    hNone, Option.isNone, ↓reduceIte, MeterStack.apply,
    bind, Except.bind, pure, Except.pure] at h
  cases hc : s.meters.top.meter.charge ov with
  | error e =>
    rw [hc] at h
    cases e with
    | outOfGas =>
      simp only [Exec.halt, stateT_modify_eq, Option.isNone, Bool.false_eq_true,
        ↓reduceIte, stateT_pure_eq, stateT_pure_raw, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      exact absurd rfl hNoHalt
    | assertion a =>
      simp only [stateT_throw_eq] at h; cases h
  | ok m₁ =>
    rw [hc] at h
    obtain ⟨hov, rfl⟩ := charge_ok hc
    simp only [stateT_set_eq, stateT_pure_raw, hNone, Option.isNone, ↓reduceIte,
      Meter.chargeState, Nat.zero_le, Nat.sub_zero, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    exact ⟨hov, rfl, rfl, rfl, rfl, rfl⟩

theorem cost_state_only_gas {st : Nat} {s s' : Exec.Machine}
    (h : (Exec.cost { state := st }).run s = .ok ((), s'))
    (hNone : s.ctx.outcome = none)
    (hNoHalt : s'.ctx.outcome ≠ some .halt) :
    st - min st s.meters.top.meter.stateLeft ≤ s.meters.top.meter.gasLeft ∧
      s'.meters.top.meter.gasLeft = s.meters.top.meter.gasLeft - (st - min st s.meters.top.meter.stateLeft) ∧
      s'.ctx = s.ctx ∧ s'.world = s.world ∧ s'.fork = s.fork := by
  simp only [Exec.cost, Exec.running, stateT_run_eq, stateT_bind_eq, stateT_bind_raw, stateT_get_eq, stateT_pure_eq, stateT_pure_raw,
    hNone, Option.isNone, ↓reduceIte,
    show ((0 : Nat) != 0) = false from rfl, Bool.false_and, Bool.false_eq_true,
    show ((0 : Int) != 0) = false from rfl] at h
  simp only [Exec.meterOp, Exec.running, stateT_bind_eq, stateT_bind_raw, stateT_get_eq, stateT_pure_eq, stateT_pure_raw,
    hNone, Option.isNone, ↓reduceIte, MeterStack.apply,
    bind, Except.bind, pure, Except.pure,
    Meter.charge, Nat.zero_le, Nat.sub_zero, stateT_set_eq] at h
  cases hc : s.meters.top.meter.chargeState st with
  | error e =>
    rw [hc] at h
    cases e with
    | outOfGas =>
      simp only [Exec.halt, stateT_modify_eq, stateT_pure_raw, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      exact absurd rfl hNoHalt
    | assertion a =>
      simp only [stateT_throw_eq] at h; cases h
  | ok m₁ =>
    rw [hc] at h
    simp only [stateT_set_eq, stateT_pure_raw, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩
    unfold Meter.chargeState at hc
    split at hc
    · rename_i hle
      simp only [Except.ok.injEq] at hc
      subst hc
      have hmin : min st s.meters.top.meter.stateLeft = st := Nat.min_eq_left hle
      refine ⟨by omega, ?_, rfl, rfl, rfl⟩
      dsimp only
      omega
    · rename_i hgt
      split at hc <;> try contradiction
      rename_i hsp
      simp only [Except.ok.injEq] at hc
      subst hc
      have hmin : min st s.meters.top.meter.stateLeft = s.meters.top.meter.stateLeft :=
        Nat.min_eq_right (by omega)
      refine ⟨by omega, ?_, rfl, rfl, rfl⟩
      dsimp only
      omega

def beginCallInput (s : Exec.Machine) (kind : CallKind) (addr : Nat) (arg : GasArg)
    (value argsLen code : Nat) : Call.Input :=
  let k : Call.Kind := match kind with
    | .call => .call | .callcode => .callcode | .delegatecall => .delegatecall | .staticcall => .staticcall
  { kind := k, targetWarm := s.world.isAddressWarm addr, valueNonzero := value != 0,
    targetAlive := s.world.isAlive addr,
    delegated := code != addr || (match (s.world.getAccount addr).code with | .delegation _ => true | _ => false),
    delegateWarm := (s.world.warmAddress addr).isAddressWarm code,
    requestedGas := Exec.gasArg arg s.meters.top.meter.gasLeft,
    gasLeft := s.meters.top.meter.gasLeft, stateGasLeft := s.meters.top.meter.stateLeft,
    memoryCost := Rules.memoryExpansion s.fork s.ctx.memory argsLen, depth := s.ctx.depth,
    insufficientBalance := (s.world.getAccount s.ctx.account).balance < value }

theorem beginCallInput_props {sender : Nat} {s₁ s₂ : Exec.Machine}
    {kind : CallKind} {addr : Nat} {arg : GasArg} {value argsLen code : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (hSafe : (!(s₁.ctx.account == sender && (kind == CallKind.call || kind == CallKind.callcode)) || value == 0) = true) :
    let i₁ := beginCallInput s₁ kind addr arg value argsLen code
    let i₂ := beginCallInput s₂ kind addr arg value argsLen code
    Call.hasValue i₂ = Call.hasValue i₁ ∧
      Call.createsAccount i₂ = Call.createsAccount i₁ ∧
      Call.newAccountCost s₂.fork.schedule i₂ = Call.newAccountCost s₁.fork.schedule i₁ ∧
      Call.overhead s₂.fork.schedule i₂ = Call.overhead s₁.fork.schedule i₁ ∧
      i₂.delegated = i₁.delegated ∧
      ((kind == CallKind.call || kind == CallKind.callcode) && i₂.insufficientBalance) =
        ((kind == CallKind.call || kind == CallKind.callcode) && i₁.insufficientBalance) := by
  dsimp only
  have hWarm : s₂.world.isAddressWarm addr = s₁.world.isAddressWarm addr :=
    (hSim.world_sim.warmAddr addr).symm
  have hAlive : s₂.world.isAlive addr = s₁.world.isAlive addr :=
    (hSim.world_sim.isAlive_eq addr).symm
  have hCode : (s₂.world.getAccount addr).code = (s₁.world.getAccount addr).code :=
    (hSim.world_sim.code_eq addr).symm
  have hDelWarm : (s₂.world.warmAddress addr).isAddressWarm code =
      (s₁.world.warmAddress addr).isAddressWarm code :=
    ((hSim.world_sim.warmAddress_preserves addr).warmAddr code).symm
  have hHasVal : Call.hasValue (beginCallInput s₂ kind addr arg value argsLen code) =
      Call.hasValue (beginCallInput s₁ kind addr arg value argsLen code) := rfl
  have hCreates : Call.createsAccount (beginCallInput s₂ kind addr arg value argsLen code) =
      Call.createsAccount (beginCallInput s₁ kind addr arg value argsLen code) := by
    simp [Call.createsAccount, beginCallInput, hAlive]
  have hNewAcc : Call.newAccountCost s₂.fork.schedule (beginCallInput s₂ kind addr arg value argsLen code) =
      Call.newAccountCost s₁.fork.schedule (beginCallInput s₁ kind addr arg value argsLen code) := by
    simp [Call.newAccountCost, hCreates, hSim.fork_eq]
  have hDel : (beginCallInput s₂ kind addr arg value argsLen code).delegated =
      (beginCallInput s₁ kind addr arg value argsLen code).delegated := by
    simp [beginCallInput, hCode]
  have hOv : Call.overhead s₂.fork.schedule (beginCallInput s₂ kind addr arg value argsLen code) =
      Call.overhead s₁.fork.schedule (beginCallInput s₁ kind addr arg value argsLen code) := by
    simp [Call.overhead, Call.hasValue, Call.createsAccount, beginCallInput,
      hWarm, hAlive, hCode, hDelWarm, hSim.fork_eq, hSim.ctx_eq]
  refine ⟨hHasVal, hCreates, hNewAcc, hOv, hDel, ?_⟩
  by_cases hk : (kind == CallKind.call || kind == CallKind.callcode) = true
  · simp only [hk, Bool.true_and, beginCallInput]
    rw [← hSim.ctx_eq]
    have hSafe' : value = 0 ∨ s₁.ctx.account ≠ sender := by
      simp only [hk, Bool.and_true, Bool.not_eq_true', beq_eq_false_iff_ne,
        Bool.or_eq_true, beq_iff_eq] at hSafe
      exact hSafe.symm
    exact (hSim.world_sim.insufficientBalance_eq s₁.ctx.account value hSafe').symm
  · simp [hk]

@[simp] private theorem ofExcept_ok_eq {α : Type} (x : α) :
    (ofExcept (Except.ok x) : Exec.M α) = pure x := rfl

@[simp] private theorem ofExcept_error_eq {α : Type} (e : ExecError) :
    (ofExcept (Except.error e) : Exec.M α) = throw e := rfl

private theorem ite_do_eq_bind {α : Type} (c : Bool) (act : Exec.M Unit) (rest : Exec.M α) :
    (if c = true then do act; rest else rest) = ((if c = true then act else pure ()) >>= fun _ => rest) := by
  cases c <;> rfl

private theorem call_overhead_irrel (sched : Schedule) (k : Call.Kind) (tw vn ta del dw : Bool)
    (req₁ req₂ g₁ g₂ mc st₁ st₂ d : Nat) (ib₁ ib₂ : Bool) :
    Call.overhead sched ⟨k, tw, vn, ta, del, dw, req₁, g₁, mc, st₁, d, ib₁⟩ =
    Call.overhead sched ⟨k, tw, vn, ta, del, dw, req₂, g₂, mc, st₂, d, ib₂⟩ := rfl

private theorem call_newAccountCost_irrel (sched : Schedule) (k : Call.Kind) (tw vn ta del dw : Bool)
    (req₁ req₂ g₁ g₂ mc st₁ st₂ d : Nat) (ib₁ ib₂ : Bool) :
    Call.newAccountCost sched ⟨k, tw, vn, ta, del, dw, req₁, g₁, mc, st₁, d, ib₁⟩ =
    Call.newAccountCost sched ⟨k, tw, vn, ta, del, dw, req₂, g₂, mc, st₂, d, ib₂⟩ := rfl

private theorem call_hasValue_irrel (k : Call.Kind) (tw vn ta del dw : Bool)
    (req₁ req₂ g₁ g₂ mc st₁ st₂ d : Nat) (ib₁ ib₂ : Bool) :
    Call.hasValue ⟨k, tw, vn, ta, del, dw, req₁, g₁, mc, st₁, d, ib₁⟩ =
    Call.hasValue ⟨k, tw, vn, ta, del, dw, req₂, g₂, mc, st₂, d, ib₂⟩ := rfl

private theorem bind_do_ok {α β : Type} {m : Exec.M α} {f : α → Exec.M β} {s s'' : Exec.Machine} {b : β}
    (h : (m >>= f) s = .ok (b, s'')) :
    ∃ a s', m.run s = .ok (a, s') ∧ (f a).run s' = .ok (b, s'') := by
  simp only [stateT_run_eq, stateT_bind_eq] at h ⊢
  cases hm : m s with
  | error e => rw [hm] at h; cases h
  | ok p => exact ⟨p.1, p.2, rfl, by simpa [hm] using h⟩

private theorem bind_do_step {α β : Type} {m : Exec.M α} {f : α → Exec.M β} {s s' : Exec.Machine} {a : α}
    (h : m.run s = .ok (a, s')) :
    (m >>= f) s = (f a).run s' := by
  simp only [stateT_run_eq, stateT_bind_eq] at h ⊢
  simp [h]

private theorem pre_charges_bind {α : Type} (fork : Fork) (isStatic : Bool) (kind : CallKind)
    (value ov : Nat) (sched : Schedule) (i : Call.Input) (rest : Unit → Exec.M α) :
    (Exec.cost { exec := ov } >>= fun _ =>
      Exec.running >>= fun r =>
      (if (fork == Fork.osaka && r && isStatic && kind == CallKind.call && value != 0) = true then
        Exec.halt "WriteInStaticContext"
      else pure ()) >>= fun _ =>
      (if (fork == Fork.amsterdam) = true then
        Exec.cost (Call.newAccountCost sched i)
      else pure ()) >>= rest) =
    ((do
      Exec.cost { exec := ov }
      if fork == Fork.osaka && (← Exec.running) && isStatic && kind == CallKind.call && value != 0 then
        Exec.halt "WriteInStaticContext"
      if fork == Fork.amsterdam then
        Exec.cost { state := (Call.newAccountCost sched i).state }) >>= rest) := by
  simp only [ite_do_eq_bind, bind_assoc, pure_bind]
  rfl

private theorem create_checks_bind {α : Type} (maxInit len : Nat) (isStatic : Bool) (rest : Unit → Exec.M α) :
    (Exec.running >>= fun r1 =>
      (if (r1 && decide (len > maxInit)) = true then Exec.halt else pure ()) >>= fun _ =>
      Exec.running >>= fun r2 =>
      (if (r2 && isStatic) = true then Exec.halt "WriteInStaticContext" else pure ()) >>= rest) =
    ((do
      if (← Exec.running) && decide (len > maxInit) then Exec.halt
      if (← Exec.running) && isStatic then Exec.halt "WriteInStaticContext") >>= rest) := by
  simp only [ite_do_eq_bind, bind_assoc, pure_bind]

private theorem beginCall_match_1_eq {α : Type} (arg : GasArg) (g : Nat)
    (u : Exec.M Unit) (cont : Exec.M α)
    (h : ∀ k, arg = .gasMinusChecked k → k ≤ g) :
    Exec.beginCall.match_1 (fun _ => Exec.M α) arg
      (fun k => if g < k then do u; cont else cont)
      (fun _ => cont) = cont := by
  cases arg with
  | gasMinusChecked k =>
    have hk := h k rfl
    have hlt : ¬ (g < k) := by omega
    simp [Exec.beginCall.match_1, hlt]
  | _ => rfl

theorem call_charges_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    {ov st : Nat} {kind : CallKind} {value : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (hNone : s₁.ctx.outcome = none)
    (h₁ : (do
      Exec.cost { exec := ov }
      if s₁.fork == Fork.osaka && (← Exec.running) && s₁.ctx.isStatic && kind == CallKind.call && value != 0 then
        Exec.halt "WriteInStaticContext"
      if s₁.fork == Fork.amsterdam then Exec.cost { state := st }).run s₁ = .ok ((), s₁'))
    (hAfterNone : s₁'.ctx.outcome = none) :
    ∃ s₂', (do
      Exec.cost { exec := ov }
      if s₂.fork == Fork.osaka && (← Exec.running) && s₂.ctx.isStatic && kind == CallKind.call && value != 0 then
        Exec.halt "WriteInStaticContext"
      if s₂.fork == Fork.amsterdam then Exec.cost { state := st }).run s₂ = .ok ((), s₂') ∧
      ExecSim sender s₁' s₂' ∧
      s₁'.ctx = s₁.ctx ∧ s₁'.world = s₁.world ∧
      s₁'.meters.top.meter.gasLeft ≤ s₁.meters.top.meter.gasLeft ∧
      s₂'.meters.top.meter.gasLeft ≤ s₂.meters.top.meter.gasLeft ∧
      s₂.meters.top.meter.gasLeft - s₂'.meters.top.meter.gasLeft ≤
        s₁.meters.top.meter.gasLeft - s₁'.meters.top.meter.gasLeft := by
  have hNoHalt' : s₁'.ctx.outcome ≠ some .halt := by simp [hAfterNone]
  have hpTail : ∀ {a b : Exec.Machine},
      (do
        if s₁.fork == Fork.osaka && (← Exec.running) && s₁.ctx.isStatic && kind == CallKind.call && value != 0 then
          Exec.halt "WriteInStaticContext"
        if s₁.fork == Fork.amsterdam then Exec.cost { state := st }).run a = .ok ((), b) →
      a.ctx.outcome = some .halt → b.ctx.outcome = some .halt := by
    intro a b hRest hH
    simp only [Exec.running, stateT_run_eq, stateT_bind_eq, stateT_bind_raw, stateT_get_eq, stateT_pure_eq, stateT_pure_raw,
      hH, Option.isNone, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hRest
    by_cases hAms : (s₁.fork == Fork.amsterdam) = true
    · simp only [hAms, ↓reduceIte] at hRest
      exact cost_preserves_halt hRest hH
    · simp only [hAms, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq] at hRest
      cases hRest; exact hH
  rw [← hSim.fork_eq, ← hSim.ctx_eq]
  simp only [stateT_run_eq, stateT_bind_eq] at h₁ ⊢
  cases hc₁ : Exec.cost { exec := ov } s₁ with
  | error e => rw [hc₁] at h₁; cases h₁
  | ok p₁ =>
    rcases p₁ with ⟨⟨⟩, s₁_1⟩
    rw [hc₁] at h₁
    have hNoHalt1 : s₁_1.ctx.outcome ≠ some .halt := fun hH => hNoHalt' (hpTail h₁ hH)
    obtain ⟨s₂_1, hc₂, hSim1⟩ := cost_execSim hSim hc₁ hNoHalt1
    have hNone₂ : s₂.ctx.outcome = none := by rw [← hSim.ctx_eq]; exact hNone
    have hNoHalt1₂ : s₂_1.ctx.outcome ≠ some .halt := by rw [← hSim1.ctx_eq]; exact hNoHalt1
    obtain ⟨hov₁, hg₁_1, hst₁_1, hctx₁_1, hw₁_1, _⟩ := cost_exec_only_gas hc₁ hNone hNoHalt1
    obtain ⟨hov₂, hg₂_1, hst₂_1, hctx₂_1, hw₂_1, _⟩ := cost_exec_only_gas hc₂ hNone₂ hNoHalt1₂
    rw [show Exec.cost { exec := ov } s₂ = .ok ((), s₂_1) from hc₂]
    have hNone1 : s₁_1.ctx.outcome = none := hctx₁_1 ▸ hNone
    have hNone1₂ : s₂_1.ctx.outcome = none := hctx₂_1 ▸ hNone₂
    simp only [Exec.running, stateT_bind_eq, stateT_bind_raw, stateT_get_eq, stateT_pure_eq, stateT_pure_raw,
      hNone1, hNone1₂, Option.isNone, Bool.true_and, Bool.and_true] at h₁ ⊢
    by_cases hOsaHalt : (s₁.fork == Fork.osaka && s₁.ctx.isStatic && kind == CallKind.call && value != 0) = true
    · simp only [hOsaHalt, ↓reduceIte, Exec.halt, stateT_bind_eq, stateT_bind_raw, stateT_modify_eq] at h₁
      have hHaltMid : ({ s₁_1 with ctx := { s₁_1.ctx with outcome := some .halt, error := some "WriteInStaticContext" } } : Exec.Machine).ctx.outcome = some .halt := rfl
      by_cases hAms : (s₁.fork == Fork.amsterdam) = true
      · simp only [hAms, ↓reduceIte] at h₁
        exact absurd (cost_preserves_halt h₁ hHaltMid) hNoHalt'
      · simp only [hAms, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq, stateT_pure_raw, Except.ok.injEq, Prod.mk.injEq] at h₁
        rcases h₁ with ⟨_, rfl⟩
        exact absurd rfl hNoHalt'
    · simp only [hOsaHalt, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
      by_cases hAms : (s₁.fork == Fork.amsterdam) = true
      · simp only [hAms, ↓reduceIte] at h₁ ⊢
        obtain ⟨s₂', hst₂, hSim'⟩ := cost_execSim hSim1 h₁ hNoHalt'
        have hNoHalt'₂ : s₂'.ctx.outcome ≠ some .halt := by rw [← hSim'.ctx_eq]; exact hNoHalt'
        obtain ⟨hsp₁, hg₁', hctx₁', hw₁', _⟩ := cost_state_only_gas h₁ hNone1 hNoHalt'
        obtain ⟨hsp₂, hg₂', hctx₂', hw₂', _⟩ := cost_state_only_gas hst₂ hNone1₂ hNoHalt'₂
        have hResLE : s₁.meters.top.meter.stateLeft ≤ s₂.meters.top.meter.stateLeft := by
          cases hSim.live_stack_le with
          | cons _ _ hr _ _ _ => exact hr
        refine ⟨s₂', hst₂, hSim', hctx₁'.trans hctx₁_1, hw₁'.trans hw₁_1,
          by omega, by omega, ?_⟩
        rw [hg₁', hg₁_1, hst₁_1, hg₂', hg₂_1, hst₂_1] at *
        omega
      · simp only [hAms, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq, stateT_pure_raw] at h₁ ⊢
        cases h₁
        refine ⟨s₂_1, rfl, hSim1, hctx₁_1, hw₁_1, by omega, by omega, ?_⟩
        rw [hg₁_1, hg₂_1]
        omega

@[simp] private theorem running_eq (s : Exec.Machine) :
    Exec.running s = .ok (s.ctx.outcome.isNone, s) := rfl

private theorem bind_modify_step {β : Type} (g : Exec.Machine → Exec.Machine)
    (f : Unit → Exec.M β) (s : Exec.Machine) :
    (modify g >>= f) s = f () (g s) := rfl

private theorem bind_get_step {β : Type} (f : Exec.Machine → Exec.M β) (s : Exec.Machine) :
    (get >>= f) s = f s s := rfl

private theorem bind_running_step {β : Type} (f : Bool → Exec.M β) (s : Exec.Machine) :
    (Exec.running >>= f) s = f s.ctx.outcome.isNone s := rfl

theorem beginCall_some_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    {kind : CallKind} {addr : Nat} {arg : GasArg} {value argsLen id : Nat}
    {frameKind : FrameKind} {parent₁ : Exec.Context} {saved₁ : State.Snapshot} {refill₁ : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (hNone : s₁.ctx.outcome = none)
    (hNoWrap : NoWrappingGasArg arg = true)
    (hSafe : (!(s₁.ctx.account == sender && (kind == CallKind.call || kind == CallKind.callcode)) || value == 0) = true)
    (h₁ : (Exec.beginCall kind addr arg value argsLen id frameKind).run s₁ =
      .ok (some (parent₁, saved₁, refill₁), s₁')) :
    ∃ saved₂ s₂',
      (Exec.beginCall kind addr arg value argsLen id frameKind).run s₂ =
        .ok (some (parent₁, saved₂, refill₁), s₂') ∧
      ExecSim sender s₁' s₂' ∧
      s₁'.ctx.outcome = none := by
  unfold Exec.beginCall at h₁ ⊢
  simp only [stateT_run_eq, stateT_bind_eq, Exec.site, stateT_modify_eq, stateT_get_eq] at h₁ ⊢
  let s₁_0 : Exec.Machine := { s₁ with sites := s₁.sites.map fun x =>
    if x.frame == id then { x with executed := true, entered := false || x.entered } else x }
  let s₂_0 : Exec.Machine := { s₂ with sites := s₂.sites.map fun x =>
    if x.frame == id then { x with executed := true, entered := false || x.entered } else x }
  have hSim0 : ExecSim sender s₁_0 s₂_0 :=
    ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_sim, hSim.live_stack_le,
      hSim.phase_eq, by simp [s₁_0, s₂_0, hSim.sites_eq], hSim.branches_eq, hSim.frames_size_eq⟩
  have hGasLE0 : s₁.meters.top.meter.gasLeft ≤ s₂_0.meters.top.meter.gasLeft := by
    cases hSim0.live_stack_le with
    | cons _ hg _ _ _ _ => exact hg
  have hGuard₁ : ∀ k, arg = .gasMinusChecked k → k ≤ s₁.meters.top.meter.gasLeft := by
    intro k hk
    subst hk
    dsimp only at h₁
    by_cases hlt : s₁.meters.top.meter.gasLeft < k
    · simp [hlt, Exec.unsupported, stateT_bind_eq, stateT_bind_raw, stateT_throw_eq] at h₁
    · omega
  have hGuard₂ : ∀ k, arg = .gasMinusChecked k → k ≤ s₂.meters.top.meter.gasLeft := by
    intro k hk
    have hk₁ := hGuard₁ k hk
    have : s₁.meters.top.meter.gasLeft ≤ s₂.meters.top.meter.gasLeft := by
      cases hSim.live_stack_le with | cons _ hg _ _ _ _ => exact hg
    omega
  rw [beginCall_match_1_eq arg s₁.meters.top.meter.gasLeft _ _ hGuard₁] at h₁
  rw [beginCall_match_1_eq arg s₂.meters.top.meter.gasLeft _ _ hGuard₂]
  simp only [← hSim.fork_eq, ← hSim.ctx_eq, ite_do_eq_bind] at h₁ ⊢
  by_cases hStatAms : (s₁.fork == Fork.amsterdam && s₁.ctx.isStatic && kind == CallKind.call && value != 0) = true
  · simp [hStatAms, Exec.halt, stateT_modify_eq, stateT_pure_eq] at h₁
  · simp only [hStatAms, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq, ofExcept_eq] at h₁ ⊢
    rw [← hSim.world_sim.codeTarget_eq addr]
    cases hCode : Exec.codeTarget s₁.world addr with
    | error e => simp [hCode, ofExcept_error_eq, stateT_throw_eq] at h₁
    | ok code =>
      simp only [hCode, ofExcept_ok_eq, pure_bind, ite_do_eq_bind] at h₁ ⊢
      have hWarm : s₂.world.isAddressWarm addr = s₁.world.isAddressWarm addr :=
        (hSim.world_sim.warmAddr addr).symm
      have hAlive : s₂.world.isAlive addr = s₁.world.isAlive addr :=
        (hSim.world_sim.isAlive_eq addr).symm
      have hCodeField : (s₂.world.getAccount addr).code = (s₁.world.getAccount addr).code :=
        (hSim.world_sim.code_eq addr).symm
      have hWarmCode : (s₂.world.warmAddress addr).isAddressWarm code = (s₁.world.warmAddress addr).isAddressWarm code :=
        ((hSim.world_sim.warmAddress_preserves addr).warmAddr code).symm
      obtain ⟨_, _, _, _, _, hInsuff⟩ :=
        beginCallInput_props (addr := addr) (code := code) (argsLen := argsLen) (arg := arg) hSim hSafe
      dsimp only [beginCallInput] at hInsuff
      try rw [← hSim.ctx_eq] at hInsuff
      rw [hWarm, hAlive, hCodeField, hWarmCode, hInsuff]
      rw [call_overhead_irrel _ _ _ _ _ _ _ _ (Exec.gasArg arg s₁.meters.top.meter.gasLeft) _ s₁.meters.top.meter.gasLeft _ _ s₁.meters.top.meter.stateLeft _ _ (decide ((s₁.world.getAccount s₁.ctx.account).balance < value))]
      rw [call_newAccountCost_irrel _ _ _ _ _ _ _ _ (Exec.gasArg arg s₁.meters.top.meter.gasLeft) _ s₁.meters.top.meter.gasLeft _ _ s₁.meters.top.meter.stateLeft _ _ (decide ((s₁.world.getAccount s₁.ctx.account).balance < value))]
      rw [call_hasValue_irrel _ _ _ _ _ _ _ (Exec.gasArg arg s₁.meters.top.meter.gasLeft) _ s₁.meters.top.meter.gasLeft _ _ s₁.meters.top.meter.stateLeft _ _ (decide ((s₁.world.getAccount s₁.ctx.account).balance < value))]
      rw [pre_charges_bind] at h₁
      rw [pre_charges_bind]
      obtain ⟨⟨⟩, s₁_1, hPre₁, h₁⟩ := bind_do_ok h₁
      rw [stateT_run_eq, bind_running_step] at h₁
      by_cases hNotRun : (!s₁_1.ctx.outcome.isNone) = true
      · simp [hNotRun] at h₁
      · have hRun1 : s₁_1.ctx.outcome = none := by
          cases ho : s₁_1.ctx.outcome <;> simp_all
        obtain ⟨s₂_1, hPre₂, hSim1, hctx₁_1, hw₁_1, hle₁, hle₂, hdrop⟩ :=
          call_charges_execSim (kind := kind) (value := value) hSim0 hNone hPre₁ hRun1
        dsimp only [s₁_0, s₂_0] at hPre₂
        rw [← hSim.fork_eq, ← hSim.ctx_eq] at hPre₂
        rw [bind_do_step hPre₂]
        have hNotRun₂ : (!s₂_1.ctx.outcome.isNone) = false := by
          rw [← hSim1.ctx_eq]; simpa using hNotRun
        simp only [hNotRun, Bool.false_eq_true, ↓reduceIte] at h₁
        rw [bind_modify_step, bind_get_step] at h₁
        rw [stateT_run_eq, bind_running_step]
        simp only [hNotRun₂, Bool.false_eq_true, ↓reduceIte]
        rw [bind_modify_step, bind_get_step]
        let s₁_2 : Exec.Machine := { s₁_1 with
          world := (s₁.world.warmAddress addr).warmAddress code
          ctx.memory := max s₁_1.ctx.memory (32 * Rules.wordsForBytes argsLen) }
        let s₂_2 : Exec.Machine := { s₂_1 with
          world := (s₂.world.warmAddress addr).warmAddress code
          ctx.memory := max s₂_1.ctx.memory (32 * Rules.wordsForBytes argsLen) }
        have hSim2 : ExecSim sender s₁_2 s₂_2 :=
          ⟨hSim1.fork_eq, by simp [s₁_2, s₂_2, hSim1.ctx_eq],
            (hSim.world_sim.warmAddress_preserves addr).warmAddress_preserves code,
            hSim1.live_stack_le, hSim1.phase_eq, hSim1.sites_eq,
            hSim1.branches_eq, hSim1.frames_size_eq⟩
        have hG : s₁.meters.top.meter.gasLeft ≤ s₂.meters.top.meter.gasLeft := hGasLE0
        have hG' : s₁_2.meters.top.meter.gasLeft ≤ s₂_2.meters.top.meter.gasLeft := by
          cases hSim2.live_stack_le with | cons _ hg _ _ _ _ => exact hg
        obtain ⟨hw_grant, hr_ret⟩ :=
          call_grant_and_retained_monotone arg hNoWrap hG hG' hle₁ hle₂ hdrop hGuard₁
        obtain ⟨⟨⟩, s₁_3, hSp₁, h₁⟩ := bind_do_ok h₁
        obtain ⟨s₂_3, hSp₂, hSim3⟩ := meterOp_spawnCall_execSim hSim2 hw_grant hr_ret hSp₁
        dsimp only [s₂_2] at hSp₂
        rw [bind_do_step hSp₂]
        dsimp only [stateT_run_eq] at h₁ ⊢
        rw [← hSim1.ctx_eq]
        by_cases hAbort : (decide (s₁.fork.schedule.stackDepthLimit < s₁_1.ctx.depth + 1) ||
            ((kind == CallKind.call || kind == CallKind.callcode) &&
              decide ((s₁.world.getAccount s₁.ctx.account).balance < value))) = true
        · simp only [hAbort, ↓reduceIte] at h₁
          obtain ⟨⟨⟩, s₁_ab, hmAb, h₁⟩ := bind_do_ok h₁
          obtain ⟨⟨⟩, s₁_ref, hcAb, h₁⟩ := bind_do_ok h₁
          rw [stateT_run_eq, bind_modify_step, stateT_pure_eq] at h₁
          cases h₁
        · simp only [hAbort, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
          rw [bind_get_step, bind_modify_step] at h₁ ⊢
          let s₁_4 : Exec.Machine := { s₁_3 with sites := s₁_3.sites.map fun x =>
            if x.frame == id then { x with executed := true, entered := true || x.entered } else x }
          let s₂_4 : Exec.Machine := { s₂_3 with sites := s₂_3.sites.map fun x =>
            if x.frame == id then { x with executed := true, entered := true || x.entered } else x }
          have hSim4 : ExecSim sender s₁_4 s₂_4 := by
            refine ⟨hSim3.fork_eq, hSim3.ctx_eq, hSim3.world_sim, hSim3.live_stack_le,
              hSim3.phase_eq, ?_, hSim3.branches_eq, hSim3.frames_size_eq⟩
            simp [s₁_4, s₂_4, hSim3.sites_eq]
          obtain ⟨⟨⟩, s₁_5, hCT₁, h₁⟩ := bind_do_ok h₁
          have hIfCall :
              (if kind == CallKind.call then
                Exec.checkTransfer s₁_1.ctx.account
                  (if kind == CallKind.call || kind == CallKind.staticcall then addr else s₁_1.ctx.account) value
              else pure ()).run s₂_4 = .ok ((), s₂_4) ∧ s₁_5 = s₁_4 := by
            by_cases hk : (kind == CallKind.call) = true
            · simp only [hk, ↓reduceIte] at hCT₁ ⊢
              have hSafeCT : value = 0 ∨ s₁_1.ctx.account ≠ sender ∨
                  value ≤ (s₂_4.world.getAccount s₁_1.ctx.account).balance := by
                rw [hctx₁_1]
                simp only [hk, Bool.true_or, Bool.and_true, Bool.not_eq_true',
                  beq_eq_false_iff_ne, Bool.or_eq_true, beq_iff_eq] at hSafe
                rcases hSafe with hne | h0
                · exact Or.inr (Or.inl hne)
                · exact Or.inl h0
              exact checkTransfer_execSim hSim4 hSafeCT hCT₁
            · simp only [hk, Bool.false_eq_true, ↓reduceIte, stateT_run_eq,
                stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at hCT₁ ⊢
              exact ⟨trivial, hCT₁.2.symm⟩
          obtain ⟨hCT₂, rfl⟩ := hIfCall
          dsimp only [s₂_4] at hCT₂
          rw [bind_do_step hCT₂]
          rw [stateT_run_eq, bind_modify_step, stateT_pure_eq] at h₁ ⊢
          simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h₁ ⊢
          rcases h₁ with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
          refine ⟨s₂_3.world.snapshot, _, ⟨⟨rfl, rfl, rfl⟩, rfl⟩, ?_, rfl⟩
          have hMovEq : CommittedEffects.movement s₂_3.fork s₂_3.world s₁_1.ctx.account
              (if kind == CallKind.call || kind == CallKind.staticcall then addr else s₁_1.ctx.account) value =
            CommittedEffects.movement s₁_3.fork s₁_3.world s₁_1.ctx.account
              (if kind == CallKind.call || kind == CallKind.staticcall then addr else s₁_1.ctx.account) value := by
            rw [← hSim3.fork_eq]
            exact (hSim3.world_sim.movement_eq _ _ _ _).symm
          refine ⟨hSim4.fork_eq, by dsimp only [s₁_4, s₂_4]; rw [hMovEq], ?_,
            hSim4.live_stack_le, hSim4.phase_eq, hSim4.sites_eq,
            hSim4.branches_eq, hSim4.frames_size_eq⟩
          by_cases hk : (kind == CallKind.call) = true
          · simp only [hk, ↓reduceIte]
            exact hSim4.world_sim.transfer_preserves _ _ _
          · simp only [hk, Bool.false_eq_true, ↓reduceIte]
            exact hSim4.world_sim

theorem beginCreate_some_execSim {sender : Nat} {s₁ s₂ s₁' : Exec.Machine}
    {kind : CreateKind} {value len id : Nat} {address : Observed Address}
    {parent₁ : Exec.Context} {saved₁ : State.Snapshot} {refill₁ : Nat}
    (hSim : ExecSim sender s₁ s₂)
    (hSafe : (s₁.ctx.account != sender || value == 0) = true)
    (h₁ : (Exec.beginCreate kind value len id address).run s₁ =
      .ok (some (parent₁, saved₁, refill₁), s₁')) :
    ∃ saved₂ s₂',
      (Exec.beginCreate kind value len id address).run s₂ =
        .ok (some (parent₁, saved₂, refill₁), s₂') ∧
      ExecSim sender s₁' s₂' ∧
      s₁'.ctx.outcome = none := by
  unfold Exec.beginCreate at h₁ ⊢
  simp only [stateT_run_eq, stateT_bind_eq, Exec.site, stateT_modify_eq, stateT_get_eq] at h₁ ⊢
  let s₁_0 : Exec.Machine := { s₁ with sites := s₁.sites.map fun x =>
    if x.frame == id then { x with executed := true, entered := false || x.entered } else x }
  let s₂_0 : Exec.Machine := { s₂ with sites := s₂.sites.map fun x =>
    if x.frame == id then { x with executed := true, entered := false || x.entered } else x }
  have hSim0 : ExecSim sender s₁_0 s₂_0 :=
    ⟨hSim.fork_eq, hSim.ctx_eq, hSim.world_sim, hSim.live_stack_le,
      hSim.phase_eq, by simp [s₁_0, s₂_0, hSim.sites_eq], hSim.branches_eq, hSim.frames_size_eq⟩
  simp only [← hSim.fork_eq, ← hSim.ctx_eq, ite_do_eq_bind] at h₁ ⊢
  by_cases hStatAms : (s₁.fork == Fork.amsterdam && s₁.ctx.isStatic) = true
  · simp [hStatAms, Exec.halt, stateT_modify_eq, stateT_pure_eq] at h₁
  · simp only [hStatAms, Bool.false_eq_true, ↓reduceIte, pure_bind, ite_do_eq_bind] at h₁ ⊢
    obtain ⟨⟨⟩, s₁_1, hCost1, h₁⟩ := bind_do_ok h₁
    rw [stateT_run_eq, create_checks_bind] at h₁
    obtain ⟨⟨⟩, s₁_1', hStep1, h₁⟩ := bind_do_ok h₁
    rw [stateT_run_eq, bind_running_step] at h₁
    by_cases hNotRun1 : (!s₁_1'.ctx.outcome.isNone) = true
    · simp only [hNotRun1, ↓reduceIte, stateT_pure_eq] at h₁
      cases h₁
    · have hOut1 : s₁_1'.ctx.outcome = none := by
        cases ho : s₁_1'.ctx.outcome
        · rfl
        · rw [ho] at hNotRun1; contradiction
      have hStep1Run : s₁_1' = s₁_1 ∧
          (s₁_1.ctx.outcome.isNone && decide (len > s₁.fork.schedule.maxInitCodeSize)) = false ∧
          (s₁_1.ctx.outcome.isNone && s₁.ctx.isStatic) = false := by
        simp only [ite_do_eq_bind, stateT_run_eq, bind_running_step] at hStep1
        by_cases hMax : (s₁_1.ctx.outcome.isNone && decide (len > s₁.fork.schedule.maxInitCodeSize)) = true
        · simp only [hMax, ↓reduceIte, Exec.halt] at hStep1
          rw [bind_modify_step, bind_running_step] at hStep1
          simp only [Option.isNone, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
            stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at hStep1
          have : s₁_1'.ctx.outcome = some .halt := by rw [← hStep1.2]
          rw [hOut1] at this; cases this
        · simp only [Bool.not_eq_true] at hMax
          simp only [hMax, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_running_step] at hStep1
          by_cases hSt : (s₁_1.ctx.outcome.isNone && s₁.ctx.isStatic) = true
          · simp only [hSt, ↓reduceIte, Exec.halt, stateT_modify_eq, Except.ok.injEq, Prod.mk.injEq] at hStep1
            have : s₁_1'.ctx.outcome = some .halt := by rw [← hStep1.2]
            rw [hOut1] at this; cases this
          · simp only [Bool.not_eq_true] at hSt
            simp only [hSt, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq, Except.ok.injEq, Prod.mk.injEq] at hStep1
            exact ⟨hStep1.2.symm, hMax, hSt⟩
      rcases hStep1Run with ⟨hStep1Eq, hMaxF, hStF⟩
      rw [hStep1Eq] at hOut1 h₁
      have hNoHalt1 : s₁_1.ctx.outcome ≠ some .halt := by simp [hOut1]
      obtain ⟨s₂_1, hCost2, hSim1⟩ := cost_execSim hSim0 hCost1 hNoHalt1
      dsimp only [s₂_0] at hCost2
      rw [← hSim.fork_eq, ← hSim.ctx_eq] at hCost2
      rw [bind_do_step hCost2]
      rw [stateT_run_eq, create_checks_bind]
      have hStep1_2 : (do
          if (← Exec.running) && decide (len > s₁.fork.schedule.maxInitCodeSize) then Exec.halt
          if (← Exec.running) && s₁.ctx.isStatic then Exec.halt "WriteInStaticContext").run s₂_1 = .ok ((), s₂_1) := by
        simp only [ite_do_eq_bind, stateT_run_eq, bind_running_step]
        rw [← hSim1.ctx_eq]
        simp only [hMaxF, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_running_step,
          ← hSim1.ctx_eq, hStF, stateT_pure_eq]
      rw [bind_do_step hStep1_2]
      rw [stateT_run_eq, bind_running_step]
      rw [← hSim1.ctx_eq]
      simp only [hOut1, Option.isNone, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
      have hSafe' : value = 0 ∨ s₁.ctx.account ≠ sender := by
        simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at hSafe
        exact hSafe.symm
      have hPreflightEq : (decide ((s₂.world.getAccount s₁.ctx.account).balance < value) ||
          (s₂.world.getAccount s₁.ctx.account).nonce == 2^64-1 ||
          decide (s₁.fork.schedule.stackDepthLimit < s₁.ctx.depth + 1)) =
        (decide ((s₁.world.getAccount s₁.ctx.account).balance < value) ||
          (s₁.world.getAccount s₁.ctx.account).nonce == 2^64-1 ||
          decide (s₁.fork.schedule.stackDepthLimit < s₁.ctx.depth + 1)) :=
        (hSim.world_sim.createPreflight_eq s₁.ctx.account value s₁.fork.schedule.stackDepthLimit (s₁.ctx.depth + 1) hSafe').symm
      rw [hPreflightEq]
      by_cases hPre : (decide ((s₁.world.getAccount s₁.ctx.account).balance < value) ||
          (s₁.world.getAccount s₁.ctx.account).nonce == 2^64-1 ||
          decide (s₁.fork.schedule.stackDepthLimit < s₁.ctx.depth + 1)) = true
      · simp only [hPre, ↓reduceIte] at h₁
        rw [bind_modify_step, stateT_pure_eq] at h₁
        cases h₁
      · simp only [hPre, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
        cases hReq : address.lookup s₁.fork with
        | none =>
          simp [hReq, Exec.required, Exec.unsupported, stateT_throw_eq] at h₁
        | some addrStr =>
          simp only [hReq, Exec.required, pure_bind] at h₁ ⊢
          rw [bind_modify_step] at h₁ ⊢
          let target := Exec.Address.decode addrStr
          have hAliveEq : s₂.world.isAlive target = s₁.world.isAlive target :=
            (hSim.world_sim.isAlive_eq target).symm
          have hDeplEq : s₂.world.accountDeployable target = s₁.world.accountDeployable target :=
            (hSim.world_sim.accountDeployable_eq target).symm
          dsimp only [target] at hAliveEq hDeplEq
          rw [hAliveEq, hDeplEq]
          let s₁_2 : Exec.Machine := { s₁_1 with world := s₁_1.world.warmAddress target }
          let s₂_2 : Exec.Machine := { s₂_1 with world := s₂_1.world.warmAddress target }
          have hSim2 : ExecSim sender s₁_2 s₂_2 :=
            ⟨hSim1.fork_eq, hSim1.ctx_eq, hSim1.world_sim.warmAddress_preserves target,
              hSim1.live_stack_le, hSim1.phase_eq, hSim1.sites_eq,
              hSim1.branches_eq, hSim1.frames_size_eq⟩
          obtain ⟨⟨⟩, s₁_3, hCostSt1, h₁⟩ := bind_do_ok h₁
          rw [stateT_run_eq, bind_running_step] at h₁
          by_cases hNotRun3 : (!s₁_3.ctx.outcome.isNone) = true
          · simp only [hNotRun3, ↓reduceIte, stateT_pure_eq] at h₁
            cases h₁
          · have hOut3 : s₁_3.ctx.outcome = none := by
              cases ho : s₁_3.ctx.outcome
              · rfl
              · rw [ho] at hNotRun3; contradiction
            have hNoHalt3 : s₁_3.ctx.outcome ≠ some .halt := by simp [hOut3]
            obtain ⟨s₂_3, hCostSt2, hSim3⟩ := cost_execSim hSim2 hCostSt1 hNoHalt3
            dsimp only [s₂_2, target] at hCostSt2
            rw [bind_do_step hCostSt2]
            rw [stateT_run_eq, bind_running_step, ← hSim3.ctx_eq]
            simp only [hNotRun3, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
            rw [bind_modify_step] at h₁ ⊢
            by_cases hColl : (!s₁.world.accountDeployable (Exec.Address.decode addrStr)) = true
            · simp only [hColl, ↓reduceIte] at h₁
              rw [bind_get_step] at h₁
              obtain ⟨⟨⟩, s₁_coll, hcColl, h₁⟩ := bind_do_ok h₁
              simp only [stateT_run_eq, stateT_pure_eq] at h₁
              cases h₁
            · simp only [hColl, Bool.false_eq_true, ↓reduceIte] at h₁ ⊢
              rw [bind_get_step, bind_get_step] at h₁ ⊢
              let s₁_4 : Exec.Machine :=
                { s₁_3 with world := Exec.increment s₁_3.world s₁_3.ctx.account, ctx := { s₁_3.ctx with returnLen := 0 } }
              let s₂_4 : Exec.Machine :=
                { s₂_3 with world := Exec.increment s₂_3.world s₂_3.ctx.account, ctx := { s₂_3.ctx with returnLen := 0 } }
              have hSim4 : ExecSim sender s₁_4 s₂_4 := by
                refine ⟨hSim3.fork_eq, by simp [s₁_4, s₂_4, hSim3.ctx_eq], ?_,
                  hSim3.live_stack_le, hSim3.phase_eq, hSim3.sites_eq,
                  hSim3.branches_eq, hSim3.frames_size_eq⟩
                dsimp only [s₁_4, s₂_4]
                rw [← hSim3.ctx_eq]
                exact hSim3.world_sim.increment_preserves _
              have hAcc4 : s₁_4.ctx.account = s₁.ctx.account := by
                have h0 : s₁_0.ctx.outcome = none := by
                  cases ho : s₁.ctx.outcome with
                  | none => rfl
                  | some o =>
                    simp only [Exec.cost, stateT_run_eq, bind_running_step, ho,
                      Option.isNone, Bool.false_eq_true, ↓reduceIte, stateT_pure_eq,
                      Except.ok.injEq, Prod.mk.injEq] at hCost1
                    have hEqOut : s₁_1.ctx.outcome = some o := by rw [← hCost1.2]; exact ho
                    rw [hOut1] at hEqOut
                    cases hEqOut
                have h1 : s₁_1.ctx = s₁_0.ctx :=
                  (cost_exec_only_gas hCost1 h0 hNoHalt1).2.2.2.1
                have h3 : s₁_3.ctx = s₁_2.ctx :=
                  (cost_state_only_gas hCostSt1 hOut1 hNoHalt3).2.2.1
                dsimp [s₁_4, s₁_2, s₁_0] at *
                rw [h3, h1]
              obtain ⟨⟨⟩, s₁_ct, hCT₁, h₁⟩ := bind_do_ok h₁
              have hSafeCT : value = 0 ∨ s₁_4.ctx.account ≠ sender ∨
                  value ≤ (s₂_4.world.getAccount s₁_4.ctx.account).balance := by
                rw [hAcc4]
                rcases hSafe' with h0 | hne
                · exact Or.inl h0
                · exact Or.inr (Or.inl hne)
              obtain ⟨hCT₂, rfl⟩ := checkTransfer_execSim hSim4 hSafeCT hCT₁
              dsimp only [s₁_4, s₂_4] at hCT₂
              rw [← hSim3.ctx_eq] at hCT₂ ⊢
              rw [bind_do_step hCT₂]
              obtain ⟨⟨⟩, s₁_5, hSp₁, h₁⟩ := bind_do_ok h₁
              obtain ⟨s₂_5, hSp₂, hSim5⟩ := meterOp_spawnCreate_execSim hSim4 hSp₁
              dsimp only [s₂_4] at hSp₂
              rw [← hSim3.ctx_eq] at hSp₂
              rw [stateT_run_eq, bind_do_step hSp₂]
              rw [stateT_run_eq, bind_modify_step, bind_modify_step, stateT_pure_eq] at h₁ ⊢
              simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h₁ ⊢
              rcases h₁ with ⟨⟨rfl, rfl, rfl⟩, rfl⟩
              refine ⟨(Exec.increment s₂_3.world s₁_3.ctx.account).snapshot, _, ⟨⟨rfl, rfl, rfl⟩, rfl⟩, ?_, rfl⟩
              have hMovEq : CommittedEffects.movement s₂_5.fork s₂_5.world s₁_3.ctx.account target value =
                  CommittedEffects.movement s₁_5.fork s₁_5.world s₁_3.ctx.account target value := by
                rw [← hSim5.fork_eq]
                exact (hSim5.world_sim.movement_eq _ _ _ _).symm
              refine ⟨hSim5.fork_eq, by dsimp only; rw [hMovEq], ?_,
                hSim5.live_stack_le, hSim5.phase_eq,
                by simp [hSim5.sites_eq], hSim5.branches_eq, hSim5.frames_size_eq⟩
              exact ((((hSim5.world_sim.clearStorage_preserves target).markCreated_preserves
                target).increment_preserves target).transfer_preserves s₁_3.ctx.account target value)

end EvmGasSemantics.Spec
