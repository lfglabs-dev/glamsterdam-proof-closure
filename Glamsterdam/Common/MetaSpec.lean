/-
  Glamsterdam.Common.MetaSpec: Layer I Meta-Specifications and Universal Combinators
  Zero `sorry`, zero `native_decide`, zero custom `axiom`.
  Provides:
  - `Costed`, `MetaGateSpec`, `MetaAlgorithmSpec`
  - `ObservationalProj` and `FrameInvariant` (non-interference combinator for Frame Theorems)
  - `WitnessRefuter` (mutation kill-line combinator proving 1-line mutants violate the spec)
-/
namespace Glamsterdam.Common.MetaSpec

structure Costed (α : Type) where
  val : α
  steps : Nat
  deriving Repr, DecidableEq, BEq

structure MetaGateSpec (Input : Type) (Safe : Input → Prop) where
  gate : Input → Bool
  sound : ∀ x, gate x = true → Safe x
  complete : ∀ x, Safe x → gate x = true
  posWitness : Input
  negWitness : Input
  nonVacuous : gate posWitness = true
  tight : gate negWitness = false

theorem MetaGateSpec.iff_safe {Input : Type} {Safe : Input → Prop}
    (M : MetaGateSpec Input Safe) (x : Input) :
    M.gate x = true ↔ Safe x := ⟨M.sound x, M.complete x⟩

theorem MetaGateSpec.pos_ne_neg {Input : Type} {Safe : Input → Prop}
    (M : MetaGateSpec Input Safe) :
    M.posWitness ≠ M.negWitness := fun h => by simpa [h, M.tight] using M.nonVacuous

structure MetaAlgorithmSpec (Input Output : Type) where
  fast : Input → Costed Output
  oracle : Input → Output
  stepBound : Input → Nat
  equiv : ∀ x, (fast x).val = oracle x
  bounded : ∀ x, (fast x).steps ≤ stepBound x

theorem MetaAlgorithmSpec.sound_and_bounded {Input Output : Type}
    (A : MetaAlgorithmSpec Input Output) (x : Input) :
    (A.fast x).val = A.oracle x ∧ (A.fast x).steps ≤ A.stepBound x :=
  ⟨A.equiv x, A.bounded x⟩

structure FrameInvariant (State Op : Type) (Proj : Type) where
  project : State → Proj
  step : State → Op → State
  preserved : ∀ (s : State) (op : Op), project (step s op) = project s

theorem FrameInvariant.preserved_list {State Op Proj : Type}
    (F : FrameInvariant State Op Proj) (s : State) (ops : List Op) :
    F.project (ops.foldl F.step s) = F.project s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => simpa [List.foldl, F.preserved s op] using ih (F.step s op)

structure WitnessRefuter (Input Output : Type) (Valid : Input → Output → Prop) where
  reference : Input → Output
  mutant : Input → Output
  ref_sound : ∀ x, Valid x (reference x)
  killWitness : Input
  mutant_refuted : ¬ Valid killWitness (mutant killWitness)

theorem WitnessRefuter.mutant_ne_reference {Input Output : Type}
    {Valid : Input → Output → Prop} (W : WitnessRefuter Input Output Valid) :
    W.mutant W.killWitness ≠ W.reference W.killWitness := by
  intro h
  have h_valid := W.ref_sound W.killWitness
  rw [← h] at h_valid
  exact W.mutant_refuted h_valid

end Glamsterdam.Common.MetaSpec
