/-
Copyright (c) 2026 Verity Labs / LFG Labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Marchand, Verity Audit Team
-/
import Glamsterdam.Common.Prelude

/-!
# Glamsterdam Layer I Meta-Specifications and Universal Anti-Vacuity Combinators

Zero `sorry`, zero `native_decide`, zero custom `axiom`.
Provides the consensus Layer I meta-specification combinators:
1. `Costed`, `MetaGateSpec`, `MetaAlgorithmSpec`
2. `FrameInvariant` & `ExactDeltaSpec` (frame preservation + positive write delta)
3. `WitnessRefuter` & `MutantKillBundle` (multi-mutant kernel refutation matrix)
4. `NonVacuousSpec` (`ReachablePre` + `NonTautPost` constructive witnesses)
5. `OutcomePartitionSpec` (`Iff` error characterization preventing over/under-revert)
6. `AccountingBoundarySpec` (`LedgerConservation` with explicit independent sources/sinks)
7. `OrderIndependence` (commutativity + idempotence for set-fold iterations)
-/

namespace Glamsterdam.Common.MetaSpec

open Glamsterdam.Common.Prelude

/-! ## 1. Core Gate and Algorithm Meta-Specs -/

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

/-! ## 2. Frame Invariants and Exact Delta Specifications -/

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

/-- `ExactDeltaSpec` pairs a `FrameInvariant` (fields outside the write footprint are untouched)
with a positive write characterization (fields inside the write footprint change by `expectedDelta`),
ruling out `noop` implementations. -/
structure ExactDeltaSpec (State Op FrameProj WriteProj : Type) where
  frame : FrameInvariant State Op FrameProj
  readWrite : State → WriteProj
  expectedWrite : State → Op → WriteProj
  delta_exact : ∀ (s : State) (op : Op),
    readWrite (frame.step s op) = expectedWrite s op
  witnessState : State
  witnessOp : Op
  nonTrivialWrite : readWrite (frame.step witnessState witnessOp) ≠ readWrite witnessState

/-! ## 3. Witness Refuters and Multi-Mutant Kill Bundles -/

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

/-- `MutantKillBundle` groups an arithmetic mutant, a field-omission mutant, and an ordering
mutant against a single reference function and specification predicate. -/
structure MutantKillBundle (Input Output : Type) (Valid : Input → Output → Prop) where
  arithMutant : WitnessRefuter Input Output Valid
  fieldMutant : WitnessRefuter Input Output Valid
  orderMutant : WitnessRefuter Input Output Valid

/-! ## 4. Anti-Vacuity (`NonVacuousSpec`), Error Partition (`OutcomePartitionSpec`),
    and Scoped Accounting (`AccountingBoundarySpec`) -/

/-- `NonVacuousSpec` guarantees that a conditional theorem `∀ x, Pre x → Post x (step x)` is:
1. Satisfiable on a concrete success input (`okWitness`),
2. Non-tautological in its postcondition (`nonTautWitness` falsifies `Post`),
3. Sound for all inputs satisfying `Pre`. -/
structure NonVacuousSpec (Input Output : Type)
    (Pre : Input → Prop) (Post : Input → Output → Prop) (step : Input → Output) where
  sound : ∀ x, Pre x → Post x (step x)
  okWitness : Input
  pre_inhabited : Pre okWitness
  badOutputWitness : Output
  post_non_tautological : ¬ Post okWitness badOutputWitness

theorem NonVacuousSpec.step_ne_bad {Input Output : Type}
    {Pre : Input → Prop} {Post : Input → Output → Prop} {step : Input → Output}
    (S : NonVacuousSpec Input Output Pre Post step) :
    step S.okWitness ≠ S.badOutputWitness := by
  intro h
  have h_post := S.sound S.okWitness S.pre_inhabited
  rw [h] at h_post
  exact S.post_non_tautological h_post

/-- `OutcomePartitionSpec` characterizes the exact `iff` error condition of a stateful `SpecM`
operation, preventing implementations that over-revert or under-revert. -/
structure OutcomePartitionSpec (σ ε α : Type) (op : SpecM σ ε α) (ErrCond : σ → Prop) where
  err_iff : ∀ s, (op s).isErr = true ↔ ErrCond s
  ok_iff : ∀ s, (op s).isOk = true ↔ ¬ ErrCond s
  okWitness : σ
  errWitness : σ
  okWitness_valid : (op okWitness).isOk = true
  errWitness_valid : (op errWitness).isErr = true

/-- `AccountingBoundarySpec` enforces a conservation law with explicit, independently defined
`inflow` and `outflow` terms: `measure post + outflow = measure pre + inflow`. -/
structure AccountingBoundarySpec (State Op : Type) where
  step : State → Op → State
  measure : State → Nat
  inflow : State → Op → Nat
  outflow : State → Op → Nat
  conserved : ∀ (s : State) (op : Op),
    measure (step s op) + outflow s op = measure s + inflow s op

/-- `OrderIndependence` proves that folding an operation over a set represented as a `List`
is both idempotent (duplicate elements do not change the result) and commutative (reordering
elements does not change the result). -/
structure OrderIndependence (State Elem : Type) (f : State → Elem → State) where
  idempotent : ∀ (s : State) (x : Elem), f (f s x) x = f s x
  commutative : ∀ (s : State) (x y : Elem), f (f s x) y = f (f s y) x

theorem OrderIndependence.swap_pair {State Elem : Type} {f : State → Elem → State}
    (O : OrderIndependence State Elem f) (s : State) (x y : Elem) :
    [x, y].foldl f s = [y, x].foldl f s :=
  O.commutative s x y

theorem OrderIndependence.dedup_pair {State Elem : Type} {f : State → Elem → State}
    (O : OrderIndependence State Elem f) (s : State) (x : Elem) :
    [x, x].foldl f s = [x].foldl f s :=
  O.idempotent s x

end Glamsterdam.Common.MetaSpec
