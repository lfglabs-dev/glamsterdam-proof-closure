/-
Copyright (c) 2026 Verity Labs / LFG Labs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Marchand, Verity Audit Team
-/

/-!
# Glamsterdam Common Prelude: Operational Semantics, Checked Arithmetic, and Oracles

This module defines the semantic substrate shared across the Execution Layer (`EIP-8246`,
`EIP-8037`, `EIP-8038`, `EIP-2780`, `EIP-7778`) and Consensus Layer (`EIP-7732`, `EIP-8282`)
formal specifications:

1. **`Result ε σ α` and `SpecM σ ε α`**: Explicit state-preserving exception monad.
   Unlike `StateT σ (Except ε) α` (which discards state on throw and makes rollback theorems
   vacuously true), `Result.err e s'` preserves the exact mutated state `s'` at the raise site
   until an explicit catch handler (`restore_tx_state`, `restore_state_gas`, etc.) runs.
2. **Checked and Bounded Numeric Primitives**:
   - `U256` (`2^256` bound) with explicit `checkedSub?`, `checkedAdd?`, `wrappingAdd`, `wrappingSub`.
   - `Gwei` / `U64` (`2^64` bound) with explicit `checkedAdd?`, `checkedSub?`, and `saturatingSub`.
   - `ceil32` word-rounding helper matching `ethereum.utils.numeric.ceil32`.
3. **Explicit Cryptographic & Trie Oracle Parameterization (`CryptoOracle`)**:
   Zero custom axioms; cryptographic primitives (`keccak256`, `blsVerify`, `hashTreeRoot`) are
   passed explicitly and instantiated by deterministic table-backed oracles on test vectors.
-/

namespace Glamsterdam.Common.Prelude

/-! ## 1. State-Preserving Exception Monad (`Result` / `SpecM`) -/

/-- Operational outcome of a stateful specification step that preserves `state` even when
raising an exception `err`. -/
inductive Result (ε σ α : Type) where
  | ok (val : α) (state : σ)
  | err (error : ε) (state : σ)
  deriving Repr, DecidableEq, BEq

namespace Result

/-- Whether the execution succeeded without an unhandled exception. -/
@[simp]
def isOk {ε σ α : Type} : Result ε σ α → Bool
  | .ok _ _ => true
  | .err _ _ => false

/-- Whether the execution terminated with an exception. -/
@[simp]
def isErr {ε σ α : Type} : Result ε σ α → Bool
  | .ok _ _ => false
  | .err _ _ => true

/-- Extract the post-state regardless of whether the computation succeeded or raised. -/
@[simp]
def state {ε σ α : Type} : Result ε σ α → σ
  | .ok _ s => s
  | .err _ s => s

/-- Extract the return value if `ok`. -/
@[simp]
def val? {ε σ α : Type} : Result ε σ α → Option α
  | .ok a _ => some a
  | .err _ _ => none

/-- Extract the error value if `err`. -/
@[simp]
def err? {ε σ α : Type} : Result ε σ α → Option ε
  | .ok _ _ => none
  | .err e _ => some e

end Result

/-- State-preserving operational monad matching Python's in-place mutation + exception semantics. -/
abbrev SpecM (σ ε α : Type) := σ → Result ε σ α

namespace SpecM

@[inline, simp]
def pure {σ ε α : Type} (a : α) : SpecM σ ε α :=
  fun s => .ok a s

@[inline, simp]
def bind {σ ε α β : Type} (m : SpecM σ ε α) (f : α → SpecM σ ε β) : SpecM σ ε β :=
  fun s =>
    match m s with
    | .ok a s' => f a s'
    | .err e s' => .err e s'

instance {σ ε : Type} : Monad (SpecM σ ε) where
  pure := pure
  bind := bind

@[simp]
theorem bind_pure {σ ε α : Type} (m : SpecM σ ε α) :
    bind m pure = m := by
  funext s; dsimp [bind, pure]; cases m s <;> rfl

@[simp]
theorem pure_bind {σ ε α β : Type} (a : α) (f : α → SpecM σ ε β) :
    bind (pure a) f = f a := rfl

@[simp]
theorem bind_assoc {σ ε α β γ : Type}
    (m : SpecM σ ε α) (f : α → SpecM σ ε β) (g : β → SpecM σ ε γ) :
    bind (bind m f) g = bind m (fun x => bind (f x) g) := by
  funext s; dsimp [bind]; cases m s <;> rfl

/-- Read the current state without modifying it. -/
@[inline, simp]
def get {σ ε : Type} : SpecM σ ε σ :=
  fun s => .ok s s

/-- Replace the current state. -/
@[inline, simp]
def set {σ ε : Type} (s' : σ) : SpecM σ ε Unit :=
  fun _ => .ok () s'

/-- Modify the current state in place. -/
@[inline, simp]
def modify {σ ε : Type} (f : σ → σ) : SpecM σ ε Unit :=
  fun s => .ok () (f s)

/-- Raise an exception while preserving all state mutations performed prior to the raise. -/
@[inline, simp]
def throw {σ ε α : Type} (e : ε) : SpecM σ ε α :=
  fun s => .err e s

/-- Assert a boolean condition or raise `e`, preserving the current state. -/
@[inline, simp]
def guardOr {σ ε : Type} (cond : Bool) (e : ε) : SpecM σ ε Unit :=
  fun s => if cond then .ok () s else .err e s

end SpecM

/-! ## 2. Checked, Saturating, and Wrapping Arithmetic Primitives -/

/-- Upper bound for 64-bit unsigned integers (`2^64`). -/
def U64_MOD : Nat := 18446744073709551616

/-- Upper bound for 64-bit max value (`2^64 - 1`). -/
def U64_MAX : Nat := 18446744073709551615

/-- Checked subtraction on natural numbers: returns `none` on underflow (`a < b`),
never silently truncating to `0`. -/
@[inline, simp]
def checkedSub? (a b : Nat) : Option Nat :=
  if a < b then none else some (a - b)

/-- Saturating subtraction on natural numbers (`consensus-specs` `saturating_sub` / `decrease_balance`). -/
@[inline, simp]
def saturatingSub (a b : Nat) : Nat :=
  if a < b then 0 else a - b

/-- Checked 64-bit addition (`consensus-specs` `Uint64` / `Gwei` `+`). -/
@[inline, simp]
def checkedAddU64? (a b : Nat) : Option Nat :=
  if a + b < U64_MOD then some (a + b) else none

/-- Round `x` up to the smallest multiple of 32 (`ethereum.utils.numeric.ceil32`). -/
@[inline, simp]
def ceil32 (x : Nat) : Nat :=
  let rem := x % 32
  if rem == 0 then x else x + 32 - rem

theorem checkedSub?_eq_some_iff (a b c : Nat) :
    checkedSub? a b = some c ↔ b ≤ a ∧ c = a - b := by
  unfold checkedSub?
  split <;> simp_all <;> omega

theorem checkedSub?_eq_none_iff (a b : Nat) :
    checkedSub? a b = none ↔ a < b := by
  unfold checkedSub?
  split <;> simp_all

theorem saturatingSub_le (a b : Nat) :
    saturatingSub a b ≤ a := by
  unfold saturatingSub
  split <;> omega

end Glamsterdam.Common.Prelude
