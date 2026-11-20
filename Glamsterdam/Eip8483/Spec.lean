import Glamsterdam.Gloas7732.Spec

namespace Glamsterdam.Eip8483.Spec

open Glamsterdam.Gloas7732.Spec (Builder)
open Glamsterdam.Common.MetaSpec

/-- Decoded execution-layer request. The queue carries no registry index. -/
structure Request where
  pubkey : Nat
  sourceAddress : Nat
  material : Nat

/-- The observation of the draft's list of unique (pubkey, material) pairs. -/
abbrev Registrations := Nat → Option Nat

/-- Look up the current owner, using the first matching builder as in the draft. -/
def ownerAtProcessing (builders : List Builder) (key : Nat) : Option Nat :=
  (builders.find? (fun b => b.pubkey == key)).map Builder.executionAddress

@[export glamsterdam_pq_builder_authorized]
def authorized (owner : Option Nat) (sender : Nat) : Bool :=
  owner == some sender

def authorizationGate : MetaGateSpec (Option Nat × Nat) (fun p => p.1 = some p.2) where
  gate p := authorized p.1 p.2
  sound := by simp [authorized]
  complete := by simp [authorized]
  posWitness := (some 10, 10)
  negWitness := (none, 10)
  nonVacuous := rfl
  tight := rfl

/-- Use the registry at dequeue. Both append and overwrite have this keyed observation. -/
def process (builders : List Builder) (regs : Registrations) (request : Request) : Registrations :=
  if authorized (ownerAtProcessing builders request.pubkey) request.sourceAddress then
    fun key => if key = request.pubkey then some request.material else regs key
  else regs

/-- **Authorized registration**

*Natural property.* The current owner can set registration material for its builder key.

*Formal statement.* When the registry lookup returns the request’s source address, the result at `r.pubkey` is `some r.material`.
-/
theorem authorized_write (builders : List Builder) (regs : Registrations) (r : Request)
    (h : ownerAtProcessing builders r.pubkey = some r.sourceAddress) :
    process builders regs r r.pubkey = some r.material := by
  simp [process, authorized, h]

/-- **Unauthorized request**

*Natural property.* An absent builder key or a source address that does not match the current owner leaves every registration unchanged.

*Formal statement.* If the lookup differs from `some r.sourceAddress`, then `process builders regs r = regs`.
-/
theorem unauthorized_unchanged (builders : List Builder) (regs : Registrations) (r : Request)
    (h : ownerAtProcessing builders r.pubkey ≠ some r.sourceAddress) :
    process builders regs r = regs := by
  simp [process, authorized, h]

/-- **Isolation between builder keys**

*Natural property.* A request for one key preserves the registration at every other key.

*Formal statement.* For every `key ≠ r.pubkey`, the result at `key` equals `regs key`.
-/
theorem other_key_unchanged (builders : List Builder) (regs : Registrations) (r : Request)
    (key : Nat) (h : key ≠ r.pubkey) : process builders regs r key = regs key := by
  unfold process
  split <;> simp [h]

/-- **Registration isolation across index reuse**

*Natural property.* A queued request for a former occupant preserves the replacement builder’s registration when their public keys differ.

*Formal statement.* If index `i` held `old` and the request names `old.pubkey ≠ newBuilder.pubkey`, processing after `before.set i newBuilder` leaves the value at `newBuilder.pubkey` equal to `regs newBuilder.pubkey`.
-/
theorem delayed_registration_after_reuse (before : List Builder) (i : Nat) (old newBuilder : Builder)
    (regs : Registrations) (r : Request) (_occupied : before[i]? = some old)
    (queuedFor : r.pubkey = old.pubkey) (distinct : old.pubkey ≠ newBuilder.pubkey) :
    process (before.set i newBuilder) regs r newBuilder.pubkey = regs newBuilder.pubkey :=
  other_key_unchanged _ _ _ _ (queuedFor ▸ Ne.symm distinct)

private def alice : Builder :=
  { pubkey := 1, executionAddress := 10, balance := 0, depositEpoch := 0, withdrawableEpoch := 1 }

private def queued : Request := ⟨1, 10, 77⟩

/-- Alice succeeds before replacement. After index reuse, Bob's own material persists. -/
example : process [alice] (fun _ => none) queued 1 = some 77 ∧
    process ([alice].set 0 { alice with pubkey := 2 }) (fun _ => some 9) queued 2 = some 9 := by
  decide

/-- Same-key re-entry preserves existing material, rejects the old execution address,
and permits the new owner to replace the material. -/
example : let builders := [ { alice with executionAddress := 20 } ]
          let regs := process [alice] (fun _ => none) queued
          process builders regs { queued with material := 4 } 1 = some 77 ∧
          process builders regs { queued with sourceAddress := 20, material := 4 } 1 = some 4 := by
  decide

/-- Mutation: resolve a cached queue-time index at dequeue and use its occupant's key.
Keeping the sender address equal isolates the index/key bug from authorization. -/
def cachedIndexRefuter : WitnessRefuter Builder (Option Nat)
    (fun occupant result => occupant.pubkey ≠ queued.pubkey → result = none) where
  reference occupant := process [occupant] (fun _ => none) queued occupant.pubkey
  mutant occupant := process [occupant] (fun _ => none)
    { queued with pubkey := occupant.pubkey } occupant.pubkey
  ref_sound occupant := other_key_unchanged _ _ _ _
  killWitness := { alice with pubkey := 2 }
  mutant_refuted := by decide

end Glamsterdam.Eip8483.Spec
