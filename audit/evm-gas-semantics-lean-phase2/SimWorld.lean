import EvmGasSemantics.Spec.Defs

set_option autoImplicit false
namespace EvmGasSemantics.Spec

open EvmGasSemantics

/-- Two path states that agree on all storage, original storage, transient storage, warmth,
created accounts, nonces, code, and non-sender balances (differing only in the sender's balance),
with the post-admission invariant that the sender's nonce is nonzero. -/
structure WorldSim (sender : Nat) (w₁ w₂ : State) : Prop where
  account_ne : ∀ a, a ≠ sender → w₁.getAccount? a = w₂.getAccount? a
  sender_exists : (w₁.getAccount? sender).isSome = (w₂.getAccount? sender).isSome
  sender_nonce : (w₁.getAccount sender).nonce = (w₂.getAccount sender).nonce
  sender_code : (w₁.getAccount sender).code = (w₂.getAccount sender).code
  storage : ∀ a slot, w₁.getStorage a slot = w₂.getStorage a slot
  original : ∀ a slot, w₁.getOriginal a slot = w₂.getOriginal a slot
  created : w₁.createdAccounts = w₂.createdAccounts
  transient : ∀ a slot, w₁.getTransient a slot = w₂.getTransient a slot
  warmAddr : ∀ a, w₁.isAddressWarm a = w₂.isAddressWarm a
  warmSlot : ∀ a slot, w₁.isSlotWarm a slot = w₂.isSlotWarm a slot
  preAccount : ∀ a, a ≠ sender → w₁.getPreAccount? a = w₂.getPreAccount? a
  sender_pre_code : (w₁.getPreAccount? sender).map (·.code) = (w₂.getPreAccount? sender).map (·.code)
  sender_nonce_nz : (w₁.getAccount sender).nonce ≠ 0
  sender_balance_le : (w₂.getAccount sender).balance ≤ (w₁.getAccount sender).balance
  frame_storage : w₁.frame.storage = w₂.frame.storage
  pre_eq : w₁.pre = w₂.pre

private theorem decide_mem_insert_eq {κ : Type} [DecidableEq κ] (k x : κ) (ks₁ ks₂ : List κ)
    (h : decide (x ∈ ks₁) = decide (x ∈ ks₂)) :
    decide (x ∈ State.insert k ks₁) = decide (x ∈ State.insert k ks₂) := by
  have hm (ks : List κ) : (x ∈ State.insert k ks) ↔ (x = k ∨ x ∈ ks) := by
    unfold State.insert
    split
    · constructor
      · intro hx; exact Or.inr hx
      · rintro (rfl | hx) <;> assumption
    · simp
  simp only [decide_eq_decide] at h ⊢
  rw [hm, hm, h]

private theorem read_filter_ne_addr (entries : State.Table (Nat × Nat) Nat) (a x y fb : Nat) :
    State.read (entries.filter fun entry => entry.1.1 != a) (x, y) fb =
      if x = a then fb else State.read entries (x, y) fb := by
  induction entries with
  | nil => simp [State.read]
  | cons hd tl ih =>
    rcases hd with ⟨⟨ka, ks⟩, v⟩
    by_cases hka : ka = a
    · subst hka
      simp only [List.filter, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ih, State.read]
      by_cases hx : x = ka
      · subst hx; simp
      · simp [hx]
    · have hne : (ka != a) = true := bne_iff_ne.mpr hka
      simp only [List.filter, hne, ↓reduceIte, State.read, ih]
      by_cases hx : x = a
      · subst hx
        have hxk : (x, y) ≠ (ka, ks) := by intro heq; cases heq; exact hka rfl
        simp [hxk]
      · simp [hx]

theorem WorldSim.getStorageOriginal_eq {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a slot : Nat) :
    w₁.getStorageOriginal a slot = w₂.getStorageOriginal a slot := by
  simp [State.getStorageOriginal, State.isCreated, h.created, h.original]

theorem WorldSim.accountExists_eq {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) :
    w₁.accountExists a = w₂.accountExists a := by
  unfold State.accountExists
  by_cases q : a = sender
  · subst a; exact h.sender_exists
  · simpa [State.getAccount?] using congrArg Option.isSome (h.account_ne a q)

theorem WorldSim.accountDeployable_eq {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) :
    w₁.accountDeployable a = w₂.accountDeployable a := by
  by_cases q : a = sender
  · subst a; simp [State.accountDeployable, h.sender_nonce, h.sender_code]
  · have := h.account_ne a q
    simp [State.accountDeployable, State.getAccount, this]

theorem WorldSim.code_eq {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) :
    (w₁.getAccount a).code = (w₂.getAccount a).code := by
  by_cases q : a = sender
  · subst a; exact h.sender_code
  · have e : w₁.getAccount a = w₂.getAccount a := by
      simp only [State.getAccount]; rw [h.account_ne a q]
    exact congrArg State.Account.code e

theorem WorldSim.nonce_eq {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) :
    (w₁.getAccount a).nonce = (w₂.getAccount a).nonce := by
  by_cases q : a = sender
  · subst a; exact h.sender_nonce
  · have e : w₁.getAccount a = w₂.getAccount a := by
      simp only [State.getAccount]; rw [h.account_ne a q]
    exact congrArg State.Account.nonce e

theorem WorldSim.isCreated_eq {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) :
    w₁.isCreated a = w₂.isCreated a := by
  simp [State.isCreated, h.created]

theorem WorldSim.warmAddress_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) :
    WorldSim sender (w₁.warmAddress a) (w₂.warmAddress a) := by
  refine ⟨h.account_ne, h.sender_exists, h.sender_nonce, h.sender_code, h.storage, h.original,
    h.created, h.transient, ?_, h.warmSlot, h.preAccount, h.sender_pre_code,
    h.sender_nonce_nz, h.sender_balance_le, h.frame_storage, h.pre_eq⟩
  intro x
  exact decide_mem_insert_eq a x _ _ (h.warmAddr x)

theorem WorldSim.warmSlot_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a slot : Nat) :
    WorldSim sender (w₁.warmSlot a slot) (w₂.warmSlot a slot) := by
  refine ⟨h.account_ne, h.sender_exists, h.sender_nonce, h.sender_code, h.storage, h.original,
    h.created, h.transient, h.warmAddr, ?_, h.preAccount, h.sender_pre_code,
    h.sender_nonce_nz, h.sender_balance_le, h.frame_storage, h.pre_eq⟩
  intro x y
  exact decide_mem_insert_eq (a, slot) (x, y) _ _ (h.warmSlot x y)

theorem WorldSim.setStorage_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a slot val : Nat) :
    WorldSim sender (w₁.setStorage a slot val) (w₂.setStorage a slot val) := by
  refine ⟨h.account_ne, h.sender_exists, h.sender_nonce, h.sender_code, ?_, h.original,
    h.created, h.transient, h.warmAddr, h.warmSlot, h.preAccount, h.sender_pre_code,
    h.sender_nonce_nz, h.sender_balance_le, by simp [State.setStorage, h.frame_storage], h.pre_eq⟩
  intro x y
  unfold State.setStorage State.getStorage
  dsimp [State.read]
  split
  · rfl
  · exact h.storage x y

theorem WorldSim.setTransient_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a slot val : Nat) :
    WorldSim sender (w₁.setTransient a slot val) (w₂.setTransient a slot val) := by
  refine ⟨h.account_ne, h.sender_exists, h.sender_nonce, h.sender_code, h.storage, h.original,
    h.created, ?_, h.warmAddr, h.warmSlot, h.preAccount, h.sender_pre_code,
    h.sender_nonce_nz, h.sender_balance_le, h.frame_storage, h.pre_eq⟩
  intro x y
  unfold State.setTransient State.getTransient
  dsimp [State.read]
  split
  · rfl
  · exact h.transient x y

theorem WorldSim.markCreated_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) :
    WorldSim sender (w₁.markCreated a) (w₂.markCreated a) := by
  refine ⟨h.account_ne, h.sender_exists, h.sender_nonce, h.sender_code, h.storage, h.original,
    ?_, h.transient, h.warmAddr, h.warmSlot, h.preAccount, h.sender_pre_code,
    h.sender_nonce_nz, h.sender_balance_le, h.frame_storage, h.pre_eq⟩
  simp [State.markCreated, State.insert, h.created]

theorem WorldSim.clearStorage_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) :
    WorldSim sender (w₁.clearStorage a) (w₂.clearStorage a) := by
  refine ⟨h.account_ne, h.sender_exists, h.sender_nonce, h.sender_code, ?_, h.original,
    h.created, h.transient, h.warmAddr, h.warmSlot, h.preAccount, h.sender_pre_code,
    h.sender_nonce_nz, h.sender_balance_le, by simp [State.clearStorage, h.frame_storage], h.pre_eq⟩
  intro x y
  unfold State.clearStorage State.getStorage
  dsimp
  rw [read_filter_ne_addr, read_filter_ne_addr]
  by_cases hx : x = a
  · subst hx
    have hmem₁ : x ∈ State.insert x w₁.frame.clearedStorage := by
      unfold State.insert; split <;> simp_all
    have hmem₂ : x ∈ State.insert x w₂.frame.clearedStorage := by
      unfold State.insert; split <;> simp_all
    simp [hmem₁, hmem₂]
  · have hmem₁ : (x ∈ State.insert a w₁.frame.clearedStorage) ↔ (x ∈ w₁.frame.clearedStorage) := by
      unfold State.insert; split <;> simp_all [hx]
    have hmem₂ : (x ∈ State.insert a w₂.frame.clearedStorage) ↔ (x ∈ w₂.frame.clearedStorage) := by
      unfold State.insert; split <;> simp_all [hx]
    simp only [hx, ↓reduceIte, hmem₁, hmem₂]
    exact h.storage x y

private theorem getAccount?_setAccount_self (s : State) (a : Nat) (o : Option State.Account) :
    (s.setAccount a o).getAccount? a = o := by
  simp [State.getAccount?, State.setAccount, State.read]

private theorem getAccount?_setAccount_ne (s : State) (a x : Nat) (o : Option State.Account)
    (h : x ≠ a) : (s.setAccount a o).getAccount? x = s.getAccount? x := by
  simp [State.getAccount?, State.getPreAccount?, State.setAccount, State.read, h]

/-- Raw account write: identical off the sender; at the sender, equal existence, nonce, code, nonzero nonce, and ordered balance. -/
theorem WorldSim.setAccount_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) (o₁ o₂ : Option State.Account)
    (hne : a ≠ sender → o₁ = o₂)
    (hs : a = sender → o₁.isSome = o₂.isSome ∧ (o₁.getD {}).nonce = (o₂.getD {}).nonce ∧
      (o₁.getD {}).code = (o₂.getD {}).code ∧ (o₁.getD {}).nonce ≠ 0 ∧
      (o₂.getD {}).balance ≤ (o₁.getD {}).balance) :
    WorldSim sender (w₁.setAccount a o₁) (w₂.setAccount a o₂) := by
  refine ⟨?_, ?_, ?_, ?_, h.storage, h.original, h.created, h.transient, h.warmAddr,
    h.warmSlot, h.preAccount, h.sender_pre_code, ?_, ?_, h.frame_storage, h.pre_eq⟩
  · intro x hx
    by_cases hxa : x = a
    · subst hxa; rw [getAccount?_setAccount_self, getAccount?_setAccount_self, hne hx]
    · rw [getAccount?_setAccount_ne _ _ _ _ hxa, getAccount?_setAccount_ne _ _ _ _ hxa]
      exact h.account_ne x hx
  · by_cases hsa : sender = a
    · subst hsa; rw [getAccount?_setAccount_self, getAccount?_setAccount_self]; exact (hs rfl).1
    · rw [getAccount?_setAccount_ne _ _ _ _ hsa, getAccount?_setAccount_ne _ _ _ _ hsa]
      exact h.sender_exists
  · by_cases hsa : sender = a
    · subst hsa; simp only [State.getAccount]
      rw [getAccount?_setAccount_self, getAccount?_setAccount_self]; exact (hs rfl).2.1
    · simp only [State.getAccount]
      rw [getAccount?_setAccount_ne _ _ _ _ hsa, getAccount?_setAccount_ne _ _ _ _ hsa]
      exact h.sender_nonce
  · by_cases hsa : sender = a
    · subst hsa; simp only [State.getAccount]
      rw [getAccount?_setAccount_self, getAccount?_setAccount_self]; exact (hs rfl).2.2.1
    · simp only [State.getAccount]
      rw [getAccount?_setAccount_ne _ _ _ _ hsa, getAccount?_setAccount_ne _ _ _ _ hsa]
      exact h.sender_code
  · by_cases hsa : sender = a
    · subst hsa; simp only [State.getAccount]
      rw [getAccount?_setAccount_self]; exact (hs rfl).2.2.2.1
    · simp only [State.getAccount]
      rw [getAccount?_setAccount_ne _ _ _ _ hsa]
      exact h.sender_nonce_nz
  · by_cases hsa : sender = a
    · subst hsa; simp only [State.getAccount]
      rw [getAccount?_setAccount_self, getAccount?_setAccount_self]; exact (hs rfl).2.2.2.2
    · simp only [State.getAccount]
      rw [getAccount?_setAccount_ne _ _ _ _ hsa, getAccount?_setAccount_ne _ _ _ _ hsa]
      exact h.sender_balance_le

theorem WorldSim.setAccount_ne_same {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) {a : Nat} (ha : a ≠ sender) (o : Option State.Account) :
    WorldSim sender (w₁.setAccount a o) (w₂.setAccount a o) :=
  h.setAccount_preserves a o o (fun _ => rfl) (fun hs => absurd hs ha)

theorem WorldSim.destroyAccount_ne_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) {a : Nat} (ha : a ≠ sender) :
    WorldSim sender (w₁.destroyAccount a) (w₂.destroyAccount a) :=
  (h.clearStorage_preserves a).setAccount_ne_same ha none

theorem WorldSim.getAccount_ne {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) {a : Nat} (ha : a ≠ sender) :
    w₁.getAccount a = w₂.getAccount a := by
  simp only [State.getAccount]; rw [h.account_ne a ha]

theorem WorldSim.balance_le {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) :
    (w₂.getAccount a).balance ≤ (w₁.getAccount a).balance := by
  by_cases ha : a = sender
  · subst ha; exact h.sender_balance_le
  · rw [h.getAccount_ne ha]; exact Nat.le_refl _

/-- EIP-161 `modify_state`. Off the sender both sides apply `f` to the same account; at the sender
the updated accounts must agree on nonce and code, keep a nonzero nonce, and preserve balance order. -/
theorem WorldSim.modifyAccount_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) (f : State.Account → State.Account)
    (hs : a = sender →
      (f (w₁.getAccount a)).nonce = (f (w₂.getAccount a)).nonce ∧
      (f (w₁.getAccount a)).code = (f (w₂.getAccount a)).code ∧
      (f (w₁.getAccount a)).nonce ≠ 0 ∧
      (f (w₂.getAccount a)).balance ≤ (f (w₁.getAccount a)).balance) :
    WorldSim sender (w₁.modifyAccount a f) (w₂.modifyAccount a f) := by
  by_cases ha : a = sender
  · obtain ⟨hn, hc, hnz₁, hbal⟩ := hs ha
    have hnz₂ : (f (w₂.getAccount a)).nonce ≠ 0 := hn ▸ hnz₁
    have hset := h.setAccount_preserves a (some (f (w₁.getAccount a))) (some (f (w₂.getAccount a)))
      (fun hne => absurd ha hne) (fun _ => ⟨rfl, hn, hc, hnz₁, hbal⟩)
    have he₁ : (f (w₁.getAccount a)).isEmpty = false := by
      have : ((f (w₁.getAccount a)).nonce == 0) = false := by simpa using hnz₁
      simp [State.Account.isEmpty, this]
    have he₂ : (f (w₂.getAccount a)).isEmpty = false := by
      have : ((f (w₂.getAccount a)).nonce == 0) = false := by simpa using hnz₂
      simp [State.Account.isEmpty, this]
    unfold State.modifyAccount
    dsimp only
    simp only [he₁, he₂, Bool.false_eq_true, ↓reduceIte]
    exact hset
  · have e := h.getAccount_ne ha
    unfold State.modifyAccount
    dsimp only
    rw [e]
    split
    · exact (h.setAccount_ne_same ha _).destroyAccount_ne_preserves ha
    · exact h.setAccount_ne_same ha _

theorem WorldSim.modifyAccount_ne_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) {a : Nat} (ha : a ≠ sender) (f : State.Account → State.Account) :
    WorldSim sender (w₁.modifyAccount a f) (w₂.modifyAccount a f) :=
  h.modifyAccount_preserves a f (fun e => absurd e ha)

/-- Both forks' `increment_nonce`: the incremented account is never empty. -/
theorem WorldSim.increment_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) :
    WorldSim sender (Exec.increment w₁ a) (Exec.increment w₂ a) := by
  unfold Exec.increment
  refine h.modifyAccount_preserves a _ fun ha => ?_
  subst ha
  exact ⟨by simp [h.sender_nonce], h.sender_code, by simp, h.sender_balance_le⟩

/-- A code write (`deposit`, delegation) preserves `WorldSim` for any account `a`. -/
theorem WorldSim.modifyAccount_code_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) (k : State.CodeKind) :
    WorldSim sender (w₁.modifyAccount a fun acc => { acc with code := k })
      (w₂.modifyAccount a fun acc => { acc with code := k }) := by
  refine h.modifyAccount_preserves a _ fun ha => ?_
  subst ha
  exact ⟨h.sender_nonce, rfl, h.sender_nonce_nz, h.sender_balance_le⟩

/-- Moving value between any two accounts preserves `WorldSim` (since the sender's nonce is nonzero). -/
theorem WorldSim.moveEther_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (src dst amount : Nat) :
    WorldSim sender (Exec.moveEther w₁ src dst amount) (Exec.moveEther w₂ src dst amount) := by
  unfold Exec.moveEther
  have h' := h.modifyAccount_preserves src (fun a => { a with balance := a.balance - amount })
    (fun hd => by
      subst hd
      have hbal := h.sender_balance_le
      exact ⟨h.sender_nonce, h.sender_code, h.sender_nonce_nz, by dsimp; omega⟩)
  exact h'.modifyAccount_preserves dst (fun a => { a with balance := a.balance + amount })
    (fun hd => by
      subst hd
      have hbal := h'.sender_balance_le
      exact ⟨h'.sender_nonce, h'.sender_code, h'.sender_nonce_nz, by dsimp; omega⟩)

/-- Value transfer between any two accounts preserves `WorldSim`. -/
theorem WorldSim.transfer_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (src dst amount : Nat) :
    WorldSim sender (Exec.transfer w₁ src dst amount) (Exec.transfer w₂ src dst amount) := by
  unfold Exec.transfer
  split
  · exact h
  · exact h.moveEther_preserves src dst amount

/-- `CommittedEffects.movement` agrees on related worlds for any source, target, and amount. -/
theorem WorldSim.movement_eq {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (fork : Fork) (src dst amount : Nat) (touchZero : Bool := false) :
    CommittedEffects.movement fork w₁ src dst amount touchZero =
      CommittedEffects.movement fork w₂ src dst amount touchZero := by
  unfold CommittedEffects.movement
  have hm := h.moveEther_preserves src dst amount
  have hex : ∀ a, w₁.accountExists a = w₂.accountExists a := h.accountExists_eq
  have hmex : ∀ a, (Exec.moveEther w₁ src dst amount).accountExists a =
      (Exec.moveEther w₂ src dst amount).accountExists a := hm.accountExists_eq
  simp only [hex, hmex]

/-- Failed-child rollback: restore each side to a related entry state with the same pre-state;
creation history is retained and must agree. -/
theorem WorldSim.rollback_preserves {sender : Nat} {w₁ w₂ p₁ p₂ : State}
    (h : WorldSim sender w₁ w₂) (hp : WorldSim sender p₁ p₂)
    (hpre₁ : p₁.pre = w₁.pre) (hpre₂ : p₂.pre = w₂.pre) :
    WorldSim sender (w₁.rollback p₁.snapshot) (w₂.rollback p₂.snapshot) := by
  obtain ⟨pre₁, f₁, c₁⟩ := w₁
  obtain ⟨pre₂, f₂, c₂⟩ := w₂
  obtain ⟨q₁, g₁, d₁⟩ := p₁
  obtain ⟨q₂, g₂, d₂⟩ := p₂
  simp only at hpre₁ hpre₂
  subst hpre₁ hpre₂
  exact ⟨hp.account_ne, hp.sender_exists, hp.sender_nonce, hp.sender_code, hp.storage,
    hp.original, h.created, hp.transient, hp.warmAddr, hp.warmSlot, hp.preAccount,
    hp.sender_pre_code, hp.sender_nonce_nz, hp.sender_balance_le, hp.frame_storage, hp.pre_eq⟩

/-- World update of a CALL-family entry (`beginCall`): warm the target and the resolved code
address, then (for CALL) move value. -/
theorem WorldSim.callEntry_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (addr code src dst value : Nat) (isCall : Bool) :
    WorldSim sender
      (if isCall then Exec.transfer ((w₁.warmAddress addr).warmAddress code) src dst value
        else (w₁.warmAddress addr).warmAddress code)
      (if isCall then Exec.transfer ((w₂.warmAddress addr).warmAddress code) src dst value
        else (w₂.warmAddress addr).warmAddress code) := by
  have hw := (h.warmAddress_preserves addr).warmAddress_preserves code
  cases isCall
  · exact hw
  · exact hw.transfer_preserves src dst value

/-- The resolved code target of `beginCall` agrees on related worlds. -/
theorem WorldSim.codeTarget_eq {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) :
    Exec.codeTarget w₁ a = Exec.codeTarget w₂ a := by
  unfold Exec.codeTarget
  rw [h.code_eq a]

/-- World update of a CREATE-family entry (`beginCreate`): warm the target, bump the creator's
nonce, then clear, mark, bump and fund the new account. -/
theorem WorldSim.createEntry_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (creator target value : Nat) :
    WorldSim sender
      (Exec.transfer (Exec.increment (((Exec.increment (w₁.warmAddress target) creator).clearStorage
        target).markCreated target) target) creator target value)
      (Exec.transfer (Exec.increment (((Exec.increment (w₂.warmAddress target) creator).clearStorage
        target).markCreated target) target) creator target value) :=
  ((((h.warmAddress_preserves target).increment_preserves creator).clearStorage_preserves
    target).markCreated_preserves target |>.increment_preserves target).transfer_preserves
      creator target value

/-- EIP-161 liveness agrees on related worlds (since the sender's nonce is nonzero). -/
theorem WorldSim.isAlive_eq {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (a : Nat) :
    w₁.isAlive a = w₂.isAlive a := by
  unfold State.isAlive State.isEmpty
  rw [h.accountExists_eq a]
  by_cases ha : a = sender
  · subst ha
    have hn₁ := h.sender_nonce_nz
    have hn₂ : (w₂.getAccount a).nonce ≠ 0 := h.sender_nonce ▸ hn₁
    have e₁ : ((w₁.getAccount a).nonce == 0) = false := by simpa using hn₁
    have e₂ : ((w₂.getAccount a).nonce == 0) = false := by simpa using hn₂
    simp only [State.Account.isEmpty, e₁, e₂, Bool.and_false, Bool.false_and]
  · rw [h.getAccount_ne ha]

/-- The CALL/CALLCODE insufficient-balance preflight agrees: either the frame account is not the
sender, or no value moves (`NoSenderValueTransfer`). -/
theorem WorldSim.insufficientBalance_eq {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (account value : Nat)
    (hsafe : value = 0 ∨ account ≠ sender) :
    decide ((w₁.getAccount account).balance < value) =
      decide ((w₂.getAccount account).balance < value) := by
  rcases hsafe with h0 | hne
  · subst h0; simp
  · rw [h.getAccount_ne hne]

/-- The CREATE preflight (balance, nonce overflow, depth) agrees on related worlds. -/
theorem WorldSim.createPreflight_eq {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (creator value lim depth : Nat)
    (hsafe : value = 0 ∨ creator ≠ sender) :
    (decide ((w₁.getAccount creator).balance < value) ||
        (w₁.getAccount creator).nonce == 2^64-1 || decide (lim < depth)) =
      (decide ((w₂.getAccount creator).balance < value) ||
        (w₂.getAccount creator).nonce == 2^64-1 || decide (lim < depth)) := by
  rw [h.insufficientBalance_eq creator value hsafe, h.nonce_eq creator]

/-- `State.finishFrame` on both sides with the same success flag. -/
theorem WorldSim.finishFrame_preserves {sender : Nat} {w₁ w₂ p₁ p₂ : State}
    (h : WorldSim sender w₁ w₂) (hp : WorldSim sender p₁ p₂)
    (hpre₁ : p₁.pre = w₁.pre) (hpre₂ : p₂.pre = w₂.pre) (success : Bool) :
    WorldSim sender (w₁.finishFrame p₁.snapshot success) (w₂.finishFrame p₂.snapshot success) := by
  cases success
  · exact h.rollback_preserves hp hpre₁ hpre₂
  · exact h

/-- On a successful child, `State.finishFrame` keeps the child's world, whatever the snapshot. -/
theorem WorldSim.finishFrame_success_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) (saved₁ saved₂ : State.Snapshot) :
    WorldSim sender (w₁.finishFrame saved₁ true) (w₂.finishFrame saved₂ true) := h

theorem WorldSim.refl_of_nonce_nz (sender : Nat) (w : State)
    (hnz : (w.getAccount sender).nonce ≠ 0) : WorldSim sender w w :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl,
    rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, hnz, Nat.le_refl _, rfl, rfl⟩

theorem WorldSim.increment_self_refl (sender : Nat) (w : State) :
    WorldSim sender (Exec.increment w sender) (Exec.increment w sender) := by
  apply WorldSim.refl_of_nonce_nz
  unfold Exec.increment State.modifyAccount
  dsimp only
  have he : ({ (w.getAccount sender) with nonce := (w.getAccount sender).nonce + 1 } : State.Account).isEmpty = false := by
    simp [State.Account.isEmpty]
  rw [he]
  simp [State.getAccount, getAccount?_setAccount_self]

theorem WorldSim.debit_sender_preserves {sender : Nat} {w₁ w₂ : State}
    (h : WorldSim sender w₁ w₂) {fee₁ fee₂ : Nat} (hFee : fee₁ ≤ fee₂) :
    WorldSim sender
      (w₁.modifyAccount sender fun a => { a with balance := a.balance - fee₁ })
      (w₂.modifyAccount sender fun a => { a with balance := a.balance - fee₂ }) := by
  have hbal := h.sender_balance_le
  have hset := h.setAccount_preserves sender
    (some { (w₁.getAccount sender) with balance := (w₁.getAccount sender).balance - fee₁ })
    (some { (w₂.getAccount sender) with balance := (w₂.getAccount sender).balance - fee₂ })
    (fun hne => absurd rfl hne)
    (fun _ => ⟨rfl, h.sender_nonce, h.sender_code, h.sender_nonce_nz, by dsimp; omega⟩)
  have he₁ : ({ (w₁.getAccount sender) with balance := (w₁.getAccount sender).balance - fee₁ } : State.Account).isEmpty = false := by
    have : ((w₁.getAccount sender).nonce == 0) = false := by simpa using h.sender_nonce_nz
    simp [State.Account.isEmpty, this]
  have he₂ : ({ (w₂.getAccount sender) with balance := (w₂.getAccount sender).balance - fee₂ } : State.Account).isEmpty = false := by
    have hnz₂ : (w₂.getAccount sender).nonce ≠ 0 := h.sender_nonce ▸ h.sender_nonce_nz
    have : ((w₂.getAccount sender).nonce == 0) = false := by simpa using hnz₂
    simp [State.Account.isEmpty, this]
  unfold State.modifyAccount
  dsimp only
  simp only [he₁, he₂, Bool.false_eq_true, ↓reduceIte]
  exact hset

end EvmGasSemantics.Spec
