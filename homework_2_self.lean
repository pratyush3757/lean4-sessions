/-
2024-05-15 All previous proofs using tactics
-/

theorem one_eq_one : 1 = 1 := by
  rfl
-- theorem one_eq_one : 1 = 1 := Eq.refl 1


theorem tri : True := True.intro
-- theorem tri : True := True.intro

theorem tri' : True ∧ True := by
  constructor
  . exact tri
  . exact tri
-- And.intro True.intro True.intro

theorem tri'' : True ∧ (True ∧ True) := by
  constructor
  . exact tri
  . exact tri'
-- And.intro True.intro tri'

theorem tri''' : False ∨ True := by
  apply Or.inr
  exact True.intro
-- Or.inr True.intro

theorem tri'''' : True ∨ False := by
  apply Or.inl
  exact True.intro
-- Or.inl True.intro

theorem a : (1 = 1) ∧ (2 = 2) := by
  constructor
  . rfl
  . rfl
-- And.intro (Eq.refl 1) (Eq.refl 2)

theorem b : (1 = 1) ∧ ((2 = 2) ∨ (2 = 3)) := by
  constructor
  . rfl
  . apply Or.inl
    rfl
-- And.intro (Eq.refl 1) (Or.inl (Eq.refl 2))

theorem c : False ∨ (True ∧ (3 = 3)) := by
  apply Or.inr
  constructor
  . exact tri
  . decide
-- Or.inr (And.intro tri (Eq.refl 3))

theorem d : True ∨ True := by
  apply Or.inl
  exact tri
-- Or.inr tri

theorem e : 1 + 1 = 2 := by
  decide
-- Eq.refl (1 + 1)

/-
Can you write a proof for the following?
-- No we cannot as False has no proof
-/
theorem f : False := sorry

theorem iatia (p : Prop) : p → p := by
  intro hp
  exact hp
-- fun hp => hp

example (p q : Prop) : p → q → p := by
  intro hp _
  exact hp
-- fun hp => fun _ => hp

example (p q : Prop) : p → q → q := by
  intro _ hq
  exact hq
-- fun _ => iatia q

/- Another version -/
example (p q : Prop) : p → q → q := by
  intro _
  exact iatia q
-- fun _ => iatia q

example (p : Prop) : p → (p ∨ p) := by
  intro hp
  apply Or.inr
  exact hp
-- fun hp => Or.inl hp

example (p q r : Prop) : (p → q) → (q → r) → (p → r) := by
  intro hpq hqr hp
  specialize hpq hp
  specialize hqr hpq
  exact hqr
-- fun hpq => fun hqr => fun hp => hqr (hpq hp)

example (p q : Prop) : (p ∧ (p → q)) → q := by
  intro h
  have ⟨ hp, hpq ⟩ := h
  specialize hpq hp
  exact hpq
-- fun h => (And.right h) (And.left h)

example (p q r : Prop) : ((p → q) ∧ (p → r)) → (p → (q ∧ r)) := by
  intro h hp
  have ⟨ hpq, hpr ⟩ := h
  constructor
  . specialize hpq hp
    exact hpq
  . specialize hpr hp
    exact hpr
-- fun h => fun hp => And.intro ((And.left h) hp) ((And.right h) hp)

example (p q r s : Prop) : ((p → q) ∧ (r → s) ∧ (p ∨ r)) → (q ∨ s) := by
  intro h
  have ⟨hpq, hrs, hp_or_r⟩ := h
  cases hp_or_r
  case inl hp => specialize hpq hp; exact Or.inl hpq
  case inr hr => specialize hrs hr; exact Or.inr hrs
-- fun h =>
--   Or.elim h.right.right
--           (fun hp => Or.inl (h.left hp))
--           (fun hr => Or.inr (h.right.left hr))

example (p : Prop) : False → p := by
  intro hp
  exact False.elim hp
-- False.elim

/- Second version -/
example (p : Prop) : False → p := by
  intro h
  contradiction
-- False.elim

/- Third version -/
example (p : Prop) : False → p := by
  exact False.elim
-- False.elim

example (p : Prop) : ¬(p ∧ ¬p) := by
  intro h
  have ⟨hp, hnp⟩ := h
  contradiction
-- fun h => h.right h.left

example (p q : Prop) : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  specialize hpq hp
  contradiction
-- fun hpq => fun hnq => fun hp => hnq (hpq hp)

example (p q : Prop) : (p ∧ ¬p) → q := by
  intro h
  have ⟨hp, hnp⟩ := h
  contradiction
-- fun h => False.elim (h.right h.left)

example (p q r : Prop) : (p ∧ q) ∧ r → p ∧ (q ∧ r) := by
  intro h
  have ⟨hpq, hr⟩ := h
  have ⟨hp, hq⟩ := hpq
  constructor
  . exact hp
  . constructor; exact hq; exact hr

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  have ⟨hp, hqr⟩ := h
  cases hqr
  case inl hq => apply Or.inl; exact And.intro hp hq;
  case inr hr => apply Or.inr; exact And.intro hp hr; 

example (p q : Prop) : ¬(p ∨ q) → (¬p ∧ ¬q) := by
  intro h
  constructor
  . intro hp; specialize h (Or.inl hp); exact h
  . intro hq; specialize h (Or.inr hq); exact h

example (p q : Prop) : (¬p ∧ ¬q) → ¬(p ∨ q) := by
  intro h hp_or_q
  have ⟨hnp, hnq⟩ := h
  cases hp_or_q
  case inl hp => contradiction
  case inr hq => contradiction

example (p q r : Prop) : ((p ∨ q) → r) → ((p → r) ∧ (q → r)) := by
  intro h
  constructor
  . intro hp; specialize h (Or.inl hp); exact h
  . intro hq; specialize h (Or.inr hq); exact h

/-
You cannot prove this. Try and see the intuition why.

Does law of excluded middle help to prove this?
-/
example (p : Prop) : ¬¬p → p :=
  sorry

/-
These, you can prove without law of excluded middle or any other
non-constructive proof technique.
-/
example (p : Prop) : ¬¬¬p → ¬p := by
  intro hnnnp hp
  specialize hnnnp (fun hnp => hnp hp)
  exact hnnnp

example (p : Prop) : ¬¬(p ∨ ¬p) := by
  sorry
