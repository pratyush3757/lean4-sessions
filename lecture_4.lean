/- Theorem x already proven in homework 1 -/
theorem x (p q r : Prop) : ((p ∨ q) → r) → ((p → r) ∧ (q → r)) := sorry

example (p : Prop) : ¬¬(p ∨ ¬p) :=
  fun hnem => 
    have ⟨h1, h2⟩  := (x p (¬p) False) hnem
    h2 h1

example (p : Prop) : ¬¬(p ∨ ¬p) := by
  intro hnem 
  have ⟨h1, h2⟩  := (x p (¬p) False) hnem
  contradiction
