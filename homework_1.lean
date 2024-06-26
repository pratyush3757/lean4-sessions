/-
Homework
-/
example (p q r : Prop) : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
  fun h => And.intro h.left.left (And.intro h.left.right h.right)

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
  fun h => Or.elim h.right
          (fun hq =>
            Or.inl (And.intro h.left hq) /- gives `(p ∧ q) ∨ _ ` -/
          )
          (fun hr =>
            Or.inr (And.intro h.left hr) /- gives ` _ ∨ (p ∧ r)` -/
          )

/- This works for some reason ???? -/
-- example (p q : Prop) : ¬(p ∨ q) → (¬p ∧ ¬q) :=
--   fun h => And.intro 
--           (fun hp => (fun hp => h (Or.inl hp)) hp)
--           (fun hq => (fun hq => h (Or.inr hq)) hq)

/- Simplified version -/
example (p q : Prop) : ¬(p ∨ q) → (¬p ∧ ¬q) :=
  fun h => And.intro
          (fun hp => h (Or.inl hp)) /- gives `p → False` or `¬p` -/
          (fun hq => h (Or.inr hq)) /- gives `q → False` or `¬q` -/

example (p q : Prop) : (¬p ∧ ¬q) → ¬(p ∨ q) :=
  fun h => 
    fun hp_or_hq => 
    /- Maps to `False`. Therefore, `Or.elim` is handy as it means: 
    given (`p ∨ q`, `p → False`, `q → False`) : `False`
    to prove `p → False`, we pass `p` to `h.left`. Same for `q`.
    -/
      (Or.elim (hp_or_hq) 
               (fun hp => h.left hp) 
               (fun hq => h.right hq)
      )

example (p q r : Prop) : ((p ∨ q) → r) → ((p → r) ∧ (q → r)) :=
  fun h => And.intro
            (fun hp => h (Or.inl hp))
            (fun hq => h (Or.inr hq))

/-
You cannot prove this. Try and see the intuition why.

Does law of excluded middle help to prove this?
-/

#check False.elim

/-
`¬¬p → p` means `(p → False → False) → p`
But if False → C can be proved, then it's ex falso
-/
example (p : Prop) : ¬¬p → p :=
  sorry

/-
These, you can prove without law of excluded middle or any other
non-constructive proof technique.
-/

/- `¬¬¬p → ¬p` means `(¬¬p → False) → False`
or `(¬p → False → False) → False`
or `(p → False → False → False) → (p → False)` -/
example (p : Prop) : ¬¬¬p → ¬p :=
  fun hnnnp => 
    fun hp => 
      hnnnp (fun hnp => hnp hp) /- hnnnp takes `¬¬p` or `¬p → False` -/

example (p : Prop) : ¬¬(p ∨ ¬p) :=
  sorry

example (p : Prop) : ¬¬(¬¬p → p) := sorry
