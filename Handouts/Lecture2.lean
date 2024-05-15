/-
2014-05-14
-/

example (p : Prop) : ¬¬¬p → ¬p :=
  fun hnnnp => fun hp => hnnnp (fun hnp => hnp hp)

/-
Proof of negation: We want to prove ¬p. So we write a function to 
convert a proof of p to False. ¬(Rational sqrt(2))

Proof by contradiction: We want to prove p. So we write a function
to convert a proof of ¬p to False. Constructively, this proves ¬¬p.
-/

#check Classical.em

example (p : Prop) : ¬¬p → p :=
  Or.elim (Classical.em p)
          (fun hp => fun _ => hp)
          (fun hnp => fun hnnp => False.elim (hnnp hnp))

/-
p classical => ¬¬p constructively
¬p classical <=> ¬p constructively
-/

/-
Tactics
-/

example (p : Prop) : p → p := by
  intro hp
  exact hp

example (p q : Prop) : p → q → p := by
  intro hp _
  exact hp

example (p : Prop) : p → p ∧ p := by
  intro hp
  apply And.intro
  . exact hp
  . exact hp

example (p q r : Prop) : (p → q) → (p → r) → p → q ∧ r := by
  intro hpq hpr hp
  apply And.intro
  . specialize hpq hp
    assumption
  . specialize hpr hp
    exact hpr /- Preferred style. -/

example (p : Prop) : p → p ∨ p := by
  intro hp ; apply Or.inl ; exact hp

example (p q : Prop) : (¬q → ¬p) → (p → q) := by
  intro hnqnp hp
  have emq := Classical.em q
  cases emq
  case inl hq => exact hq
  case inr hnq => specialize hnqnp hnq ; contradiction

example (p q : Prop) : (p → q) → (¬q → ¬p) := by
  intro hpq _ hp
  specialize hpq hp
  contradiction

example (p q r : Prop) : (p → q) → (p → r) → p → q ∧ r := by
  intro hpq hpr hp
  constructor
  . specialize hpq hp
    assumption
  . specialize hpr hp
    exact hpr /- Preferred style. -/

example (p : Prop) : p → p ∨ p := by
  intro hp
  left
  exact hp

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro hpq
  cases hpq
  case inl hp => right ; exact hp
  case inr hq => left  ; exact hq

example (p q : Prop) : (p → q) → (p → (p → q)) := by
  intro hpq hp _
  apply hpq
  exact hp

def Even (n : Nat) := ∃k, n = 2 * k
def Odd  (n : Nat) := ∃k, n = 2 * k + 1

#check Exists.intro

theorem zero_even : Even 0 :=
  Exists.intro 0 (by decide)

theorem succ_even_odd {n : Nat} : Even n → Odd (n+1) := by
  intro hn
  have ⟨k, hk⟩ := hn
  apply Exists.intro k
  rw [hk]

theorem one_odd : Odd 1 :=
  succ_even_odd zero_even

theorem succ_odd_even {n : Nat} : Odd n → Even (n+1) := by
  intro hn
  have ⟨k, hk⟩ := hn
  apply Exists.intro (k+1)
  rw [hk]
  rfl

/-
intro
have
specialize
apply
  Say you have theorem t that says: "If h₁, h₂ then t'". Then, apply t
  when you have the goal t', will generate sub-goals h₁, h₂.
decide
  Solves equalities, inequalities etc. with only constants.
contradiction
  Look for contradictions in the hypothesis and finish if found.
rw [h], rewrite [h]
  Say h is a proof of a = b, replace a in goal with b.
rfl
  Use reflexivity
cases h
  Split proof into cases governed by h
exact
  Goal is exactly a hypothesis
assumption
constructor (generate cases for proving AND)
left (Prove OR via left)
right (Prove OR via right)
-/

example : True ∧ (True ∨ False) := by decide

/-
Homework
-/

/-
Convert all term style proofs from propositional logic in the previous
lecture into tactic style proofs.
-/

theorem succ_succ_even_even {n : Nat} : Even n → Even (n+2) := by
  sorry

/-
State and prove that n is Odd implies n+2 is odd.
-/

/-
Define the proposition k divides n.
-/
def divides (k : Nat) (n : Nat) := True

/-
Now, prove the following theorem. You may find the following theorems
from lean library helpful. Read and understand what they are.
-/
#check Nat.add_mul
#check Nat.mul_add

theorem divides_sum {k n m : Nat} :
  divides k n ∧ divides k m → divides k (n+m) := by
  sorry

/-
This should be tricky without knowing a tactic we haven't seen.
-/
example : ¬(divides 3 5) := sorry
