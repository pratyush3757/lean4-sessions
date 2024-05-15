/-
Homework
-/

/-
Convert all term style proofs from propositional logic in the previous
lecture into tactic style proofs.
-/

def Even (n : Nat) := ∃k, n = 2 * k
def Odd  (n : Nat) := ∃k, n = 2 * k + 1

theorem succ_even_odd {n : Nat} : Even n → Odd (n+1) := by
  intro hn
  have ⟨k, hk⟩ := hn
  apply Exists.intro k
  rw [hk]

theorem succ_odd_even {n : Nat} : Odd n → Even (n+1) := by
  intro hn
  have ⟨k, hk⟩ := hn
  apply Exists.intro (k+1)
  rw [hk]
  rfl


theorem succ_succ_even_even {n : Nat} : Even n → Even (n+2) := by
  intro h
  have ⟨_, _⟩ := h
  apply succ_odd_even
  apply succ_even_odd
  exact h

/-
State and prove that n is Odd implies n+2 is odd.
-/
theorem succ_succ_odd_odd {n : Nat} : Odd n → Odd (n+2) := by
  intro h
  have ⟨_, _⟩ := h
  apply succ_even_odd
  apply succ_odd_even
  exact h

/-
Define the proposition k divides n.
-/
def divides (k : Nat) (n : Nat) := ∃x, k*x = n

/-
Now, prove the following theorem. You may find the following theorems
from lean library helpful. Read and understand what they are.
-/
#check Nat.add_mul
#check Nat.mul_add

theorem divides_sum {k n m : Nat} :
  divides k n ∧ divides k m → divides k (n+m) := by
  intro h
  have ⟨hk_div_n, hk_div_m⟩ := h
  have ⟨x, hx⟩ := hk_div_n
  have ⟨y, hy⟩ := hk_div_m
  apply Exists.intro (x+y)
  rewrite [Nat.mul_add]
  rewrite [hx]
  rewrite [hy]
  rfl

/-
This should be tricky without knowing a tactic we haven't seen.
-/
example : ¬(divides 3 5) := sorry
