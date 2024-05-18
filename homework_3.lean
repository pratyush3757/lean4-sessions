/-
Homework
-/

/-
Define exclusive OR connective for propositions.
-/
def XOR (p q : Prop) := (p ∧ ¬q) ∨ (¬p ∧ q)

/-
The following can be proved using theorems we have proved or similar.
-/
theorem even_xor_odd {n : Nat} : XOR (Even n) (Odd n) := by
  induction n
  case zero => 
    left
    have heven := zero_even
    constructor
    . exact heven
    . apply even_not_odd ; exact heven
  case succ n ihn =>
    cases ihn
    case inl heno =>
      have ⟨he, _⟩ := heno
      have ho_n1 := succ_even_odd he
      right
      constructor
      . apply odd_not_even ; exact ho_n1
      . exact ho_n1
    case inr hneo =>
      have ⟨_, ho⟩ := hneo
      have he_n1 := succ_odd_even ho
      left
      constructor
      . exact he_n1
      . apply even_not_odd ; exact he_n1

/-
Prove that every natural number can be written as the product 
of a power of two and an odd number.
-/
theorem nat_pow_two_odd (n : Nat) : ∃k m, Odd m ∧ n+1 = 2^k * m := by
  apply Nat.caseStrongInductionOn n -- See the generated cases in lean.
  sorry

theorem alice01 : Alice 0 1 := sorry

theorem bob11 : Bob 1 1 := sorry

/-
A two player game that starts with a number n. Alice and Bob take
turns subtracting a number less than 10 from remaining. Last person
to subtract wins. Define propositions A n and B n indicating Alice
and Bob's wins on n.

- Prove that if n < 10, then Alice wins.
- Prove Bob 10.
-/