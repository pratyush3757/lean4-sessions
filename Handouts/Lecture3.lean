/-
2024-05-16
-/
#check Eq.symm

example (h : 2 = 3) : 3 = 2 := by
  apply Eq.symm
  assumption

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
The omega test looks for contradictions in integral (in)equalities.

If it finds one, it solves the goal using it.
-/
example : ¬(Odd 4) := by
  intro ho
  have ⟨_, _⟩ := ho
  omega

theorem even_not_odd {n : Nat} : Even n → ¬Odd n := by
  intro he ho
  have ⟨_, _⟩ := he
  have ⟨_, _⟩ := ho
  omega

theorem odd_not_even {n : Nat} : Odd n → ¬Even n :=  by
  intro ho he
  have ⟨_, _⟩ := ho
  have ⟨_, _⟩ := he
  omega

#check Nat.rec

/-
The `induction` tactic.

For `Nat`, we get two cases.
-/
theorem even_or_odd {n : Nat} : Even n ∨ Odd n := by
  induction n
  case zero => left ; exact zero_even
  case succ n ihn => -- n and ihn are the "previous" n and inductive hypothesis.
    cases ihn
    case inl en => right ; exact succ_even_odd en
    case inr on => left  ; exact succ_odd_even on

def sum : Nat → Nat
  | .zero => 0
  | .succ n => sum n + .succ n

#eval sum 10

#check Nat.add_mul_div_left

/-
We prove a classic example for induction.
-/
theorem sum_formula (n : Nat) : sum n = (n * (n+1)) / 2 := by
  induction n
  case zero => rfl -- `rfl` can see through the definition.
  case succ n ihn =>
    unfold sum
    rw [ihn]
    calc -- A `calc` proof shows step-by-step calculation with each step's proof.
      _ = (n * (n + 1) + 2 * (n + 1)) / 2 := by
        rw [Nat.add_mul_div_left]
        decide
      _ = ((n + 2) * (n + 1)) / 2 := by rw [Nat.add_mul]
      _ = ((n + 1) * (n + 2)) / 2 := by rw [Nat.mul_comm]

theorem even_mul_nat_even {n m : Nat} (hn : Even n) : Even (n*m) := by
  have ⟨k₁, hk₁⟩ := hn
  unfold Even
  apply Exists.intro (k₁ * m)
  calc
    n * m = 2 * k₁ * m   := by rw [hk₁]
    _     = 2 * (k₁ * m) := by rw [Nat.mul_assoc]

/-
Nim with two heaps.

oooo
oooo

Alice and Bob takes turns picking a heap and taking non-zero number
of coins from the chosen heap. The last player to move wins.
-/

abbrev between (lower what upper : Nat) : Prop :=
  lower ≤ what ∧ what ≤ upper

/-
A mutually recursive definition is needed to define Alice and Bob's
winning condition.
-/
mutual
def Alice : Nat → Nat → Prop
  | n, m =>
    ∃k, between 1 k n ∧ (between 1 k n → Bob (n-k) m)
      ∨ between 1 k m ∧ (between 1 k m → Bob n (m-k))
def Bob : Nat → Nat → Prop
  | n, m =>
    ∀k, (between 1 k n → Alice (n-k) m)
      ∧ (between 1 k m → Alice n (m-k))
end

/-
To prove ∀x : T, p x, write a function
  fun (v : T) => hpv
-/
theorem bob00 : Bob 0 0 := by
  intro k
  constructor
  . intro ; omega
  . intro ; omega

theorem alice10 : Alice 1 0 := by
  apply Exists.intro 1
  left
  constructor
  . decide
  . intro ; exact bob00

/-
Homework
-/

/-
Define exclusive OR connective for propositions.
-/
def XOR (p q : Prop) := True

/-
The following can be proved using theorems we have proved or similar.
-/
theorem even_xor_odd {n : Nat} : XOR (Even n) (Odd n) := by
  sorry

/-
Prove that every natural number can be written as the product 
of a power of two and an odd number.
-/
theorem nat_pow_two_odd (n : Nat) : ∃k m, Odd m ∧ n = 2^k * m := by
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
