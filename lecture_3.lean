def Even (n : Nat) := ∃k, n = 2 * k
def Odd  (n : Nat) := ∃k, n = 2 * k + 1
def divides (k : Nat) (n : Nat) := ∃x, k*x = n

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

example : ¬(divides 3 5) := by
  intro hdiv
  have ⟨k,hk⟩ := hdiv
  omega

theorem even_not_odd {n : Nat} : Even n → ¬Odd n := by
  intro heven hodd
  have ⟨x, hx⟩ := heven
  have ⟨y, hy⟩ := hodd
  omega

theorem odd_not_even {n : Nat} : Odd n → ¬Even n := by
  intro hodd heven
  have ⟨x, hx⟩ := heven
  have ⟨y, hy⟩ := hodd
  omega

#check Nat.rec

theorem even_or_odd {n : Nat} : Even n ∨ Odd n := by
  induction n
  case zero => left ; apply Exists.intro 0 ; decide
  case succ n ihn =>
    cases ihn
    case inl he => right ; exact succ_even_odd he   
    case inr ho => left ; exact succ_odd_even ho

def sum : Nat → Nat
  | .zero => 0
  | .succ n => sum n + .succ n

#eval sum 10

theorem sum_formula (n : Nat) : sum n = (n * (n+1)) / 2 := by
  induction n
  case zero => rfl
  case succ n ihn =>
    unfold sum
    rewrite [ihn]
    calc
      _ = (n * (n + 1) + 2 * (n + 1)) / 2 := by
        rw [Nat.add_mul_div_left]; decide
      _ = ((n + 2) * (n + 1)) / 2 := by rw [Nat.add_mul]
      _ = ((n + 1) * (n + 2)) / 2 := by rw [Nat.mul_comm]

theorem even_mul_nat_even {n m : Nat} (hn : Even n) : Even (n*m) := by
  unfold Even
  have ⟨k, hk⟩ := hn
  calc
    n * m = 2 * k * m := by rw [hk]
  sorry
