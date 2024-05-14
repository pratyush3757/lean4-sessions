#check Classical.em

example (p : Prop) : ¬¬p → p :=
  fun h => Or.elim (Classical.em p)
                    (id)
                    (fun hnp => False.elim (h hnp))

example (p : Prop) : ¬¬p → p :=
  Or.elim (Classical.em p)
          (fun hp => fun _ => hp)
          (fun hnp => fun hnnp => False.elim (hnnp hnp))

/- Tactics -/

example (p : Prop) : p → p := by
  intro hp
  exact hp

example (p q : Prop) : p → q → p := by
  intro hp _
  exact hp

example (p : Prop) : p → p ∧ p := by
  intro hp
  apply And.intro /- or `constructor` -/
  { exact hp }
  { exact hp }

example (p : Prop) : p → p ∧ p := by
  intro hp
  apply And.intro /- or `constructor` -/
  . exact hp
  . exact hp

example (p q r : Prop) : (p → q) → (p → r) → p → q ∧ r := by
  intro hp_implies_q hp_implies_r hp
  apply And.intro /- or `constructor` -/
  . exact (hp_implies_q hp)
  . exact (hp_implies_r hp)

example (p q r : Prop) : (p → q) → (p → r) → p → q ∧ r := by
  intro hp_implies_q hp_implies_r hp
  apply And.intro /- or `constructor` -/
  . specialize hp_implies_q hp
    assumption /- or `exact hp_implies_q` -/
  . specialize hp_implies_r hp
    exact hp_implies_r

example (p : Prop) : p → p ∨ p := by
  intro hp
  apply Or.inl /- or `left` -/
  . exact hp

example (p q : Prop) : (¬q → ¬p) → (p → q) := by
  intro hnq_implies_np hp
  have emq := Classical.em q
  cases emq
  case inl hq => exact hq
  case inr hnq => specialize hnq_implies_np hnq; contradiction

example (p q : Prop) : (p → q) → (¬q → ¬p) := by
  intro hp_implies_q hnq hp
  specialize hp_implies_q hp; contradiction

/- Same proof in Term style -/
example (p q : Prop) : (p → q) → (¬q → ¬p) :=
  fun hp_implies_q => fun hnq => fun hp => hnq (hp_implies_q hp)

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro hpq
  cases hpq
  case inl hp => right ; exact hp
  case inr hq => left ; exact hq


/- 3 ways to prove the same thing -/
example (p q : Prop) : (p → q) → (p → (p → q)) := by
  intro hpq hp _
  specialize hpq hp /- Change the hypthesis -/
  exact hpq

example (p q : Prop) : (p → q) → (p → (p → q)) := by
  intro hpq hp _
  apply hpq /- Change the goal -/
  exact hp

example (p q : Prop) : (p → q) → (p → (p → q)) := by
  intro hpq _  /- Collect only what you need for proof -/
  exact hpq


def Even (n : Nat) := ∃k, n = 2 * k
def Odd (n : Nat) := ∃k, n = (2 * k) + 1

#check Exists.intro

theorem zero_even : Even 0 :=
  Exists.intro 0 (Eq.symm (Nat.mul_zero 2))

theorem zero_even' : Even 0 :=
  Exists.intro 0 (by decide)

theorem one_odd : Odd 1 :=
  Exists.intro 0 (by decide)

theorem succ_even_odd {n : Nat} : Even n → Odd (n + 1) := by
  intro hn
  have ⟨k , hk⟩ := hn
  apply Exists.intro k
  rw [hk]

theorem one_odd' : Odd 1 :=
  succ_even_odd zero_even

theorem succ_odd_even {n : Nat} : Odd n → Even (n + 1) := by
  intro hn
  have ⟨k , hk⟩ := hn
  apply Exists.intro (k+1)
  rw [hk]
  rfl
