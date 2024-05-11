/-
2024-05-11
-/

/-
You can eliminate the `fun` binding by moving parameters beside the
function name.
-/
def fib (n : Nat) : Nat :=
  match n with
    | Nat.zero => 1
    | Nat.succ Nat.zero => 1
    | Nat.succ (Nat.succ n) => fib n + fib (Nat.succ n)

#eval fib 5

/-
To prove an implication `p → q`, you have to write a function that
takes a proof of `p` and produces a proof of `q`.
-/
theorem iatia (p : Prop) : p → p :=
  fun hp => hp

/-
We can use `example` to state unnamed theorems.
-/
example (p q : Prop) : p → q → p :=
  fun hp => fun _ => hp

example (p q : Prop) : p → q → q :=
  fun _ => iatia q

example (p : Prop) : p → (p ∨ p) :=
  fun hp => Or.inl hp

/-
If we have a proof of `p → q` and a proof of `p`, we can combine them
to make a proof of `q`.

The rule is: given `hpq : p → q` and `hp : p`, we have `hpq hp : q`.

A rule that eliminates connectives in hypotheses is called an
elimination rule.
-/
example (p q r : Prop) : (p → q) → (q → r) → (p → r) :=
  fun hpq => fun hqr => fun hp => hqr (hpq hp)

example (p q : Prop) : (p ∧ (p → q)) → q :=
  fun h => (And.right h) (And.left h)

example (p q r : Prop) : ((p → q) ∧ (p → r)) → (p → (q ∧ r)) :=
  fun h => fun hp => And.intro ((And.left h) hp) ((And.right h) hp)

#check Or.elim

/-
The elimination rule for `∨` is called proof by cases.

If `v : p ∨ q` and `v₁ : p → r` and `v₂ : q → r`, then
`Or.elim v v₁ v₂ : r`.
-/
example (p q r s : Prop) : ((p → q) ∧ (r → s) ∧ (p ∨ r)) → (q ∨ s) :=
  fun h =>
    Or.elim h.right.right
            (fun hp => Or.inl (h.left hp))
            (fun hr => Or.inr (h.right.left hr))
/-
Notice `h.left` is the same as `And.left h`. And this notation composes
better.
-/

#check False.elim

/-
`False` cannot be introduced. But you can eliminate it to prove
anything. This is called "ex falso" or the principle of
explosion.
-/
example (p : Prop) : False → p :=
  False.elim

/-
`¬p` is defined as `p → False`.
-/
example (p : Prop) : ¬(p ∧ ¬p) :=
  fun h => h.right h.left

example (p q : Prop) : (p → q) → (¬q → ¬p) :=
  fun hpq => fun hnq => fun hp => hnq (hpq hp)

example (p q : Prop) : (p ∧ ¬p) → q :=
  fun h => False.elim (h.right h.left)

/-
The following function is non-terminating.

We have to use `partial` to satisfy lean.
-/
partial def foo (n : Nat) : Nat := foo n

/-
Homework
-/
example (p q r : Prop) : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
  sorry

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
  sorry

example (p q : Prop) : ¬(p ∨ q) → (¬p ∧ ¬q) :=
  sorry

example (p q : Prop) : (¬p ∧ ¬q) → ¬(p ∨ q) :=
  sorry

example (p q r : Prop) : ((p ∨ q) → r) → ((p → r) ∧ (q → r)) :=
  sorry

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
example (p : Prop) : ¬¬¬p → ¬p :=
  sorry

example (p : Prop) : ¬¬(p ∨ ¬p) :=
  sorry
