/-
Homework
-/

/-
`fib n` should return the nth Fibonacci number.
-/
def fib : Nat → Nat := 
  fun n => 
    match n with
    | .zero => .zero
    | .succ .zero => 1
    | .succ (.succ n') => fib (.succ n') + fib n'

#eval fib 10

/-
`iter k f x` should be f(f(...f(x))), where `f` is applied `k` times.

`iter 0 f` is the function `fun x => x`. The identity function.

`iter 1 f` is the same as `f`.

Hint: Use induction on `k`. See `match` above.
-/
def iter : Nat → (Nat → Nat) → (Nat → Nat) := 
  fun k => 
  match k with
  | .zero => fun x => x
  | .succ .zero => (fun f => fun x => f x)
  | .succ k' => fun f => fun x => f (iter k' f x)

def double : Nat → Nat :=
  fun n => n + n

#check iter 0 double
#check iter 1 double
#check iter 2 double
#eval iter 3 double 2

/-
`split_apply f g h x y` should be same as `f(g(x), h(y))`.

Figure out the whole definition. Assume you have only `Nat`
and functions.
-/
def split_apply : (Nat → Nat → Nat) → (Nat → Nat) → (Nat → Nat) → (Nat) → (Nat) → Nat := 
  fun f => fun g => fun h => fun x => fun y => f (g x) (h y)

def plus_one : Nat → Nat :=
  fun n => n + 1
def add : Nat -> Nat -> Nat :=
  fun x => fun y => x +y

#eval split_apply add plus_one double 1 5

/-
Now, some proofs. All these can be proved by composing things we have
already seen.
-/
theorem one_eq_one : 1 = 1 := Eq.refl 1
theorem two_eq_two : 2 = 2 := Eq.refl 2

theorem tri : True := True.intro
theorem and_tri : True ∧ True := And.intro tri tri
theorem or_tri_l : True ∨ False := Or.inl tri
theorem or_tri_r : False ∨ True := Or.inr tri

theorem a : (1 = 1) ∧ (2 = 2) := And.intro one_eq_one two_eq_two
theorem b : (1 = 1) ∧ ((2 = 2) ∨ (2 = 3)) := And.intro one_eq_one (Or.inl two_eq_two)
theorem c : False ∨ (True ∧ (3 = 3)) := Or.inr (And.intro tri (Eq.refl 3))

/-
The following has two different written proofs.
-/
theorem d : True ∨ True := Or.inr tri
/-
Try whether you can prove this. It is just an equality.
-/
theorem e : 1 + 1 = 2 := Eq.refl (1 + 1)

/-
Can you write a proof for the following?
-/
theorem f : False := sorry
/- We cannot as False has no proof -/
