/-
2024-05-08
-/

/-
We define a variable with name `length`, type `Nat`, and value `42`.
-/
def length : Nat := 42

#eval length * length

/-
We define a variable with name `square`, type `Nat → Nat`, and value `42`.

This is a function from natural numbers to natural numbers.
-/
def square : Nat → Nat := fun x => x * x
/-
The `fun` here is a binder, like ∀, ∃.

It says, "we map x to x * x".
-/

/-
We can use things we have defined to define further things.
-/
def cube : Nat → Nat := fun x => x * (square x)

#eval (square 42)

def myid : Nat → Nat := fun x => x

/-
`addsq` is a function that takes a `Nat` and returns a `Nat → Nat`.
-/
def addsq : Nat → (Nat → Nat) :=
  fun x => fun y => (square x) + (square y)
/-
Notice the scope of the `fun` binder. It extends all the way to the right.

With explicit parenthesis, the above will be:

  fun x => (fun y => ((square x) + (square y)))

i.e., the square x + square y is in the scope of both x and y, as it should be.

Expressions with free variables are meaningless.
-/

/-
`foo` below is the same as the function `fun x => 5*5 + x*x`.

Notice I changed the name `y` to `x`. Is that a problem?
-/
def foo : Nat → Nat := (addsq 5)

#eval (foo 8)

/-
The domain of `bar` is `Nat → Nat`. The codomain is `Nat`.
-/
def bar : (Nat → Nat) → Nat :=
  fun f => (f 10)
/-
The only thing you can do with a function is to apply it to elements
in the domain.
-/
#eval (bar square)
#eval (bar cube)

/-
`compose f g` should be same as `f ∘ g` in math.

Here, we just define it for natural number functions.
-/
def compose : (Nat → Nat) → (Nat → Nat) → (Nat → Nat) :=
  fun f => fun g => fun x => f (g x)

/-
Guess the outputs.
-/
#eval ((compose square cube) 5)
#eval ((compose square square) 5)

/-
Now, a recursive function. What can we do with a `Nat` besides arithmetic?

The most fundamental operation on any type is `match`. It splits the
domain into all possible cases.
-/
def factorial : Nat → Nat :=
  fun n =>
    match n with
      | .zero => 1
      | .succ n' => n * (factorial n')
/-
The `match` is saying every natural number `n` is either zero or 
the successor of some natural number `n'`.
-/

/-
Let us define g(n) = n(n-2)(n-4)...1
-/
def g : Nat → Nat :=
  fun n =>
    match n with
      | .zero => 1
      | .succ .zero => 1
      | .succ (.succ n') => n * (g n')
/-
Notice the `match` still covers all natural numbers. This is analogous
to proof by exhaustive cases. If we miss a case, Lean will complain.
-/

/-
`Prop` is the type of propositions. Think of `Prop` like `Nat`.

What are the values of type `Prop`? `True` is one, `1 = 1` is another.
-/
#check True
#check Prop
#check 1=1
#check 1=2

/-
The values of type `Prop` are types themselves. This is *not* true for
`Nat`. `42` is a `Nat` but not a type.

However `1 = 1` has type `Prop` *and* there are values of type `1 = 1`.

Value of type `1 = 1` are exactly the proofs of the proposition `1 = 1`.
-/
theorem one_eq_one : 1 = 1 := Eq.refl 1
/-
We use `Eq.refl a`, which has type `a = a` as a value of type `1 = 1`.
-/

/-
Since Lean is sound, you cannot prove the following without `sorry`.

`sorry` is a special value that has every possible type.
-/
theorem one_sq_two : 1 = 2 := sorry

/-
Here's how you construct `3 : Nat` in it's most raw form.

The notation `3` is just syntactic sugar for the following.
-/
def three : Nat := Nat.succ (.succ (.succ .zero))

/-
We know that `True` is a theorem. How do we prove this?

`True.intro` constructs a value of type `True`. In other words,
`True.intro` is the proof of `True`.

`True.intro` is to `True` what `Nat.zero` and `Nat.succ` are to `Nat`.
-/
theorem tri : True := True.intro

/-
What are the values of type `p ∧ q`?

To construct this value, you need a value of type `p` and a value of
type `q`.

i.e., to prove `p ∧ q`, you need a proof of `p` and a proof of `q`.

Let `hp` be a proof of `p` and `hq` be a proof of `q`. Then,
`And.intro hp hq` is a proof of `p ∧ q`.
-/
theorem tri' : True ∧ True :=
  And.intro True.intro True.intro

theorem tri'' : True ∧ (True ∧ True) :=
  And.intro True.intro tri'

/-
How to construct values of type `p ∨ q`?

There are two ways: `Or.inl hp` where `hp` has type `p`, or `Or.inr hq`
where `hq` has type `q`.
-/
theorem tri''' : False ∨ True :=
  Or.inr True.intro

theorem tri'''' : True ∨ False :=
  Or.inl True.intro
/-
Try changing `inl` to `inr` and vice-versa for two proofs above.
It should fail.
-/

#check (True.intro : True)

/-
Homework
-/

/-
`fib n` should return the nth Fibonacci number.
-/
def fib : Nat → Nat := sorry

/-
`iter k f x` should be f(f(...f(x))), where `f` is applied `k` times.

`iter 0 f` is the function `fun x => x`. The identity function.

`iter 1 f` is the same as `f`.

Hint: Use induction on `k`. See `match` above.
-/
def iter : Nat → (Nat → Nat) → (Nat → Nat) := sorry

/-
`split_apply f g h x y` should be same as `f(g(x), h(y))`.

Figure out the whole definition. Assume you have only `Nat`
and functions.
-/
def split_apply : Type := sorry

/-
Now, some proofs. All these can be proved by composing things we have
already seen.
-/
theorem a : (1 = 1) ∧ (2 = 2) := sorry
theorem b : (1 = 1) ∧ ((2 = 2) ∨ (2 = 3)) := sorry
theorem c : False ∨ (True ∧ (3 = 3)) := sorry
/-
The following has two different written proofs.
-/
theorem d : True ∨ True := sorry
/-
Try whether you can prove this. It is just an equality.
-/
theorem e : 1 + 1 = 2 := sorry

/-
Can you write a proof for the following?
-/
theorem f : False := sorry
