def length : Nat := 42

#eval length * length

def square : Nat → Nat := fun x => x * x

def cube : Nat → Nat := fun x => x * square x

#eval square 91
#eval cube 91


def myid : Nat → Nat := fun x => x

def addsq : Nat → (Nat → Nat) := 
  fun x => fun y => square x + square y

#eval addsq 2 3

def bar : (Nat → Nat) → Nat :=
  fun f => f 10

#eval bar square
#eval bar cube

def compose : (Nat → Nat) → (Nat → Nat) → (Nat → Nat) :=
  fun f => fun g => fun x => f (g x)

#eval (compose square square) 5


def factorial : Nat → Nat :=
  fun n =>
    match n with
      | .zero => 1
      | .succ n' => n * factorial n'

#eval factorial 10

def twostepfact : Nat → Nat :=
  fun n =>
    match n with
      | .zero => 1
      | .succ .zero => 1
      | .succ (.succ n') => n * twostepfact n'

#eval twostepfact 5

theorem tri : True := True.intro

theorem tri' : True ∧ True :=
  And.intro tri tri

theorem tri'' : True ∧ True ∧ True :=
  And.intro True.intro tri'

theorem tri''' : True ∨ False :=
  Or.inl tri
