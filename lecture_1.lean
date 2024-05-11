/- Syntactic sugar for functions -/

def add (x : Nat) (y : Nat) : Nat :=
  x + y

def sub (x y : Nat): Nat :=
  x - y

#eval add 10 2
#eval sub 10 2

/- Proving things -/
example (p : Prop) : p → p := 
  fun hp => hp
/- Implications are specialisations of functions for Prop → Prop instead of function's TypeX → TypeY -/

example (p q : Prop) : p → q → p :=
  fun hp => fun _ => hp

example (p q : Prop) :  p → q → q :=
  fun _ => fun hq => hq

example (p : Prop) : p → (p ∨ p) :=
  fun hp => Or.inl hp

example (p : Prop) : p → (p ∧ p) :=
  fun hp => And.intro hp hp


/- using id -/
/- I am therefore I am -/
theorem iatia (p : Prop) : p → p := 
  id /- gives identity -/
example (p : Prop) : p → p := 
  id /- gives identity -/
example (p q : Prop) :  p → q → q :=
  fun _ => iatia q

example (p q r : Prop) : (p → q) → (q → r) → (p → r) :=
  fun hpq => fun hqr => 
    (fun hp => hqr (hpq hp))
/- modus ponents? is same as func application -/

example (p q : Prop) : (p ∧ (p → q)) → q :=
  fun h => (And.right h) (And.left h)

example (p q : Prop) : ((p → q) ∧ (p → r)) → (p → (q ∧ r)) :=
  fun h => 
    (fun hp => And.intro ((And.left h) hp) ((And.right h) hp))

#check Or.elim

-- example (p q r s : Prop) : ((p → q) ∧ (r → s) ∧ (p ∨ r)) → (q ∨ s) :=
--   fun h =>
--     Or.elim (And.right (And.right h)) (And.left (And.right h)) (And.left h)

example (p q r s : Prop) : ((p → q) ∧ (r → s) ∧ (p ∨ r)) → (q ∨ s) :=
  fun h =>
    Or.elim ((And.right h).right)
            (fun hp => Or.inl ((And.left h) hp)) /- get proof of p and apply (p → q) on it -/
            (fun hr => Or.inr ((And.left (And.right h)) hr)) /- get proof of r and apply (r → s) on it -/

example (p q r s : Prop) : ((p → q) ∧ (r → s) ∧ (p ∨ r)) → (q ∨ s) :=
  fun h =>
    Or.elim h.right.right
            (fun hp => Or.inl (h.left hp))
            (fun hr => Or.inr (h.right.left hr))

#check False.elim

/- `¬p` is defined as p → False -/
example (p : Prop) : ¬(p ∧ ¬p) :=
  fun h => h.right h.left

example (p q : Prop) : (p → q) → (¬q → ¬p) :=
  fun hpq => 
    (fun hnq => fun hp => hnq (hpq hp))

example (p q : Prop) : ¬(p ∨ q) → (¬p ∧ ¬q) :=
  sorry

example (p q : Prop) : (p ∧ ¬p) → q :=
  fun h => False.elim (h.right h.left)
