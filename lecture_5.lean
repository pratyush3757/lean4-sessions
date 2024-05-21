inductive BinTree (a : Type) where
| Empty : BinTree a
| Fork (left : BinTree a) (x : a) (right : BinTree a) : BinTree a

#check BinTree.Empty

#check BinTree.Fork 
  BinTree.Empty 
  2 
  (.Fork 
    .Empty 
    3 
    (.Fork 
      .Empty 
      4 
      .Empty
    )
  )

inductive OR (p q : Prop) : Prop where
| inl (hp : p) : OR p q
| inr (hq : q) : OR p q

inductive XOR (p q : Prop) : Prop where
| YesNo (hp : p) (hnq : ¬q) : XOR p q
| NoYes (hnp : ¬p) (hq : q) : XOR p q

def Even (n : Nat) := ∃k, n = 2 * k
def Odd (n : Nat) := ∃k, n = (2 * k) + 1

theorem zero_even : Even 0 :=
  Exists.intro 0 (Eq.symm (Nat.mul_zero 2))

example : XOR (Even 0) (Odd 0) := by
  apply XOR.YesNo
  case hp => exact zero_even
  case hnq => intro h; have ⟨_,_⟩ := h; omega

mutual
inductive Alice : Nat → Nat → Prop where
| Fst : (k : Nat) → (hk : 1 ≤ k ∧ k ≤ n) → (h: Bob (n-k) m) → Alice n m
| Snd : (k : Nat) → (hk : 1 ≤ k ∧ k ≤ m) → (h: Bob n (m-k)) → Alice n m

inductive Bob : Nat → Nat → Prop where
| intro (left : (k : Nat) → (hk : 1 ≤ k ∧ k ≤ n) → Alice (n-k) m)
        (right : (k : Nat) → (hk : 1 ≤ k ∧ k ≤ m) → Alice n (m-k)) : Bob n m

end

theorem bob00 : Bob 0 0 :=
  Bob.intro (fun _ _ => by omega) (fun _ _ => by omega)

theorem alice10 : Alice 1 0 := by
  apply Alice.Fst 1
  . decide
  . exact bob00
-- Alice.Fst 1 (by decide) bob00

theorem alice01 : Alice 0 1 := by
  apply Alice.Snd 1
  . decide
  . exact bob00
-- Alice.Snd 1 (by decide) bob00

/- Tactics and term modes both can be used to write programs or proofs -/
def square : Nat → Nat := by
  intro n
  exact (n*n)

#eval square 5

theorem bobnn : ∀n, Bob n n := by
  intro n
  apply Nat.caseStrongInductionOn n
  case zero => exact bob00
  case ind => 
    intro n ihn
    apply Bob.intro
    case left => 
      intro k hk
      apply Alice.Snd k
      case hk => exact hk
      case h => exact ihn (Nat.succ n - k) (by omega)
    case right => 
      intro k hk
      apply Alice.Fst k
      case hk => exact hk
      case h => exact ihn (Nat.succ n - k) (by omega)


/- After break -/
class Animal (a : Type) where
  sound : a → String

structure Cat where
  name : String
deriving Repr

structure Dog where
  name : String
deriving Repr

#eval Cat.mk "Foo"
#eval Dog.mk "Pluto"
#eval Cat.mk "Tom"

instance : Animal Cat where
  sound c := c.name ++ " Meow"

instance : Animal Dog where
  sound d := d.name ++ " Barks"

#eval Animal.sound (Dog.mk "Pluto")

section GroupTheory

class Group (G : Type u) where
  op : G → G → G
  assoc : ∀ a b c : G, op (op a b) c = op a (op b c)
  e : G
  identity : ∀ a : G, (op a e = a) ∧ (op e a = a)
  inverse : ∀ a : G, ∃ b : G, (op a b = e) ∧ (op b a = e)

/- To make the op infix -/
open Group
infixl:70 " * " => op

def is_identity [Group G] (e' : G) := ∀ a : G, (e' * a = a) ∧ (a * e' = a)

theorem unique_identity [Group G] : ∀ e' : G, is_identity e' → e' = e := by
  intro e' h
  specialize h e
  have h' := identity e'
  have hlef := Eq.symm h'.left
  exact Eq.trans (hlef) h.left

theorem left_cancellation [Group G] : ∀ a x y : G, a * x = a * y → x = y := by
  intro a x y eqn
  have ⟨ainv, h_ainv⟩ := inverse a
  calc
    x = (e : G) * x := Eq.symm (identity x).right
    _ = (ainv * a) * x := by rw [h_ainv.right]
    _ = ainv * (a * x) := by rw [assoc]
    _ = ainv * (a * y) := by rw [eqn]
    _ = (ainv * a) * y := by rw [assoc]
    _ = (e : G) * y    := by rw [h_ainv.right]
    _ = y              := by exact (identity y).right

end GroupTheory
