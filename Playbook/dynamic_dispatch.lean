set_option eval.type true

class HasShape (α : Type u) where
  perimeter : α -> Float
  area      : α -> Float

inductive Shape where
  | mk [HasShape α] : (p : α) -> Shape

abbrev Radius := Float
abbrev Side   := Float

inductive Circle    | mk (r : Radius)
inductive Rectangle | mk (s₁ s₂ : Side)
inductive Square    | mk (s : Side)

abbrev pi := 3.1415926

instance : HasShape Circle where
  perimeter | .mk r => 2 * pi * r
  area      | .mk r => pi * r^2

instance : HasShape Rectangle where
  perimeter | .mk s₁ s₂ => 2 * (s₁ + s₂)
  area      | .mk s₁ s₂ => s₁ * s₂

instance : HasShape Square where
  perimeter | .mk s => 4 * s
  area      | .mk s => s ^ 2

open Shape in
open HasShape hiding mk in
instance : HasShape Shape where
  perimeter | mk s => perimeter s
  area      | mk s => area s

abbrev circle (r : Radius) : Shape := .mk $ Circle.mk r
abbrev rect   (x y : Side) : Shape := .mk $ Rectangle.mk x y
abbrev square (s : Side)   : Shape := .mk $ Square.mk s
abbrev shapes : List Shape :=
  [ circle 2.4
  , rect 3.1 4.4
  , square 2.1
  ]

#eval
(shapes.map HasShape.area, shapes.map HasShape.perimeter)

-- #check panic
def main1 : IO Unit :=
  (pure $ repr (shapes.map HasShape.area, shapes.map HasShape.perimeter))
  >>= .println

#eval main1
#print main1

def main2 : IO Nat :=
  let x := IO.rand 0 10
  x >>= fun x => bif x &&& 1 == 0 then panic! "Even" else pure x


#check (· >> ·)

instance : HAndThen Bool Unit Unit := ⟨fun a b => bif a then b () else ()⟩

def lsum [Add α] [Zero α] : List α -> α
  | l =>
    loop l 0
    where loop lst acc :=
      match lst with
      | []  => acc
      | x :: xs => loop xs (acc + x)

#check let i : Fin 20 := ⟨10, by decide⟩; let j : Nat := ↑i; j


#eval
open IO(print) in let x (_ : Unit) : IO Unit := print "h" *> print "a"
do x () *> x ()


abbrev DivideByZero := String
def divE : Int -> Int -> Except String Int
  | _, 0 => .error "Divide By Zero"
  | x, y => .ok $ x / y

abbrev NonEmptyString := {s : String // s ≠ ""}
#check (⟨"123", by decide⟩ : NonEmptyString)

instance : Monad List where
  pure x := [x]
  bind x f := x.flatMap f


def List.prod : List α -> List β -> List (α × β) | xs , ys => (· , ·) <$> xs <*> ys

instance : HMul (List α) (List β) (List $ α × β) := ⟨List.prod⟩
#eval [1,2,3] * ['a','b','c']

#eval do
let mut v := #[]
for x in [0 : 43], y in ['a', 'b'] do
  v := v.push (x, y)
return v

def inf (x : Nat) : Id Unit := do while x &&& 1 != 0 do pure ()

def countdown' (n : Nat) : List Nat :=
  if h' : n == 0 then []
  else
    let n' := n - 1
    n' :: countdown' n'
termination_by n
decreasing_by
  have h : (¬(n == 0) = true) = (n ≠ 0) := by
    simp
  rw [h] at h'
  apply Nat.sub_one_lt
  exact h'

inductive Term : Type -> Type 1
  | Int : Int -> Term Int
  | Add : Term (Int -> Int -> Int)
  | App : Term (β -> α) -> Term β -> Term α

def Term.eval : ∀ {α}, Term α -> α :=
fun {α : Type} =>
fun
  | Term.Int n => n
  | Term.Add => fun x y => x + y
  | Term.App f x => (eval f) (eval x)

open Term in #eval (Int 1).eval

def f₁ {β γ : Type} : ({α : Type} -> α -> List α) × β × γ -> List β × List γ
  | ⟨g, x, y⟩ => (g x, g y)

abbrev foo := @List.map Int Int

def typeI : Nat -> Type
  | 0 => Empty
  | 1 => Unit
  | 2 => Bool
  | _ => Nat

def listify (x : α) := [x] in def f' : β × γ -> List β × List γ
  | (x, y) =>
    (listify x, listify y)

def f'₁ : β × γ -> List β × List γ
  | (x, y) => let listify {α} (x : α) := [x]; (listify x, listify y)

/-- impredicative polymorphism.
    ```
    some : ∀α, α -> Option α where α := ∀α', List α' -> List α'
    ```
-/
def f'' : Option ({α : Type} -> List α -> List α) -> Option (List Int × List Char)
  | some g => some (g [1,2,3,4,5], g ("hello".toList))
  | none => none
#eval f'' (some List.reverse)
#check {α : Type} -> [Repr ({α : Type} -> α -> α)] -> List α -> List α
#eval open IO in
  let x := print "h" *> print "a";
  x *> x

inductive PList where
  | nil
  | cons [Repr α] : α -> PList -> PList
  deriving Repr

namespace PList
abbrev L₁ :=
  cons 3
$ cons "123"
$ cons true nil

def length : PList -> Nat
  | nil => 0
  | cons _ xs => length xs + 1
def repr (l : PList) : String :=
  s!"[{go "" l}]" where
    go s
    | nil => s
    | cons x nil => s ++ reprStr x
    | cons x xs@(cons _ _) => go (s ++ reprStr x ++ ", ") xs
instance : Repr PList where
  reprPrec n _ := n.repr

#check Function.const
def constMap (a : α) [Repr α]  : PList -> PList
  | nil => nil
  | cons _ xs => cons a (constMap a xs)
#eval (L₁, L₁.length)
#eval (L₁, L₁.constMap 20)
end PList

inductive AbstractStack' : Type u -> Type (u+1) where
  | mk [Inhabited β] : α -> (β -> α -> α) -> (α -> β × α) -> AbstractStack' α

def Nat.minus1 | zero => (0, 0) | succ x => (1, x)

abbrev ListStack' : AbstractStack' Nat :=
  .mk Nat.zero Nat.add Nat.minus1

example (p : 1 ≠ 0) (np : 1 = 0) : C := False.elim (p np)

def exElim.{u} : ∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (a : α), p a → b) → b :=
fun h₁ h₂ =>
  match h₁ with
  | Exists.intro a h => h₂ a h

def isEven (n : Nat) := n % 2 = 0
example : ∃x > 2, isEven x := by
  refine ⟨4, ?x⟩
  case x => simp[isEven]

example {P : (α : Sort u) -> Prop} (h : ∃x, P x) (h' : ∀a, P a -> Q) : Q := by
  cases h with
  | intro x h => exact h' x h

inductive ExistsType | pack : α -> ExistsType

#check ST

inductive ExistentialsThatReduceToInt where
  | pack : α -> (α -> Nat) -> ExistentialsThatReduceToInt

open ExistentialsThatReduceToInt in
abbrev x := (pack "asda" String.length, pack 2 (fun x => x ^ 2)) in
def ExistentialsThatReduceToInt.app | pack x f => f x in
#eval (x.1.app, x.2.app)
