def List.headtail [Inhabited β] : List β -> β × List β
  | [] => (default, []) | x :: xs => (x, xs)
def List.reduce [Inhabited α](f : α -> α -> α) (xs : List α) :=
  match xs with
  | [] => default | [x] => x
  | x :: x' :: xs => reduce f (f x x' :: xs)
def List.foldrK (f : α -> β -> β) (init : β) (xs : List α) (k : β -> γ) : γ :=
  match xs with
  | [] => k init
  | x :: xs => foldrK f init xs (fun x' => k (f x x'))
def List.foldrK' (f : α -> β -> β) z xs := List.foldl (fun k x => k ∘ f x) id xs z

inductive AbstractStack.{u, v} (β : Type u) where
  | mk {F : Type u -> Type u} [Inhabited β]
  : F β
  → (β -> F β -> F β)                                          -- push
  → (F β -> β × F β)                                           -- pop
  → ({δ : Type u} -> [Inhabited δ]
    -> (δ -> δ -> δ) -> F δ -> δ)                              -- reduce
  → ({δ : Type u} -> (β -> δ) -> F β -> F δ)                   -- map
  → ({δ : Type u} -> {m : Type u -> Type v} -> [Applicative m]
    -> F δ -> (δ -> m PUnit) -> m PUnit)                       -- forM
  → ({δ : Type v} -> (β -> δ -> δ) -> δ -> F β -> δ)           -- right fold
  → AbstractStack β

namespace AbstractStack

open List in abbrev ListStack {σ : Type u} (s : List σ) [Inhabited σ] : AbstractStack σ :=
  mk s cons headtail reduce map forA foldr

end AbstractStack

open IO AbstractStack in def prog₁ := fun () =>
  let (mk s push pop reduce map forA foldr) := ListStack [1,2,3,4,5]
  let x := s |> pop |>.2 |> push 11 |> map (· ^ 2)
  let x' := map Nat.repr x
  do
    print "`x` consists of "
    forA x' (print ∘ (· ++ " "))
    print "where "
    print (x' |> reduce fun x y => s!"{x} + {y}")
    print " = "
    print (foldr (· + ·) 0 x)

#eval prog₁ ()

structure Counter (α : Type u) where
  private {t : Type u}
  _this : t
  _inc  : t -> t
  _display : t -> IO Unit
  tag : α
namespace Counter
def inc : Counter α -> Counter α | ⟨x, i, d, t⟩ => ⟨i x, i, d, t⟩
def display : Counter α -> IO Unit
  | {_this, _display..} => _display _this
def setTag (obj : Counter α) (t : α) := {obj with tag := t}
end Counter

abbrev counterA : Counter String := ⟨0, (1 + ·), IO.print, "A"⟩
abbrev counterB : Counter String where
  _this := ""
  _inc := fun s => String.push s '#'
  _display := IO.print
  tag := "B"
open Counter in
def prog₂ :=
  display (inc counterA) *> display (inc (inc counterB))
#eval prog₂

inductive Resistor where
  | metal (bands : Nat) (h : bands >= 4 ∧ bands <= 8)
  | ceramic (bands : Nat) (h : bands >= 4 ∧ bands <= 8)
deriving Repr
#eval Resistor.ceramic (7) (by simp)


inductive PZero where
  | _Z
inductive PSucc (α : Type) : Type where
  | _S : α -> PSucc α

class Cardinal (c : Type u)
instance : Cardinal PZero := ⟨⟩
instance [Cardinal c] : Cardinal (PSucc c) := ⟨⟩
class InBounds (size) [Cardinal size]

namespace PZeroSucc
abbrev Z := PZero in
abbrev S α := PSucc α in
instance D4 : InBounds (S (S (S (S Z)))) := ⟨⟩                 in -- four
instance D5 : InBounds (S (S (S (S (S Z))))) := ⟨⟩             in -- five
instance D6 : InBounds (S (S (S (S (S (S Z)))))) := ⟨⟩         in -- six
instance D7 : InBounds (S (S (S (S (S (S (S Z))))))) := ⟨⟩     in -- seven
instance D8 : InBounds (S (S (S (S (S (S (S (S Z)))))))) := ⟨⟩    -- eight
end PZeroSucc

inductive Resistor' (size : Type) | mkR deriving Repr
def resistor (_ : size) [Cardinal size] [InBounds size] : Resistor' size := Resistor'.mkR

section open PZero renaming _Z -> Z open PSucc renaming _S -> S
abbrev d0  :=  Z
abbrev d3  :=  S (S (S Z))
abbrev d4  :=  S (S (S (S Z)))
abbrev d6  :=  S (S (S (S (S (S Z)))))
abbrev d8  :=  S (S (S (S (S (S (S (S Z)))))))
abbrev d10 :=  S (S (S (S (S (S (S (S (S (S Z)))))))))
#check resistor d6

/--
error: failed to synthesize
  InBounds (PSucc (PSucc (PSucc (PSucc (PSucc (PSucc (PSucc (PSucc (PSucc (PSucc PZero))))))))))

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#check resistor d10
end


#check @exists_imp
#check Exists.elim
example {B : Prop} {α : Sort u} {P : α -> Prop} : (∃x, P x) -> (∀x : α, P x -> B) -> B
  | ⟨x, P⟩, h =>
    let h' := h x; h' P


class Sequence (F : Type u -> Type u) where
  length : F α -> Nat

instance : Sequence List := ⟨List.length⟩
instance : Sequence Array := ⟨Array.size⟩

def f [Sequence F] (x : F α) :=
  let id {α} (x : α) := x;
  (id x, id $ Sequence.length x)

class Extract (container : Type u) (elem : outParam (Type v)) where
  extract : container -> elem

@[default_instance]
instance ex_fst : Extract (Prod α β) α := ⟨fun (x, _) => x⟩
instance ex_snd : Extract (Prod α β) β := ⟨fun (_, y) => y⟩


open Extract in #eval @extract _ _ _ ('c', 3)

class EditAction (ε : Type u) (α : outParam (Type u)) where
  apply : α -> ε -> α
inductive ListAction α | ap (a : α) | rm
open ListAction in instance : EditAction (ListAction α) (List α) where
  apply
  | [], rm => []
  | _ :: xs, rm => xs
  | l, ap a => a :: l

#check let p := IO.print; p


def ack : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

def synack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => synack m 1
  | m + 1, n + 1 => synack m (synack (m / 2 + 1) n)
termination_by m n => (m, n)
decreasing_by
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.right'
    case h₁ => simp; apply Nat.div_le_self
    next => apply Nat.lt_add_one
  apply Prod.Lex.left
  simp


def binarySearch (x : Nat) (xs : Array Nat) : Option Nat :=
  go 0 xs.size where
  go (i j : Nat) (hj : j <= xs.size := by omega) :=
    if h : i < j then
      let mid := (i + j) / 2
      let y := xs[mid]
      if x = y then some mid
      else if x < y then go i mid
      else go (mid + 1) j
      else none
#check WellFounded.fix
