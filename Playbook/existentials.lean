unsafe inductive Stlc : Type u -> Type (u+1) where
  | Lift : α -> Stlc α
  | Pair : Stlc α -> Stlc β -> Stlc (α × β)
  | Lam  : (Stlc α -> Stlc β) -> Stlc (α -> β)
  | App  : Stlc (α -> β) -> Stlc α -> Stlc β
  | Fix  : Stlc (α -> α) -> Stlc α

unsafe def Stlc.eval : Stlc α -> α
  | .Lift v    => v
  | .Pair l r  => (eval l, eval r)
  | .Lam f     => λ x => eval (f (.Lift x))
  | .App f x   => (eval f) (eval x)
  | .Fix f     => (eval f) (eval (.Fix f))

open Stlc in section
#eval
let plus (x y : Stlc Nat) := Stlc.Lift <| eval x + eval y;
eval (.Lam (plus $ .Lift 1)) 2

#eval
let mul : Stlc (Nat -> Nat -> Nat) :=
  Stlc.Lam (λ x => .Lam (λ y => .Lift $ eval x * eval y))
App mul (Lift 2) |>.App (Lift 3) |>.eval
end


inductive Term : Type -> Type 1
  | Lit : Int -> Term Int
  | Succ : Term Int -> Term Int
  | IsZero : Term Int -> Term Bool
  | If : Term Bool -> Term α -> Term α -> Term α
  | Pair : Term α -> Term β -> Term (α × β)

section

variable {C : Sort -> Sort} {D : Sort}
#check ∀ x, C x -> D
#check (∃ x, C x) -> D
end

inductive Ordered where
  | mkOrdered [Ord α] : α -> Ordered

inductive Obj : Type (u+1) where
  | mk : {α : Type u} -> [Repr α] -> α -> Obj
deriving Repr
#check @Obj.mk
def fromObj {r : Type (u + 1)} : Obj -> ({α : Type u} -> [Repr α] -> α -> r) -> r
  | Obj.mk x, continuation => continuation x
def toObj : ({r : Type (u+1)} -> ({α : Type u} -> [Repr α] -> α -> r) -> r) -> Obj
  | atCont => atCont Obj.mk -- η-conversion `fun x => f x <=> f`

def Obj.print : Obj -> String | mk inst => reprStr inst

-- def main : IO Unit := println! [Obj.mk 123456, Obj.nil].map Obj.print


section

inductive Key where
  | key [Repr α] : α -> (α -> Nat) -> Key

open Key
abbrev b2i b := bif b then 1 else 0
abbrev ks := [
  key 7 id,
  key [1,2,3] List.length,
  key true b2i,
]
instance : Inhabited Key := ⟨key 0 id⟩
abbrev ext : Key -> Nat | key x f => f x

instance : ToString Key := ⟨Nat.repr ∘ ext⟩

def minks : List Key -> Key
  | []  => unreachable!
  | [x] => x
  | x :: xs => let y := minks xs
    if ext x < ext y then x else y

end

section
inductive Multi where
  | multi (a : α) (b : β) (f : α -> β -> Nat)
open Multi
abbrev mult | multi x y f => f x y
abbrev multiLs :=
  [ multi 3 4 (· + ·)
  , multi [1,2,3] [4,5] (fun x y => List.length (x ++ y))
  , multi [7,8,9] 10 (fun x y => List.length x + y)
  ]
#eval List.map mult multiLs
end

section
inductive FuncList : Type u -> Type v -> Type (max u v + 1)  where
  | cons : (α -> γ) -> FuncList γ β -> FuncList α β
  | nil : (α -> β) -> FuncList α β
open FuncList
abbrev twice x := 2 * x
abbrev double (x : α) := (x , x)
abbrev fl :=
    cons twice
  $ cons (· == 4)
  $ cons double (nil id)
def apply : FuncList α β -> α -> β
  | nil f, x => f x
  | cons f fl, x => apply fl (f x)
#eval apply fl 2

end
section RankNType
#check ∀α β, α -> β -> α -- Rank 1
#check ∀α, α -> (∀β, β -> α) -- Rank 1
#check (∀α, α -> α) -> (∀β, β -> β)

#check (∀α, List α -> Int) -> Int
#check ∀α, (List α -> Int) -> Int
end RankNType
