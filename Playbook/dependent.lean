def natOrStringThree : (b : Bool) -> if b then Nat else String
  | true => (3 : Nat)
  | false => "three"

inductive Vec (α : Type u) : Nat -> Type u where
  | nil : Vec α 0
  | cons : α -> Vec α n -> Vec α (n + 1)

open Vec in
example : Vec String 2 := cons "Hello" $ cons "world" nil

def Vec.repeat (n : Nat) (x : α) : Vec α n :=
  match n with
  | 0 => nil
  | n + 1 => cons x (Vec.repeat n x)

def Vec.zip : Vec α n -> Vec β n -> Vec (α × β) n
  | nil, nil => nil
  | cons x xs, cons y ys => cons (x, y) (zip xs ys)


namespace Tarski

inductive NatOrBool | nat | bool
abbrev NatOrBool.asType : NatOrBool -> Type
  | nat => Nat | bool => Bool
def decode : (t : NatOrBool) -> String -> Option t.asType
  | .nat => (·.toNat?)
  | .bool => fun
            | "true" => some true
            | "false" => some false
            | _ => none

inductive NestedPairs where
  | nat : NestedPairs
  | pair : NestedPairs -> NestedPairs -> NestedPairs

abbrev NestedPairs.asType : NestedPairs -> Type
  | nat => Nat
  | pair t₁ t₂ => asType t₁ × asType t₂

def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool :=
  match t, x, y with
  | .nat, x, y => x == y
  | .pair t₁ t₂, (x₁,x₂), (y₁,y₂) => beq t₁ x₁ y₁ && beq t₂ x₂ y₂

instance : BEq $ NestedPairs.asType t where
  beq x y := t.beq x y

end Tarski
instance : Applicative List where
  pure := fun a => [a]
  seq mf mx := mf.foldl (init := []) fun a f =>
    a ++ (mx () |>.mapTR f)

def List.product (xs : List α) (ys : List β) : List (α × β) :=
  .mk <$> xs <*> ys

#check Nat.le
