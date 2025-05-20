#eval some (· + ·) <*> some 4 <*> some 5

instance : Functor $ Prod α where map f | (x, y) => (x , f y)

section
abbrev FinN n := { x : Nat // x < n }

def FinN.fromNat?' n : Nat -> Option (FinN n)
  | i =>
    dite (i < n)
         (fun hyp => some ⟨i, hyp⟩)
         (fun _ => none)

def FinN.fromNat? n : Nat -> Option (FinN n)
  | i => if hyp : i < n then some ⟨i, hyp⟩ else none
end


structure CheckedInput (thisYear : Nat) where
  name      : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y <= thisYear}

abbrev NonEmptyList α := { x : List α // x ≠ []}

inductive Validate ε α where
  | ok (_ : α)
  | errs : NonEmptyList ε -> Validate ε α

instance : Functor $ Validate ε where
  map f
  | .ok x => .ok $ f x
  | .errs es => .errs es
