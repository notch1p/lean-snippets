partial def
  mergesort [LE α] [DecidableRel $ LE.le (α := α)] : List α -> List α
  | [ ] => [ ]
  | [x] => [x]
  | xs  =>
    let (l, r) := xs.splitAt (xs.length / 2)
    merge (mergesort l) (mergesort r)
    where merge
          | [], ys           => ys
          | xs, []           => xs
          | x :: xs, y :: ys =>
            if x <= y then x :: merge xs (y :: ys)
                      else y :: merge (x :: xs) ys

#check mergesort.merge
#eval mergesort [4,5,61,2,3,5,7,8,10,2]

structure NonEmptyList (α : Type) where
  head : α
  tail : List α

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := {head := x, tail := xs}

structure Monoid where
  Carrier : Type
  unit    : Carrier
  op      : Carrier -> Carrier -> Carrier

def listMonoid : Type -> Monoid | α => ⟨List α, [], .append⟩
in #check listMonoid Nat

#check Membership

structure Adder where
  delta : Nat

instance : CoeFun Adder λ _ => Nat -> Nat where
  coe a := (· + a.delta)

abbrev plus [HAdd α β γ] (a : α) (b : β) := a + b
abbrev n := λ () => 3
