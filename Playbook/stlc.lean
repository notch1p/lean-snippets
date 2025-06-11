
inductive SType where
  | nat
  | arrow : SType -> SType -> SType


open SType in inductive Term (conv : SType -> Type) : SType -> Type
  | Var {α}   : conv α -> Term conv α
  | Const     : Nat -> Term conv nat
  | Plus       : Term conv nat -> Term conv nat -> Term conv nat
  | Lam {α β} : (conv α -> Term conv β) -> Term conv (arrow α β)
  | App {α β} : Term conv (arrow α β) -> Term conv α -> Term conv β
  | Let {α β} : Term conv α -> (conv α -> Term conv β) -> Term conv β

namespace STLC open SType Term

infixr: 50 " ->' " => arrow
abbrev T : SType -> Type
  | nat => Nat | arrow α β => T α -> T β

instance {conv} : OfNat (Term conv nat) n where
  ofNat := Const n

nonrec abbrev TermOf (t : SType) := {conv : SType -> Type} -> Term conv t
scoped notation (name := «term[[_]]») "[[" s "]]" => TermOf s

def add : [[nat ->' nat ->' nat]] := Lam $ fun x => Lam $ fun y => Plus (Var x) (Var y)
def One : [[nat]] := 1
def Zero : [[nat]] := 0
def succ : [[nat ->' nat]] := Lam $ fun x => Plus (Var x) One
def One' : [[nat]] := (App succ Zero)

def toStr (e : Term (λ _ => String) t) (i := 1) : String := 
  -- it is defined this way because
  -- nested function definition do not support polymorphic recursion
  match e with
  | Var s => s
  | Const n => toString n
  | App f a => s!"({toStr f i}) {toStr a i}"
  | Plus a b => s!"{toStr a} + {toStr b}"
  | Lam f =>
    let x := s!"x{i.toSubscriptString}"
    s!"λ{x}. {toStr (f x) (i + 1)}"
  | Let a b =>
    let x := s!"x{i.toSubscriptString}"
    s!"let {x} = {toStr a i} in {toStr (b x) (i + 1)}"

instance : ToString (Term (fun _ => String) ty) where
  toString x := toStr x

#eval toString $ @One' (fun _ => String)

abbrev Closed (α β : SType) := {conv : SType -> Type} -> conv α -> Term conv β

def flatten : Term (Term conv) t -> Term conv t
  | Var e => e
  | Const n => Const n
  | Plus e₁ e₂ => Plus (flatten e₁) (flatten e₂)
  | Lam f => Lam fun x => flatten $ f $ Var x -- η
  | Let a b => Let (flatten a) fun x => flatten $ b $ Var x
  | App f a => App (flatten f) (flatten a)

def subst (e : Closed α β) (e' : TermOf α) : TermOf β :=
  flatten $ e e'

#eval toStr <| subst (fun x => App succ (Var x)) 1

end STLC
