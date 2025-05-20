inductive BinTree α where
  | nil
  | branch : BinTree α -> α -> BinTree α -> BinTree α


def BinTree.mapM [Monad m] (f : α -> m β) : BinTree α -> m (BinTree β)
  | nil => pure nil
  | branch l x r =>
    f x      >>= fun fx =>
    mapM f l >>= fun fl =>
    mapM f r >>= fun fr =>
    pure $ branch fl fx fr

class MonadIO (m) [Monad m] where
  liftIO : IO α -> m α

instance : MonadIO IO where
  liftIO := id

open MonadIO in
instance [Monad m] [MonadIO m] : MonadIO (StateT s m) where
  liftIO x := StateT.lift (liftIO x)

instance : MonadLift IO IO where
  monadLift := id

inductive Expr op where
  | const : Int -> Expr op
  | prim : op -> Expr op -> Expr op -> Expr op

inductive Arith where
  | add
  | sub
  | mul
  | div
section
open Expr Arith
abbrev add_2_3 : Expr Arith := prim add (const 2) (const 3)
abbrev div_14 := prim div (const 14) $ prim sub (const 45) $ prim mul (const 5) (const 9)
def evalOp : Expr Arith -> Option Int
  | const i => pure i
  | prim p e₁ e₂ => do
    let (v₁,v₂) := (<-evalOp e₁, <-evalOp e₂)
    match p with
    | add => pure $ v₁ + v₂
    | sub => pure $ v₁ - v₂
    | mul => pure $ v₁ * v₂
    | div => if v₂ == 0 then none else pure $ v₁ / v₂
def eval! : Expr Arith -> Except String Int
  | const i => pure i
  | prim p e₁ e₂ => do
    let (v₁,v₂) := (<-eval! e₁, <-eval! e₂)
    match p with
    | add => pure $ v₁ + v₂
    | sub => pure $ v₁ - v₂
    | mul => pure $ v₁ * v₂
    | div => if v₂ == 0 then .error s!"Divide by Zero of {v₁}" else pure $ v₁ / v₂
end

@[reducible] def Reader (ρ : Type u) (α : Type v) := ρ -> α
def read : Reader ρ ρ := id
def Reader.pure : α -> Reader ρ α
  | x => λ _ => x
def Reader.bind : Reader ρ α -> (α -> Reader ρ β) -> Reader ρ β
  | res, f =>
    λ e => f (res e) e

instance : Monad (Reader ρ) where
  pure := Reader.pure
  bind := Reader.bind
abbrev Env : Type := List (String × (Int → Int → Int))
def exampleEnv : Env := [("max", max), ("mod", (· % ·))]
def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  bind read fun env =>
  match env.lookup op with
  | none => pure 0
  | some f => pure (f x y)

def applyPrimReader' (op : String) (x : Int) (y : Int) : Env -> Int :=
  λ env =>
    match env.lookup op with
    | none => 0
    | some f => f x y

#eval applyPrimReader "max" 1 2 exampleEnv

def test (op : String) (a : Int) (b : Int) : Reader Env Int
  := fun x => match x.lookup op with | none => 0 | some f => f a b


example : 0.1 + 0.2 = 0.3 := sorry

structure Rational where
  num : Int
  den : Int
  p   : den ≠ 0


def Rational.add : Rational -> Rational -> Rational
  | ⟨n₁, d₁, p₁⟩, ⟨n₂, d₂, p₂⟩ =>
    if d₁ = d₂ then ⟨n₁ + n₂, d₁, p₁⟩
    else ⟨n₁ * d₂ + n₂ * d₁, d₁ * d₂, Int.mul_ne_zero p₁ p₂⟩

instance : Add Rational := ⟨Rational.add⟩

open Rational in
example : (⟨1, 10, ne_of_beq_false rfl⟩ : Rational) + ⟨2, 10, ne_of_beq_false rfl⟩ = ⟨3, 10, ne_of_beq_false rfl⟩ := by
  constructor


abbrev ℕ := Nat
variable {x : ℕ}

example : (∀n : ℕ, x < n -> x < 0) = ((∃n : ℕ, x < n) -> x < 0) := by
  apply eq_iff_iff.mpr
  constructor <;> intros
  case mp h hh =>
    rcases hh with ⟨n, nh⟩
    apply h n nh
  next h₁ n h₃ =>
    have : ∃n, x < n := ⟨n, h₃⟩
    exact h₁ this
