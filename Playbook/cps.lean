
/-- The continuation monad, parameterized by the result type `r`. -/
structure Cont (r : Type u) (α : Type u) where
  run : (α -> r) -> r
/-- Unwrap the continuation to run it. -/
def Cont.runCont {r α : Type u} (c : Cont r α) (k : α -> r) : r :=
  c.run k
namespace Control.Monad.Cont

/-- The Monad instance for `Cont r`. -/
instance (r : Type u) : Monad (Cont r) where
  pure a :=
    { run := fun k => k a }
  bind c f :=
    { run := fun k =>
        -- run c, then feed 'a' from c into f
        c.run (fun a => (f a).run k) }

/--
  call-with-current-continuation: captures the current continuation,
  allowing the user to invoke it within the provided function.
-/
def callCC {r α β : Type u}
  (f : (α -> Cont r β) -> Cont r α) : Cont r α :=
  ⟨λ k => (f (λ a => ⟨λ _ => k a⟩)).run k⟩

end Control.Monad.Cont

open Control.Monad.Cont
def List.lengthCps : List α -> (Nat -> ρ) -> ρ
  | [], k => k 0 | _ :: xs, k => lengthCps xs (k ∘ Nat.succ)
def List.lengthCps' : List α -> Cont ρ Nat -- not tailrec
  | [] => pure 0
  | _ :: xs => lengthCps' xs >>= pure ∘ (·.succ)
def List.lengthCps'' (xs : List α) : Cont ρ Nat :=
  ⟨List.lengthCps xs⟩

def pow2 (x : Float) (cont : Float -> α) := cont (x ^ 2)
def pow2m (a : Float) : Cont α Float := return (a ^ 2)
def add (x y : Float) (cont : Float -> α) := cont (x + y)
nonrec def sqrt (x : Float) (cont : Float -> α) := cont (x.sqrt)
def pyth : Float -> Float -> (Float -> α) -> α
  | x, y, cont => pow2
                    x (λ xx =>
                        pow2
                          y (λ yy =>
                              add xx yy (λ xny =>
                                sqrt xny cont)))

def pythm (x y : Float) : Cont α Float := callCC $ λ exitF => do
  if x < 0 || y < 0 then (exitF 0.0)
  let x₂ <- pow2m x
  let y₂ <- pow2m y
  let xny <- ⟨add x₂ y₂⟩
  let r <- ⟨sqrt xny⟩
  return r

#eval Cont.runCont (pythm (-1.0) 0) id

def safediv
  (x y : Float) : Cont α (Option Float) := callCC $ λ exitOn => do
  if y == 0.0 then exitOn none
  return some $ x / y
def safediv'
  (x y : Float)
  (ret : Option Float -> Cont α Unit) : Cont α (Option Float) := do
  if y == 0.0 then ret none
  return some $ x / y

prefix : 65 "call/cc " => callCC


#eval
call/cc safediv' 4 0
  |>.runCont λ
             | none => "inf"
             | some x => toString x

#eval (safediv 4 2).runCont λ
                            | none => "inf"
                            | some x => toString x

def divList (xs ys : List Float) : Cont α (List Float) := callCC $ λ K =>
  match xs, ys with
  | [], _ => K []
  | _ , [] => K []
  | x :: xs, y :: ys =>
    call/cc safediv' x y |>.runCont
      λ | none => K []
        | some xy =>
          divList xs ys |>.runCont λ l =>
            K $ xy :: l

def divList'
  (xs ys : List Float)
  (cont : List Float -> IO Unit)
  (ret : List Float -> IO Unit := λ rs => println! s!"{rs}\n|- aborted")
: IO Unit :=
  match xs, ys with
  | [], _ | _, [] => cont []
  | x :: xs, y :: ys =>
    if y == 0 then IO.println s!"returning from call at: {x}/{y}" *> ret []
    else
      divList' xs ys λ rs =>
        IO.println s!"calculating {x}/{y}" *>
        (cont <| x / y :: rs)
partial_fixpoint

open List in
#eval divList [1,2,3,4,5] [5,4,3,2,1] |>.run id in
#eval divList' [1,2,3,4,5] [5,4,0,2,1] λ s => println! s
#eval divList' [1,2,3,4,5] [5,4,0,2,1] λ rs => println! rs

open Cont in section
abbrev ContT (ρ : Type) (m : Type -> Type) (α : Type)
 := Cont (m ρ) α

instance [Monad m] : MonadLift m (ContT ρ m) where
  monadLift x := ⟨bind (m := m) x⟩

def factCPS : Nat -> (Nat -> ρ) -> ρ
  | 0, k => k 1
  | n'@(n + 1), k => factCPS n $ k ∘ (· * n')

def factTail : Nat -> (_ : Nat := 1) -> Nat
  | 0, c => c
  | n'@(n + 1), c => factTail n (n' * c)

def thrice (f : α -> α) x := f ∘ f ∘ f $ x
def thriceCPS (f : α -> (α -> ρ) -> ρ) x := λ k =>
  f x fun x =>
    f x fun x =>
      f x $ k


end

--              Cont ρ α           α -> Cont ρ β             Cont ρ β      = (· >>= ·)
def chainCPS : ((α -> ρ) -> ρ) -> (α -> ((β -> ρ) -> ρ)) -> ((β -> ρ) -> ρ)
  | c, f => c ∘ flip f

inductive Tree where
  | leaf : Int -> Tree
  | node : Tree -> Int -> Tree -> Tree deriving Repr
open Tree in abbrev tree :=
  node
    (node
      (node
        (node
          (leaf 3)
          13
          (leaf 5))
        6
        (leaf 7))
      8
      (leaf 9))
    10
    (leaf 11)

def Tree.sum : Tree -> Int
  | leaf i => i
  | node t i t' => sum t + i + sum t'
def Tree.sumCps (t : Tree) (ret : Int -> Cont ρ Int) :=
  go ret t ret
  where go ret
    | leaf 13, _ => ret 42
    | leaf i, k => k i
    | node _ 13 _, _ => ret 42
    | node t i t', k =>
      go ret t λ k' =>
        go ret t' λ k'' =>
          k $ k' + i + k''

partial def Tree.sum' : List Tree -> (_ : Int := 0) -> Int
  | [], a => a
  | leaf 6 :: ts, a => 1000
  | leaf x :: ts, a => sum' ts (a + x)
  | node l 6 r :: ts, a => 1000
  | node l i r :: ts, a => sum' (l :: r :: ts) (a + i)

def Tree.flatten : Tree -> List Tree -> List Tree
  | n@(leaf _), l => n :: l
  | node l i r, ll =>
    flatten l (leaf i :: flatten r ll)
def Tree.sumList : Tree -> Int
  | t => go 0 (t.flatten []) where
    go acc
    | [] => acc
    | leaf 6 :: xs => 1000
    | leaf x :: xs => go (acc + x) xs
    | node _ _ _ :: xs => go acc xs

#eval call/cc tree.sumCps |>.runCont id

section
variable {α β : Type u}
def regularToCps := λ (b : β) => λ (f : β -> β) => f b
#check @regularToCps
def cpsToRegular := λ (k : (β -> β) -> β) => k id
#check @cpsToRegular

#check (cpsToRegular ∘ regularToCps : β -> β)
#check Function.comp regularToCps cpsToRegular (δ := (β -> β) -> β)

open Tree in
def prog : ContT ρ IO Int := do
  let tree :=
    node
      (node
        (node
          (node
            (leaf 3)
            13
            (leaf 5))
          6
          (leaf 7))
        8
        (leaf 9))
      10
      (leaf 11)
  let res <- call/cc tree.sumCps
  return res

#eval prog.runCont λ x => pure x
end

#check forM

abbrev ten {ρ} := λ (k : Int -> ρ) =>
  λ c =>
    (λ b =>
      (λ a =>
        k (a + 4))
      (b + 3))
    (c + 2)

abbrev Bin := {p // p = -1 ∨ p = 0 ∨ p = 1}
abbrev ConstHello := {s // s = "hello"}

def compareBin (a b : Int) : Bin :=
  if a == b then ⟨0, .inr $ .inl $ .refl 0⟩
  else if a > b then ⟨1, .inr $ .inr $ .refl 1⟩
  else ⟨-1, .inl $ .refl (-1)⟩

def List.find?' (p : α -> Bool) : List α -> Cont ρ (Option α)
  | [] => return none
  | x :: xs =>
    if p x then return x
    else find?' p xs

def runCatch [Monad m] (act : ExceptT α m α) : m α :=
  act >>= fun
          | .ok x => pure x
          | .error x => pure x


def lstFind? (p : α -> Bool) : List α -> Option α
  | [] => failure
  | x :: xs =>
    runCatch
      ( cond (p x) (throw x) (pure ())
      *>liftM (lstFind? p xs)
      )


structure AllLessThan where
  num : Nat

def AllLessThan.forM [Monad m] (coll : AllLessThan) (act : Nat -> m PUnit) : m PUnit :=
  let rec cd
          | 0 => pure ()
          | n + 1 => act n *> cd n
  cd coll.num

instance : ForM m AllLessThan Nat := ⟨AllLessThan.forM⟩
#eval @forM _ AllLessThan _ _ _ ⟨10⟩ IO.println

structure LinesOf where
  stream : IO.FS.Stream

partial def LinesOf.forM (readFrom : LinesOf) (action : String → IO Unit) : IO Unit := do
  let line <- readFrom.stream.getLine
  if line == "" then return ()
  action line
  forM readFrom action

instance : ForM IO LinesOf String where
  forM := LinesOf.forM

open IO in
def filterLines (argv : List String) : IO UInt32 := do
  if !argv.isEmpty then
    eprintln "Unexpected arguments"
    return 1
  let instOfStream : LinesOf := ⟨<-getStdin⟩
  forM instOfStream fun l => do
    if l.any (·.isAlpha) then print l
  return 0

@[always_inline, inline]def OptionT.exec [Applicative m] (action : OptionT m α) : m PUnit :=
  action *> pure ()

@[always_inline, inline]
noncomputable abbrev optiontBind [Monad m] (a : OptionT m α) (act : α -> OptionT m β) : OptionT m β := OptionT.mk $
  a >>= fun
        | some n => act n
        | none => pure none

#print OptionT.bind
def AllLessThan.forM' [Monad m] (coll : AllLessThan) (act : Nat -> Nat -> m PUnit) : m PUnit :=
  let rec cd iter
          | 0 => pure ()
          | n + 1 => act n iter *> cd (iter + 1) n
  cd 0 coll.num

def countDownTo3 (n : Nat) : IO Unit :=
  let nums : AllLessThan := ⟨n⟩
  letI pn : IO (Option PUnit) := pure none
  OptionT.exec
    (AllLessThan.forM'
      nums
      fun i j =>
        if i < 3 then IO.println s!"iterCnt: {j}" *> pn else IO.println i)

instance : ForIn m AllLessThan Nat where
  forIn := ForM.forIn

def countToThree (n : Nat) : IO Unit := do
  let nums : AllLessThan := ⟨n⟩
  let mut i' := 0
  for i in nums do
    if i < 3 then break
    i' := i' + 1
    IO.println (i, i')

#eval countToThree 10

def List.find?'' (p : α -> Bool) (xs : List α) := Id.run do
  for x in xs do
    if not (p x) then continue
    return true
  return false

def spam : IO Unit := do
  repeat IO.println "Spam!"
