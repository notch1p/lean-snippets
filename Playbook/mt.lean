def getSomeInput : OptionT IO String :=
  IO.getStdin >>= (·.getLine) >>= λ i =>
    match i.trim with
    | "" => failure
    | s => pure s

namespace MonadExceptErr
#check IO.Error
inductive Err where
  | divByZero
  | notANumber : String -> Err
  | passThrough : String -> Err
instance : ToString Err where
  toString
  | Err.divByZero => "Division by zero"
  | Err.notANumber s => s!"Not a number : '{s}'"
  | Err.passThrough s => s
def Err.toIOError | Err.divByZero => IO.userError "de1"
                  | Err.notANumber s => IO.userError s!"de2{s}"
                  | Err.passThrough s => IO.userError s
def divBackend [Monad m] [MonadExcept Err m] (n k : Int) : m Int :=
  if k == 0 then throw .divByZero
  else return n / k

def asNumber [Monad m] [MonadExcept Err m] : String -> m Int
  | s => match s.toInt? with
    | none => throw (.notANumber s)
    | some i => pure i

def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String := do
  try
    return toString (<-divBackend (<-asNumber n) (<-asNumber k))
  catch e => pure <| toString e

instance : MonadExcept Err IO where
  throw e := throw e.toIOError
  tryCatch b handler := do
    try b
    catch e =>
      let es := e.toString
      if e matches IO.Error.userError _ then
        if es == "de1" then handler (.divByZero)
        else if es.startsWith "de2" then handler (.notANumber $ es.extract ⟨3⟩ es.endPos)
        else handler (.passThrough es)
      else handler (.passThrough es)



end MonadExceptErr
#check MonadExcept
namespace StateLC
structure LetterCounts where
  vowels : Nat := 0
  consonants : Nat := 0
deriving Repr

inductive Err
  | notALetter : Char -> Err
deriving Repr

abbrev vowels := "aeiuoyAEIUOY"
abbrev consonants := "bcdfghjklmnpqrstvwxzBCDFGHJKLMNPQRSTVWXZ"
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify λ st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify λ st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList

def countLetters' (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (iter : String.Iterator) := do
    if iter.atEnd then pure ()
    else
      let c := iter.curr
        if vowels.contains c then modify λ st => {st with vowels := st.vowels}
        else if consonants.contains c then modify λ st => {st with consonants := st.consonants}
        else throw (.notALetter c)
      loop iter.next
  loop str.iter

def countLetters'' (m : Type -> Type) [Monad m] [MonadState LetterCounts m] [MonadExcept Err m] (str : String) : m Unit :=
  let rec loop (iter : String.Iterator) := do
    if iter.atEnd then pure ()
    else
      let c := iter.curr
        if vowels.contains c then modify λ st => {st with vowels := st.vowels}
        else if consonants.contains c then modify λ st => {st with consonants := st.consonants}
        else throw (.notALetter c)
      loop iter.next
  loop str.iter

abbrev M₁ := StateT LetterCounts (Except Err)
abbrev M₂ := ExceptT Err (StateM LetterCounts)
#eval countLetters'' M₁ "123" |>.run {}
#eval countLetters'' M₂ "123" |>.run' {}
#eval countLetters'' M₂ "asfhjrwuoeiruov" {}

#reduce (types := true) M₁ Nat
#reduce (types := true) M₂ Nat

def countWithFallback str := try countLetters'' (m := M₁) str catch _ => countLetters "Fallback"

end StateLC


#check MonadWithReader
namespace MonadWithLog
structure WithLogT (ρ : Type u) (m : Type u -> Type v) (α : Type u) where
  run : m (α × Array ρ)

instance [Monad m] : Monad (WithLogT ρ m) where
  pure x := ⟨pure (x, #[])⟩
  bind x f :=
  ⟨ do
    let (a, l₁) <- x.run
    let (b, l₂) <- f a |>.run
    pure (b, l₁ ++ l₂)
  ⟩

class MonadWithLog (log : Type) (m : Type → Type) where
  tell : log → m Unit

-- Instance for WithLogT
instance {log m} [Monad m] : MonadWithLog log (WithLogT log m) where
  tell msg := ⟨(pure ((), #[msg]))⟩

-- Instance for transformed monad
instance {log m t} [MonadWithLog log m] [MonadLift m t] : MonadWithLog log t where
  tell msg := liftM (MonadWithLog.tell msg : m Unit)

abbrev LogExceptT (ε : Type) (m : Type -> Type) ρ α := ExceptT ε (WithLogT ρ m) α

open MonadWithLog  MonadExceptErr in
def prog (n m : Int) : LogExceptT Err IO String Int := do
  try
    divBackend n m
  catch
  | .divByZero => tell "Division By Zero"; pure 1
  | _ => pure 1
def runProg : IO Unit := do
  let x <- prog 4 0 |>.run.run
  x.2.forM IO.println
  let y <- prog 4 2 |>.run.run
end MonadWithLog

inductive Many α where
  | none
  | more : α -> (Unit -> Many α) -> Many α

namespace Many
@[always_inline, inline]def one (x : α) := more x (λ () => none)
@[always_inline, inline]def union : Many α -> Many α -> Many α
  | none, ys => ys
  | more x xs, ys => more x λ () => (union (xs ()) ys)
@[always_inline, inline]def fromList : List α -> Many α
  | [] => none
  | x :: xs => more x λ () => fromList xs
@[always_inline, inline]def take : Nat -> Many α -> List α
  | 0 , _ => []
  | n + 1, none => []
  | n + 1, more x xs => x :: (take n (xs ()))
@[always_inline, inline]def takeAll : Many α -> List α
  | none => []
  | more x xs => x :: (takeAll (xs ()))
abbrev toList (xs : Many α) := Many.takeAll xs

def bind : Many α -> (α -> Many β) -> Many β
  | none, _ => none
  | more x xs, f => union (f x) (bind (xs ()) f)
@[always_inline] instance : Monad Many where pure := one; bind := bind
infix : 50 " <+> " => union
def addsTo (n : Nat) : List Nat -> Many (List Nat)
  | [] => if n == 0 then pure [] else none
  | x :: xs =>
    if x > n then addsTo n xs
    else addsTo n xs <+> (addsTo (n - x) xs
      >>= fun ans => pure $ x :: ans)
#eval [1,2,4,5,6,7,8,10,12,13,14,15,0] |> addsTo 15 |>.takeAll
end Many

def ManyT (m : Type u -> Type v) (α : Type u) : Type v := m (Many α)
@[always_inline, inline] abbrev ManyT.mk  (mx : m (Many α)) : ManyT m α := mx
@[always_inline, inline] abbrev ManyT.run  (mx : ManyT m α) : m (Many α) := mx

namespace ManyT
variable {α β : Type u} {m : Type u -> Type v} [Monad m]

def bind (mx : (ManyT m α)) (f : α -> (ManyT m β)) : ManyT m β :=
  ManyT.mk <| mx >>= loop
  where
    loop
    | Many.none => pure Many.none
    | Many.more x tail =>
      f x >>= fun fx => (loop (tail ())) >>= fun tb => return fx <+> tb

instance [Monad m] : Monad (ManyT m) where
  pure a := mk (pure (Many.one a))
  bind := bind
def orElse (x : ManyT m α) (y : Unit -> ManyT m α) := mk $
  x.run >>= fun
            | Many.none => y ()
            | Many.more _ _ => x
@[always_inline, inline] def liftM (ma : m α) : ManyT m α :=
  ManyT.mk <| ma >>= λ x => pure $ Many.one x

@[always_inline, inline] instance [Monad m] : MonadLiftT m (ManyT m) where
  monadLift := liftM

@[always_inline, inline] instance [Monad m] : Alternative (ManyT m) where
  failure := pure (f := m) Many.none
  orElse := ManyT.orElse

#reduce (types := true) StateT Nat (ManyT Id)
#reduce (types := true) ManyT (StateT Nat Id)
end ManyT
