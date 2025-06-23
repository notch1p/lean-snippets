import Parser
import Playbook.ffidecl

open Parser Parser.Char
namespace Lexing
abbrev TParser := SimpleParser Substring Char

abbrev INT := @ASCII.parseInt

def alphanum' [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m]
  : ParserT ε σ Char m Char :=
  withErrorMessage "expected letter or digit character or \'" do
    tokenFilter fun c =>
      if c >= 'a' then c <= 'z'
      else if c >= 'A' then c <= 'Z'
      else c >= '0' && c <= '9' || c == '\''

def reserved := ["let", "in", "fn", "fun", "=", "if", "else", "then", "->"]
open ASCII in def ID' : TParser String :=
  withErrorMessage "identifier" do
      (· ++ ·)
  <$> (Char.toString <$> alpha)
  <*> foldl String.push "" alphanum'

def ID : TParser String := do
  let id <- ID'
  if reserved.contains id then throwUnexpectedWithMessage none s!"expected identifier, not keyword {id}"
  else return id

def spaces : TParser Unit :=
  dropMany <| tokenFilter [' ', '\n', '\r', '\t'].contains
abbrev ws (t : TParser α) := spaces *> t <* spaces

abbrev kw (s : String) : TParser String := withErrorMessage "keyword" do spaces *> string s <* spaces
abbrev LET   := drop 1 $ kw "let"
abbrev IN    := drop 1 $ kw "in"
abbrev FUN   := drop 1 $ kw "fun"
abbrev EQ    := drop 1 $ kw "="
abbrev IF    := drop 1 $ kw "if"
abbrev ELSE  := drop 1 $ kw "else"
abbrev THEN  := drop 1 $ kw "then"
abbrev ARROW := drop 1 $ kw "->"
abbrev COMMA := spaces *> kw ","
end Lexing

abbrev Symbol := String
inductive Expr where
  | CI (i : Int)       | CS (s : String)        | CB (b : Bool) | CUnit
  | App (e₁ e₂ : Expr) | Cond (e₁ e₂ e₃ : Expr) | Let (a : Symbol) (e₁ e₂ : Expr)
  | Var (s : Symbol)   | Fun (a : Symbol) (e : Expr)
  | Prod' (e₁ e₂ : Expr)
deriving Repr, BEq, Nonempty

instance : Inhabited Expr := ⟨Expr.CUnit⟩

def List.reduce [Inhabited α] (f : α -> α -> α) (xs : List α) :=
  match xs with
  | [] => default | [x] => x
  | x :: x' :: xs => reduce f (f x x' :: xs)

namespace Parsing
open Lexing Expr

/--
  `chainl1 p op` parses *one* or more occurrences of `p`, separated by `op`. Returns
  a value obtained by a **left** associative application of all functions returned by `op` to the
  values returned by `p`.
-/
partial def chainl1  [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m]
  (p : ParserT ε σ τ m α)
  (op : ParserT ε σ τ m (α -> α -> α)) : ParserT ε σ τ m α := do
  let x <- p; rest x where
  rest x :=
    (do let f <- op; let y <- p; rest (f x y)) <|> pure x
def chainl [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m]
  (p : ParserT ε σ τ m α)
  (op : ParserT ε σ τ m (α -> α -> α))
  (x : α) : ParserT ε σ τ m α := chainl1 p op <|> return x
mutual
private partial def atom : TParser Expr :=
  first [ parenthesized (spaces *> pure CUnit)
        , parenthesized prodExp
        , ws varExp
        , ws letExp
        , ws funExp
        , ws condExp
        , ws intExp
        , ws strExp]


private partial def exp : TParser Expr :=
  chainl1 atom (pure App)

private partial def prodExp : TParser Expr := do
  let e <- exp
  let es <- takeMany (COMMA *> exp)
  match es.toList with
  | [] => pure e | e' :: es => pure $ es.foldl Prod' (Prod' e e')

private partial def between (l : Char) (t : TParser Expr) (r : Char) : TParser Expr :=
 spaces *> char l *> spaces *> t <* spaces <* char r <* spaces
private partial def parenthesized (t : TParser Expr) : TParser Expr := between '(' t ')'

private partial def intExp  : TParser Expr := INT             >>= pure ∘ CI
private partial def strExp  : TParser Expr := do
  let s <- char '"'
        *> foldl String.push "" (tokenFilter (not ∘ ['"'].contains))
        <* char '"'                                           return CS s
private partial def varExp  : TParser Expr :=
  ID >>= pure ∘ fun
         | "true"                                             => CB true
         | "false"                                            => CB false
         | v                                                  => Var v
private partial def letExp  : TParser Expr := do
  LET; let id <- ID; EQ; let e₁ <- exp; IN; let e₂ <- exp     return Let id e₁ e₂
private partial def funExp  : TParser Expr := do
  FUN; let var <- ID; ARROW; let e <- exp                     return Fun var e
private partial def condExp : TParser Expr := do
  IF; let c <- exp; THEN; let e₁ <- exp; ELSE; let e₂ <- exp  return Cond c e₁ e₂

end
def parse (s : String) : Except String Expr :=
  match Parser.run (spaces *> exp <* endOfInput) s with
  | .ok _ t    => pure t
  | .error _ e => throw (toString e)

end Parsing


def List.rmDup [BEq α] [Hashable α] (l : List α) : List α :=
  let s : Std.HashSet α := ∅
  let rec go s
    | [] => []
    | x :: xs => if x ∈ s then go s xs else x :: go (insert x s) xs
  go s l


inductive TV where
  | mkTV : String -> TV deriving Repr, BEq, Ord, Hashable
instance : ToString TV := ⟨fun | .mkTV s => s⟩

inductive MLType where
  | TVar : TV -> MLType
  | TCon : String -> MLType
  | TArr : MLType -> MLType -> MLType
  | TProd : MLType -> MLType -> MLType
deriving Repr, BEq, Ord, Inhabited

infixr: 50 " ->' " => MLType.TArr
infixr: 65 " ×'' " => MLType.TProd
def MLType.toStr : MLType -> String
  | TVar a => toString a | TCon a => a
  | a ×'' b => paren (arr? a) (toStr a) ++ " × " ++ paren (arr? b) (toStr b)
  | a ->' b =>
    paren (arr? a) (toStr a) ++ " → " ++ toStr b where
    paren b s := bif b then s!"({s})" else s
    arr? | TArr _ _ => true | _ => false

instance : ToString MLType := ⟨MLType.toStr⟩

inductive Scheme where
  | Forall : List TV -> MLType -> Scheme deriving Repr, BEq, Ord

instance : ToString Scheme where
  toString
  | .Forall [] t => toString t
  | .Forall ts t => "∀ { " ++ (ts.foldl (init := "") fun a s => s!"{a}{s} ") ++ s!"}. {toString t}"

namespace MLType open TV Expr
inductive TypingError
  | NoUnify (t₁ t₂ : MLType)
  | Undefined (s : String)
  | NonApplicable
  | WrongCardinal (n : Nat)
  | Duplicates (t : TV) (T : MLType) deriving Repr

instance : ToString TypingError where
  toString
  | .NoUnify t₁ t₂ => s!"Can't unify type\n  {t₁}\nwith\n  {t₂}."
  | .Undefined s   => s!"Variable\n  {s}\nis not in scope."
  | .NonApplicable => s!"This expression is not applicable."
  | .WrongCardinal n => s!"Incorrect cardinality. Expected {n}"
  | .Duplicates (mkTV a) b =>  s!"Unbounded fixpoint constructor does not exist in a strongly normalized system.\nNote: unifying {a} and {b} results in μ{a}. {b}, which isn't allowed."
open TypingError
abbrev Env := Std.HashMap String Scheme
abbrev Infer σ := StateRefT Nat $ EST TypingError σ
abbrev Subst := Std.HashMap TV MLType
instance : ToString Env where
  toString e := e.toList.foldl (init := "") fun a (v, t) => s!"{v} : {t} " ++ a

def curry : MLType -> MLType
  | t₁ ->' t₂ =>
    go t₁ |>.foldr (· ->' ·) t₂
  | t => t
where
  go | t₃ ×'' t₄ => go t₃ ++ go t₄ | t => [t]

@[inline] abbrev tInt := TCon "Int"
@[inline] abbrev tBool := TCon "Bool"
@[inline] abbrev tString := TCon "String"
@[inline] abbrev tUnit := TCon "Unit"
@[inline] abbrev typeOf (e : Env) s := e.get? s
abbrev dE : List (String × Scheme) :=
  [ ("add'", .Forall []      $ tInt ×'' tInt ->' tInt)
  , ("sub'", .Forall []      $ tInt ×'' tInt ->' tInt)
  , ("mul'", .Forall []      $ tInt ×'' tInt ->' tInt)
  , ("div'", .Forall []      $ tInt ×'' tInt ->' tInt)
  , ("eq'",  .Forall [⟨"α"⟩] $ TVar ⟨"α"⟩ ×'' TVar ⟨"α"⟩ ->' tBool)
  , ("not",  .Forall []      $ tBool ->' tBool)
  , ("id",   .Forall [⟨"α"⟩] $ TVar ⟨"α"⟩ ->' TVar ⟨"α"⟩)
  , ("zero", .Forall []      $ tInt)
  , ("succ", .Forall []      $ tInt ->' tInt)]



abbrev defaultE : Env := .ofList $
  dE.foldl (init := []) fun a p@(sym, .Forall c ty) =>
    if sym.endsWith "\'"
    then p :: (sym.dropRight 1, .Forall c $ curry ty) :: a
    else p :: a

class Rewritable (α : Type) where
  apply : Subst -> α -> α
  fv    : α -> Std.HashSet TV
open Rewritable

namespace Rewritables
def diff [BEq α] [Hashable α] (s₁ s₂ : Std.HashSet α) :=
  s₂.fold (fun a s => if s ∈ s₁ then s₁.erase s else a) s₁
instance [BEq α] [Hashable α] : SDiff (Std.HashSet α) := ⟨diff⟩

def applyT : Subst -> MLType -> MLType
  | _, s@(TCon _) => s
  | s, t@(TVar a) => s.getD a t
  | s, t₁ ×'' t₂ => applyT s t₁ ×'' applyT s t₂
  | s, t₁ ->' t₂ => applyT s t₁ ->' applyT s t₂

def fvT : MLType -> Std.HashSet TV
  | TCon _ => ∅ | TVar a => {a} | t₁ ->' t₂ | t₁ ×'' t₂ => fvT t₁ ∪ fvT t₂

instance : Rewritable MLType := ⟨applyT, fvT⟩
instance : Rewritable Scheme where
  apply s | .Forall as t =>
            .Forall as $ apply (as.foldr (fun a s => s.erase a) s) t
  fv      | .Forall as t => fv t \ Std.HashSet.ofList as
instance [Rewritable α] : Rewritable (List α) where
  apply := List.map ∘ apply
  fv    := List.foldr ((· ∪ ·) ∘ fv) ∅
instance : Rewritable Env where
  apply s e := e.map fun _ v => apply s v
  fv      e := fv e.values
end Rewritables
def gensym (n : Nat) : String :=
  let (q, r) := (n / 26, n % 26)
  let s := s!"'{Char.ofNat $ r + 97}"
  if q == 0 then s
  else q.toSubDigits.foldl (fun a s => a.push s) s
def normalize : Scheme -> Scheme
  | .Forall _ body =>
    let rec fv | TVar a => [a] | a ->' b | a ×'' b => fv a ++ fv b | TCon _ => []
    let ts := (List.rmDup $ fv body);
    let ord := ts.zip $ ts.foldrIdx (fun i _ a => mkTV (gensym i) :: a) []
    let rec normtype
      | a ->' b => normtype a ->' normtype b
      | a ×'' b => normtype a ×'' normtype b
      | TVar a  => match ord.lookup a with
                   | some x => TVar x
                   | none => panic! "some variable is undefined"
      | t => t
  .Forall (List.map Prod.snd ord) (normtype body)
def merge (s₁ s₂ : Subst) := s₁ ∪ s₂.map fun _ v => apply s₁ v
infixl : 65 " ∪' " => merge

def bindTV (a : TV) (t : MLType) : Infer σ Subst :=
  if t == TVar a then pure ∅
  else if a ∈ fv t then throw $ Duplicates a t
  else pure {(a, t)}

partial def unify : MLType -> MLType -> Infer σ Subst
  | l₁ ×'' r₁, l₂ ×'' r₂
  | l₁ ->' r₁, l₂ ->' r₂    => do
    let s₁ <- unify l₁ l₂
    let s₂ <- unify (apply s₁ r₁) (apply s₁ r₂)
    return s₂ ∪' s₁
  | TVar a, t | t, TVar a   => bindTV a t
  | t@(TCon a), t'@(TCon b) => if a == b then pure ∅ else throw $ NoUnify t t'
  | t₁, t₂                  => throw $ NoUnify t₁ t₂

@[inline] def fresh : Infer σ MLType :=
  modifyGet fun s => (TVar $ mkTV s!"?m{s}", s + 1)

def instantiate : Scheme -> Infer σ MLType
  | .Forall as t => do
    let as' <- as.mapM fun _ => fresh
    let s := as.zip as' |> Std.HashMap.ofList
    return apply s t

def generalize (E : Env) (t : MLType) : Scheme :=
  let as := fv t \ fv E |>.toList
  .Forall as t

def lookupEnv (s : String) (E : Env) : Infer σ (Subst × MLType) :=
  match E.get? s with
  | none => throw $ Undefined s
  | some s => instantiate s >>= fun t => pure (∅ , t)
infix :50 " ∈ₑ " => lookupEnv

mutual
def infer1 (E : Env) : (Subst × (MLType -> MLType)) -> Expr -> Infer σ (Subst × (MLType -> MLType))
  | (s, contT), e => do
    let (s', t) <- infer (apply s E) e
    return (s' ∪' s, contT ∘ (t ->' ·))
def infer (E : Env) : Expr -> Infer σ (Subst × MLType)
  | Var x => x ∈ₑ E

  | Fun x e => do
    let tv       <- fresh
    let E'       := E.insert x (.Forall [] tv)
    let (s₁, t₁) <- infer E' e
    pure (s₁, apply s₁ tv ->' t₁)

  | App e₁ e₂ => do
    let tv       <- fresh
    let (s₁, t₁) <- infer E e₁
    let (s₂, t₂) <- infer (apply s₁ E) e₂
    let s₃       <- unify (apply s₂ t₁) (t₂ ->' tv)
    pure (s₃ ∪' s₂ ∪' s₁, apply s₃ tv)

  | Let x e₁ e₂ => do
    let (s₁, t₁) <- infer E e₁
    let E'       := apply s₁ E
    let t'       := generalize E' t₁
    let (s₂, t₂) <- infer (E'.insert x t') e₂
    pure (s₂ ∪' s₁, t₂)

  | Cond c t e => do
    let tv         <- fresh
    let tv'        <- fresh
    let iter1      <- infer1 E (∅, id) c
    let iter2      <- infer1 E iter1 t
    let (s₁, cont) <- infer1 E iter2 e
    let s₂         <- unify (apply s₁ (cont tv')) (tBool ->' tv ->' tv ->' tv)
    pure (s₂ ∪' s₁, apply s₂ tv')

  | Prod' e₁ e₂ => do
    let (s₁, t₁) <- infer E e₁
    let (s₂, t₂) <- infer (apply s₁ E) e₂
    pure (s₂ ∪' s₁, (apply s₂ t₁) ×'' t₂)

  | CB _ => pure (∅, tBool)   | CI _  => pure (∅, tInt)
  | CS _ => pure (∅, tString) | CUnit => pure (∅, tUnit)
end

def closed : Std.HashMap TV MLType × MLType -> Scheme
  | (sub, ty) =>
    generalize ∅ (apply sub ty) |> normalize

def runInfer1 (e : Expr) (E : Env) : Except TypingError Scheme :=
  match runEST fun _ => infer E e |>.run' 0 with
  | .error e => throw e
  | .ok  res => pure $ closed res

def check1 (s : String) (E : Env := ∅) : String :=
  match Parsing.parse s with
  | .error e => toString e
  | .ok e    =>
    match runInfer1 e E with
    | .error e => toString e
    | .ok    s => toString s

def asType : MLType -> Type
  | t₁ ×'' t₂ => asType t₁ × asType t₂
  | t₁ ->' t₂ => asType t₁ -> asType t₂
  | TCon "Int" => Int | TCon "String" => String | TCon "Bool" => Bool | TCon "Unit" => Unit
  | TCon _ => Empty   | TVar _ => Empty

mutual
structure VEnv where
  env : Std.HashMap.Raw String Value

inductive Value where
  | VI (i : Int) | VB (b : Bool) | VS (s : String) | VU
  | VF (s : Symbol) (e : Expr) (e : VEnv)
  | VOpaque (s : Nat)
  | VEvalError (s : String)
  | VP (e₁ e₂ : Value) deriving Nonempty, Repr
end
instance : Inhabited Value := ⟨.VEvalError "something wrong during evaluation. Likely implementation error."⟩
def Value.toStr
  | VI v | VB v | VS v => reprStr v | VU => toString ()
  | VEvalError s => s
  | VOpaque s  => s!"<${s}::opaque>"
  | VF _ _ _   => "<fun>"
  | VP v₁ v₂   => toStr v₁ ++ "," ++ toStr v₂

@[inline, always_inline]abbrev Value.flatten1 : Value -> List Value
  | VP v₁ v₂ => [v₁] ++ [v₂]
  | t@_ => [t]

def binop : Nat -> Int -> Int -> Int
  | 0 => (· + ·) | 1 => (· - ·) | 2 => (· * ·) | 3 => (· / ·)
  | _ => panic! "Not defined"

open Value in instance : ToString Value := ⟨Value.toStr⟩ in
def callForeign (as : List Value) : Nat -> Value
  | t@0 | t@1 | t@2 | t@3 =>
    if let (VI i, VI i') := (as[0]!, as[1]!) then
      VI $ (binop t) i i'
    else unreachable!

  | 4 =>
    if let (VB b) := as[0]! then
      VB $ b.not
    else unreachable!

  | 5 =>
    let rec go : Value -> Value -> Except Value Bool
      | VI i, VI i' | VB i, VB i' | VS i, VS i' | VOpaque i, VOpaque i' =>
        pure $ i == i'
      | VU, VU => pure true
      | VF .., VF .. => throw $ VEvalError s!"equality handler is not implemented for function type"
      | VP l r, VP l' r' => (· && ·) <$> go l l' <*> go r r'
      | _, _ => unreachable!
    match go as[0]! as[1]! with
    | .ok x => VB x | .error e => e
  | n => .VOpaque n
in
partial def eval (E : VEnv) : Expr -> Except TypingError Value
  | CI v => pure $ VI v | CS v => pure $ VS v | CB v => pure $ VB v | CUnit => pure VU
  | Var x => match E.env.get? x with | some x => pure x | none => throw $ Undefined x
  | Fun x body => pure $ VF x body E
  | App f a => do
    let e' <- eval E f
    match e' with
    | VF s body E' =>
      let e <- eval E a
      let E' := E'.env.insert s e
      eval ⟨E'⟩ body
    | VOpaque n =>
      let a <- eval E a
      pure $ callForeign a.flatten1 n
    | _ => throw $ NonApplicable
  | Let x e body => do
    let e' <- eval E e
    let E' := E.env.insert x e'
    eval ⟨E'⟩ body
  | Cond c t e => do
    let e' <- eval E c
    match e' with
    | VB true => eval E t
    | VB false => eval E e
    | _       => throw $ WrongCardinal 2
  | Prod' e₁ e₂ => do
    pure $ VP (<-eval E e₁) (<-eval E e₂)

@[always_inline, inline] def parse! s := Parsing.parse s |>.toOption |>.get!
@[always_inline, inline] def eval! s (e : VEnv := ⟨∅⟩) := parse! s |> eval e |>.toOption |>.get!

def arityGen (prim : Symbol) (arity : Nat) (primE : VEnv := ⟨∅⟩) : Value :=
  let rec go s
  | 0 => App (Var prim) s
  | 1 => Fun s!"g1" (App (Var prim) (Prod' s $ Var "g1"))
  | t@(n + 2) =>
    Fun s!"g{t}" $ (go (Prod' s (Var s!"g{t}")) (n + 1))
  Option.get!
  $ Except.toOption
  $ eval primE
  $ Fun s!"g{arity}"
  $ Fun s!"g{arity - 1}"
  $ go (Prod' (Var s!"g{arity}") (Var s!"g{arity - 1}")) (arity - 2)

@[inline, always_inline]
abbrev ag (prim : Symbol) (arity : {n // n > 1}) (primE : VEnv := ⟨∅⟩) : Value :=
  arityGen prim arity primE

def prim :=
  [ ("id" ,   eval! "fun x -> x")
  , ("add'",  .VOpaque 0)
  , ("sub'",  .VOpaque 1)
  , ("mul'",  .VOpaque 2)
  , ("div'",  .VOpaque 3)
  , ("not",   .VOpaque 4)
  , ("eq'" ,  .VOpaque 5)]
def prim' : VEnv := ⟨.ofList prim⟩

scoped macro n:term "of!" s:term : term => `(($n, (ag (String.push $n '\'') ⟨$s, by omega⟩ prim')))
abbrev defaultVE : VEnv where
  env := .ofList $ prim
  ++ [ "add" of! 2
     , "sub" of! 2
     , "mul" of! 2
     , "div" of! 2
     , "eq"  of! 2]
  ++ [ ("zero",  eval! "0" prim')
     , ("succ",  eval! "fun x -> add' (x,1)" prim')]

def check1E (s : String) (E : Env := ∅) (VE : VEnv := ⟨∅⟩) : Except String String := do
  let e <- Parsing.parse s
  match runInfer1 e E, eval VE e with
  | .error s, _ => throw $ toString s
  | _, .error s => throw $ toString s
  | .ok s, .ok r =>
    pure $ toString r ++ " ⊢ " ++ toString s

end MLType

open MLType IO in def main : IO Unit := do
  let prompt := "λ> "
  setStdoutBuf false
  let stdin <- IO.getStdin
  repeat do
    print prompt
    let input <- IO.FS.Stream.getLine stdin
    if input.isEmpty then return ()
    else if input.startsWith "\n" then continue
    else match check1E input defaultE defaultVE with
         | .error s | .ok s => println! s
