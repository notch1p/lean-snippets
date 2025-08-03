import Parser
import Playbook.dependentPP
open Parser Parser.Char

infixr : 60 " <$ " => Functor.mapConst
infixr : 60 " $> " => flip Functor.mapConst

abbrev Symbol := String

inductive Expr where
  | CI (i : Int)       | CS (s : String)        | CB (b : Bool) | CUnit
  | App (e₁ e₂ : Expr) | Cond (e₁ e₂ e₃ : Expr) | Let (a : Symbol) (e₁ e₂ : Expr)
  | Fix (e : Expr)     | Fixcomb (e : Expr)
  | Var (s : Symbol)   | Fun (a : Symbol) (e : Expr)
  | Prod' (e₁ e₂ : Expr)
deriving Repr, BEq, Nonempty
instance : Inhabited Expr := ⟨Expr.CUnit⟩

abbrev Binding := Symbol × Expr

inductive Associativity | leftAssoc | rightAssoc deriving Ord, Repr

instance : ToString Associativity where
  toString
  | .leftAssoc => "left"
  | .rightAssoc => "right"

abbrev OpIndex := Nat × String
instance opIndexOrd : Ord OpIndex where
  compare 
  | (n, a), (n', a') => 
    let n := compare n' n; let a := compare a a'
    if a matches .eq then .eq else n.then a

/--(ℕ × String) ↦ ε × Associativity-/
abbrev OpTable α := Std.TreeMap OpIndex ((α -> α -> α) × Associativity) opIndexOrd.compare

namespace Lexing

open Std in

abbrev TParser := SimpleParserT Substring Char $ StateM $ OpTable Expr

abbrev INT := @ASCII.parseInt

def alphanum' [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m]
  : ParserT ε σ Char m Char :=
  withErrorMessage "expected letter or digit character or \'" do
    tokenFilter fun c => c.isAlphanum || c == '\'' || c == '_'
def alpha' [Parser.Stream σ Char] [Parser.Error ε σ Char] [Monad m]
  : ParserT ε σ Char m Char :=
  withErrorMessage "expected alphabetic character" do
    tokenFilter fun c => if c >= 'a' then c <= 'z' else c == '_' || c >= 'A' && c <= 'Z'

def void : TParser α -> TParser Unit := (() <$ ·)

def MLCOMMENTL := void $ string "(*"
def MLCOMMENTR := void $ string "*)"

def comment : TParser Unit :=
  withBacktracking $
   (string "NB.") *> dropUntil (endOfInput <|> void eol) anyToken

def spaces : TParser Unit :=
  dropMany <| MLCOMMENTR <|> MLCOMMENTL <|> void ASCII.whitespace <|> comment <|> void eol

abbrev ws (t : TParser α) := spaces *> t <* spaces

def reserved := 
  #["infixl", "infixr","let", "rec", "in", "fn", "fun", "=", "if", "else", "then", "->", ";;"]

open ASCII in def ID' : TParser String :=
  withErrorMessage "identifier" do
      (· ++ ·)
  <$> (Char.toString <$> alpha')
  <*> foldl String.push "" alphanum'

def ID : TParser String := do
  let id <- ID'
  if reserved.contains id then throwUnexpectedWithMessage none s!"expected identifier, not keyword {id}"
  else ws $ pure id
abbrev kw (s : String) : TParser Unit := ws 
                                         $ withBacktracking
                                         $ withErrorMessage "keyword"
                                         $ string s
                                         *> notFollowedBy alphanum'

abbrev LET   := kw "let"
abbrev IN    := kw "in"
abbrev FUN   := kw "fun"
abbrev EQ    := kw "="
abbrev IF    := kw "if"
abbrev ELSE  := kw "else"
abbrev THEN  := kw "then"
abbrev ARROW := kw "->"
abbrev COMMA := kw ","
abbrev REC   := kw "rec"
abbrev END   := kw ";;"

abbrev ADD   := "+"
abbrev SUB   := "-"
abbrev MUL   := "*"
abbrev DIV   := "/"
abbrev DOL   := "$"
abbrev ATT   := "@@"

abbrev INFIXL := kw "infixl"
abbrev INFIXR := kw "infixr"

end Lexing

def List.mapReduce! [Inhabited β] (mapf : α -> β) (f : β -> β -> β) (xs : List α) : β :=
  match xs with
  | [] => default
  | x :: xs => xs.foldl (flip $ flip f ∘ mapf) (mapf x)

namespace Parsing
open Lexing Expr
section helper
variable {ε σ τ m α} 
         [Parser.Stream σ τ] 
         [Parser.Error ε σ τ] 
         [Monad m]
/--
  `chainl1 p op` parses *one* or more occurrences of `p`, separated by `op`. Returns
  a value obtained by a **left** associative application of all functions returned by `op` to the
  values returned by `p`.
  - if there is exactly one occurrence of `p`, `p` itself is returned touched.
-/
partial def chainl1 
  (p : ParserT ε σ τ m α)
  (op : ParserT ε σ τ m (α -> α -> α)) : ParserT ε σ τ m α := do
  let x <- p; rest x where
  rest x :=
    (do let f <- op; let y <- p; rest (f x y)) <|> pure x

partial def chainr1
  (p : ParserT ε σ τ m α)
  (op : ParserT ε σ τ m (α -> α -> α)) : ParserT ε σ τ m α := do
  let x <- p; rest x where
  rest x :=
    (do let f <- op; chainr1 p op <&> f x) <|> pure x

@[inline] def η₂ s :=
  fun e₁ e₂ => App (App s e₁) e₂

@[inline] def infixOp (op : Symbol) (e : α -> α -> α) : TParser $ α -> α -> α :=
  (kw op) *> pure e

@[inline] def link s := η₂ $ Var s

@[inline] def buildOpParser
  (p : TParser α)
  (table : OpTable α)
  : TParser α := table.foldl (init := p) fun a (_, s) (e, assoc) =>
    match assoc with
    | .leftAssoc => chainl1 a $ infixOp s e
    | .rightAssoc => chainr1 a $ infixOp s e

def first'
  (ps : Array $ ParserT ε σ τ m α)
  (combine : ε → ε → ε := fun _ => id)
  : ParserT ε σ τ m α := do
  let rec go n (h : n <= ps.size) e s :=
    match _ : n with
    | 0 => return .error s e
    | m + 1 => 
      let pss := ps.size
      have : m < pss := Nat.le_trans (Nat.lt.base _) h
      let savePos := Stream.getPosition s
      ps[pss - m.succ] s >>= fun
      | .ok s v => return .ok s v
      | .error s f =>
        go m (Nat.le_of_lt this) (combine e f) (Stream.setPosition s savePos)
  go ps.size (Nat.le.refl) (Error.unexpected (<- getPosition) none)

end helper

open Associativity in
def opTable : OpTable Expr := .ofArray (cmp := opIndexOrd.compare)
  #[ ((0   , DOL)     , (App       , rightAssoc))
   , ((0   , ATT)     , (App       , rightAssoc))
   , ((50  , "=")     , (link "eq" , leftAssoc))
   , ((65  , ADD)     , (link "add", leftAssoc))
   , ((65  , SUB)     , (link "sub", leftAssoc))
   , ((70  , MUL)     , (link "mul", leftAssoc))
   , ((70  , DIV)     , (link "div", leftAssoc))]

mutual

private partial def funapp : TParser Expr := 
  chainl1 atom (pure App)

private partial def atom : TParser Expr :=
  first' $ #[ parenthesized prodExp
            , letrecExp                  , letExp
            , fixpointExp                , funExp
            , condExp                    , intExp
            , strExp                     , varExp
            , parenthesized opSection]
            |>.map ws

private partial def prodExp : TParser Expr := do
  let es <- sepBy COMMA parseExpr
  return match h : es.size with
         | 0 => CUnit
         | 1 => es[0]
         | _ + 2 => es[0:es.size - 1].foldr Prod' es[es.size - 1]

private partial
def between (l : Char) (t : TParser Expr) (r : Char) : TParser Expr :=
  ws (char l) *> t <* ws (char r)
private partial
def parenthesized (t : TParser Expr) : TParser Expr := between '(' t ')'

private partial def intExp      : TParser Expr := ws INT >>= pure ∘ CI

private partial def strExp      : TParser Expr :=
  CS <$> (char '"' *>
            foldl .push "" (tokenFilter (· != '"'))
          <* char '"')

private partial def varExp      : TParser Expr :=
  ID >>= pure ∘ fun
          | "true"                => CB true
          | "false"               => CB false
          | v                     => Var v

private partial def opMatcher (arr : Array $ Nat × String) : TParser OpIndex :=
  first' $ arr.map fun (prec, s) => string s >>= pure ∘ (prec, ·)

private partial def opSection   : TParser Expr := do
  let e₁ <- option? parseExpr
  let tb <- get
  let k <- opMatcher tb.keysArray
  let e₂ <- option? parseExpr
  if let some (op, _) := tb.get? k then
    match e₁, e₂ with
    | some e₁, some e₂ =>         return op e₁ e₂
    | _, some e₂ =>               return Fun "y" $ (flip op $ e₂) $ Var "y"
    | some e₁, _ =>               return Fun "x" $ op e₁ $ Var "x"
    | none, none =>               return Fun "x" $ Fun "y" $ op (Var "x") (Var "y")
  else unreachable!

private partial def letExp      : TParser Expr := do
  LET let id <- ID
      let a <- takeMany ID
  EQ; let e₁ <- parseExpr
  IN; let e₂ <- parseExpr         return Let id (a.foldr Fun e₁) e₂

private partial def letrecExp   : TParser Expr := do
  LET; REC
      let id <- ID
      let a <- takeMany ID
  EQ  let e₁ <- parseExpr
  IN  let e₂ <- parseExpr         return Let id (Fix $ Fun id $ a.foldr Fun e₁) e₂

private partial def fixpointExp : TParser Expr := do
  REC;
  match <-option? parseExpr with
  | some e =>                     return Fixcomb e
  | none   =>                     return Var "rec"

private partial def funExp      : TParser Expr := do
  FUN   let var <- takeMany1 ID
  ARROW let e <- parseExpr        return var.foldr Fun e

private partial def condExp     : TParser Expr := do
  IF   let c <- parseExpr
  THEN let e₁ <- parseExpr
  ELSE let e₂ <- parseExpr        return Cond c e₁ e₂

private partial def parseExpr : TParser Expr := 
  buildOpParser funapp =<< get

end

def infixlDecl : TParser (Symbol × Expr) := do
  INFIXL; let i <- intExp let s <- strExp
  match s, i with
  | CS op, CI i =>
    let op := op.trim
    ARROW let e <- parseExpr
    modify (·.insert (i.toNat, op) (η₂ e, .leftAssoc))
    return (op, e)
  | _, _ => unreachable!

def infixrDecl : TParser (Symbol × Expr) := do
  INFIXR; let i <- intExp let s <- strExp
  match s, i with
  | CS op, CI i =>
    let op := op.trim
    ARROW let e <- parseExpr
    modify (·.insert (i.toNat, op) (η₂ e, .rightAssoc))
    return (op, e)
  | _, _ => unreachable!

def letDecl : TParser Binding := do
  LET; let id <- ID; let a <- takeMany ID; EQ; let b <- parseExpr;  return (id, a.foldr Fun b)
def letrecDecl : TParser Binding := do
  LET;
  REC; let id <- ID; let a <- takeMany ID; EQ; let b <- parseExpr;  return (id, Fix $ Fun id $ a.foldr Fun b)

def value p := show TParser Binding from ("_", ·) <$> p

def declaration := first' #[ letrecDecl
                          , letDecl
                          , infixlDecl
                          , infixrDecl
                          , value parseExpr]

def module : TParser $ Array Binding :=
  sepBy (optional END) declaration <* optional END

def parse (s : String) : Except String Expr :=
  match spaces *> parseExpr <* endOfInput |>.run s |>.run' opTable with
  | .ok _ t    => pure t
  | .error _ e => throw (toString e)

def parseModule (s : String) : EStateM String (OpTable Expr) (Array Binding) := do
  match spaces *> module <* endOfInput |>.run s |>.run (<- get) with
  | (.ok _ t, s)    => set s *> pure t
  | (.error _ e, _) => throw (toString e)

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
  | a ×'' b => paren (prod? a) (toStr a) ++ " × " ++ toStr b
  | a ->' b =>
    paren (arr? a) (toStr a) ++ " → " ++ toStr b where
    paren b s := bif b then s!"({s})" else s
    arr? | TArr _ _ => true | _ => false
    prod? | TProd _ _ => true | _ => false

instance : ToString MLType := ⟨MLType.toStr⟩

inductive Scheme where
  | Forall : List TV -> MLType -> Scheme deriving Repr, BEq, Ord

instance : ToString Scheme where
  toString
  | .Forall [] t => toString t
  | .Forall ts t => s!"∀ {ts.mapReduce! toString (· ++ " " ++ ·)}. {toString t}"

instance : Inhabited Scheme where
  default := .Forall [] (MLType.TCon "False")

namespace MLType open TV Expr

inductive TypingError
  | NoUnify (t₁ t₂ : MLType)
  | Undefined (s : String)
  | WrongCardinal (n : Nat)
  | Duplicates (t : TV) (T : MLType) deriving Repr

instance : ToString TypingError where
  toString
  | .NoUnify t₁ t₂ => s!"Can't unify type\n  {t₁}\nwith\n  {t₂}."
  | .Undefined s   => s!"Variable\n  {s}\nis not in scope.\n\
                         Note: use letrec or fixcomb if this is a recursive definition"
  | .WrongCardinal n => s!"Incorrect cardinality. Expected {n}"
  | .Duplicates (mkTV a) b =>
    s!"\
    Unbounded fixpoint constructor does not exist in a strongly normalized system.\n\
    Note: unifying {a} and {b} results in μ{a}. {b}, which isn't allowed.\n\
    Note: recursion is supported primitively via letrec \n\
    Note: or unsafely via fixpoint combinator `rec`"
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

local instance : CoeHead String TV := ⟨mkTV⟩
local instance : CoeTail TV MLType := ⟨TVar⟩

@[inline] abbrev tInt := TCon "Int"
@[inline] abbrev tBool := TCon "Bool"
@[inline] abbrev tString := TCon "String"
@[inline] abbrev tUnit := TCon "Unit"

abbrev dE : List (String × Scheme) :=
  [ ("rec"  , .Forall ["α"] $ ("α" ->' "α") ->' "α")
  , ("__add", .Forall []    $ tInt ×'' tInt ->' tInt)
  , ("__sub", .Forall []    $ tInt ×'' tInt ->' tInt)
  , ("__mul", .Forall []    $ tInt ×'' tInt ->' tInt)
  , ("__div", .Forall []    $ tInt ×'' tInt ->' tInt)
  , ("__eq" , .Forall ["α"] $ "α" ×'' "α" ->' tBool)
  , ("not"  , .Forall []    $ tBool ->' tBool)
  , ("id"   , .Forall ["α"] $ "α" ->' "α")
  , ("succ" , .Forall []    $ tInt ->' tInt)]

variable {σ : Type}

abbrev defaultE : Env := .ofList $
  dE.foldl (init := []) fun a p@(sym, .Forall c ty) =>
    if sym.startsWith "__"
    then p :: (sym.drop 2, .Forall c $ curry ty) :: a
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
/--
  perform exactly 1 step of sequential inferrence in CPS style.
  Sequential inferrence is manually unwinded in
  `infer` e.g. `If` `Fix` branch.
  It is done this way so that Lean doesn't complain about termination problem.
    (it can get complicated as `infer1` is mutually recursive with `infer`)
  - returns a continuation and a modified substitution map.
-/
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

  | Fixcomb e => do
    let tv <- fresh
    let tv' <- fresh
    let (s₁, cont) <- infer1 E (∅, id) e
    let s₂ <- unify (apply s₁ (cont tv')) ((tv ->' tv) ->' tv)
    pure (s₂ ∪' s₁, apply s₂ tv')

  | Fix (Fun fname fbody) => do
    let tv <- fresh
    let E' := E.insert fname (.Forall [] tv)
    let (s₁, t₁) <- infer E' fbody
    let s₂ <- unify (apply s₁ tv) t₁
    let s := s₂ ∪' s₁
    pure (s₂ ∪' s₁, apply s tv)
  | Fix e => do
    let (s₁, t₁) <- infer E e
    pure (s₁, t₁)

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

def inferToplevel (b : Array Binding) (E : Env) : Except TypingError Env :=
  b.foldlM (init := E) fun E (id, expr) => runInfer1 expr E <&> E.insert id

def check1 (s : String) (E : Env := defaultE) : String :=
  match Parsing.parse s with
  | .error e => toString e
  | .ok e    =>
    match runInfer1 e E with
    | .error e' => toString e' ++ s!"AST: {reprStr e}"
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
  | VF (s : Symbol) (E : Expr) (e : VEnv)
  | VFRec (s: Symbol) (e : Expr) (E : VEnv)
  | VOpaque (s : Nat)
  | VEvalError (s : String)
  | VP (e₁ e₂ : Value) deriving Nonempty
end
instance : Inhabited Value := ⟨.VEvalError "something wrong during evaluation.\n\
                                            Note: Likely implementation error or a breach of type safety\n\
                                            Note: The type system is unsound by design\n\
                                            Note: because the primitive `rec` fixpoint combinator is present\n"⟩
def Value.toStr : Value -> String
  | VI v | VB v => toString v | VU => toString ()
  | VS v => reprStr v
  | VEvalError s => s
  | VOpaque s   => s!"<${s}::prim>"
  | VF _ _ _    => "<fun>"
  | VFRec _ _ _ => "<recfun>"
  | VP v₁ v₂    => paren (prod? v₁) (toStr v₁) ++ "," ++ toStr v₂ where
    paren b s := bif b then s!"({s})" else s
    prod? | VP _ _ => true | _ => false

def binop (n : Nat) (h : n ∈ [1,2,3,4]) : Int -> Int -> Int :=
  match n with
  | 1 => (· + ·) | 2 => (· - ·) | 3 => (· * ·) | 4 => (· / ·)

open Value in instance : ToString Value := ⟨Value.toStr⟩ in
def callForeign (as' : Value) (n : Nat) : Value :=
  let as := match as' with | VP v₁ v₂ => [v₁, v₂] | _ => [as']
  have : List.length as > 0 := by cases as' <;> simp[as]
  match h : n with
  | 1 | 2 | 3 | 4 =>
    if let t@(VI i, VI i') := (as[0], as[1]!) then
      VI $ (binop n $ by simp[h]) i i'
    else unreachable!
  | 5 =>
    if let (VB b) := as[0] then
      VB $ b.not
    else unreachable!
  | 6 =>
    let rec go : Value -> Value -> Except Value Bool
      | VI i, VI i' | VB i, VB i' | VS i, VS i' | VOpaque i, VOpaque i' =>
        pure $ i == i'
      | VU, VU => pure true
      | VF .., VF .. => throw $ VEvalError s!"equality handler is not implemented for function type"
      | VP l r, VP l' r' => (· && ·) <$> go l l' <*> go r r'
      | x, y => unreachable!
    match go as[0] as[1]! with
    | .ok x => VB x | .error e => e
  | 7 => if let (VI i) := as[0] then VI $ i + 1 else unreachable!

  | n => .VOpaque n
in
partial def eval (E : VEnv) : Expr -> Except TypingError Value
  | CI v => pure $ VI v | CS v => pure $ VS v | CB v => pure $ VB v | CUnit => pure VU
  | Var x => match E.env.get? x with | some x => pure x | none => throw $ Undefined x
  | Fun x body => pure $ VF x body E
  | Fix e | Fixcomb e =>
    eval E e >>= fun
    | VF fname fbody E' =>
      pure $ VFRec fname fbody E'
    | _ => unreachable!
  | App f a => do
    match <- eval E f with
    | VF s body E' =>
      let e <- eval E a
      let E' := E'.env.insert s e
      eval ⟨E'⟩ body
    | VOpaque n =>
      let a <- eval E a
      pure $ callForeign a n
    | self@(VFRec fname fbody E') =>
      let e <- eval E a
      let recE := E'.env.insert fname self
      match fbody with
      | Fun x body =>
        eval ⟨recE.insert x e⟩ body
      | _ => unreachable!
    | _ => unreachable!
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
  [ ("id"   , eval! "fun x -> x")
  , ("rec"  , .VOpaque 0)
  , ("__add", .VOpaque 1)
  , ("__sub", .VOpaque 2)
  , ("__mul", .VOpaque 3)
  , ("__div", .VOpaque 4)
  , ("not"  , .VOpaque 5)
  , ("__eq" , .VOpaque 6)
  , ("succ" , .VOpaque 7)]
def prim' : VEnv := ⟨.ofList prim⟩

scoped macro n:term "of!" s:term : term => `(($n, (ag (String.append "__" $n) ⟨$s, by omega⟩ prim')))
abbrev defaultVE : VEnv where
  env := .ofList $ prim
  ++ [ "add" of! 2
     , "sub" of! 2
     , "mul" of! 2
     , "div" of! 2
     , "eq"  of! 2]

def evalToplevel (bs : Array Binding) (VE : VEnv) : Except TypingError VEnv :=
  bs.foldlM (init := VE) fun VE@⟨env⟩ (id, e) => (VEnv.mk ∘ env.insert id) <$> eval VE e

def interpret (PE : OpTable Expr) (E : Env) (VE : VEnv) (s : String) : IO (OpTable Expr × Env × VEnv) := do
  match Parsing.parseModule s PE with
  | .ok bs PE => 
     let E <- IO.ofExcept $ inferToplevel bs E |>.mapError toString
     let VE@{env} <- IO.ofExcept $ evalToplevel bs VE |>.mapError toString
     (PE, E, VE) <$ bs.forM fun (id, _) =>
       match E.get? id, env.get? id with
       | some t, some r => println! "{id} : {r} ⊢ {t}"
       | _, _ => pure ()
  | .error e _ => IO.throwServerError e

section PP open PrettyPrint Alignment

def EnvHeader := ["id", "type", "value"]
def alignE : Align EnvHeader := (left, left, right)
def genTable (E : Env) : VEnv -> TableOf EnvHeader
  | {env := VE} => E.keysArray.map fun k =>
    (k, toString $ E.get! k, toString $ VE.get! k)

def PEnvHeader := ["op", "prec", "assoc"]
def genTableOp (PE : OpTable Expr) : TableOf PEnvHeader :=
  PE.toArray.map fun ⟨(prec, sym), (_, assoc)⟩ =>
    (sym, toString prec, toString assoc)
def alignPE : Align PEnvHeader := (left, right, left)

def HelpHeader := ["cmd", "info"]
def alignH : Align HelpHeader := (right,left)
def helpMsg : TableOf HelpHeader :=
  #[ ("#dump", "dump the REPL environment in table form")
   , ("#load <path>+", "load src from <path>+ (that doesn't contain spaces) into REPL")
   , ("#help", "show this help string")
   , ("#ast <exp|decl>", "display the parsetree of <exp> or <decl>")]

end PP
end MLType

open PrettyPrint (tabulate) in
open MLType IO in
def main : IO Unit := do
  setStdoutBuf false

  let motd := "A basic language using Hindley-Milner type system with a naive interpreted implementation.\n\
               For language specifications see source: Playbook/hm.lean\n\
               Type #help;; to check available commands.\n\
               To exit press <C-d> (Unix) or <C-z> if on Windows."
  let mut prompt := "λ> "
  let mut buf := ""

  let stdin <- IO.getStdin
  let E <- mkRef defaultE
  let VE <- mkRef defaultVE
  let PE <- mkRef Parsing.opTable
  println! motd

  repeat do
    let pe <- PE.get
    let e <- E.get
    let ve <- VE.get

    print prompt
    prompt := ".. "

    let input <- FS.Stream.getLine stdin
    buf := buf ++ input |>.trimLeft

    if input.isEmpty then return ()
    if !input.trimRight.endsWith ";;" then continue
    if input.startsWith "\n" then continue

    if buf.startsWith "#help" then
      print $ tabulate "Commands" {align := alignH} helpMsg
    else if buf.startsWith "#ast" then
      match (Parsing.parseModule $ buf.drop 4).run pe with
      | .ok b _  => println! reprStr b
      | .error e _ => println! e
    else if buf.startsWith "#dump" then
      println $ tabulate "REPL Environment" {align := alignE}  $ genTable e ve
      print $ tabulate "Operators" {align := alignPE} $ genTableOp pe
    else if buf.startsWith "#load" then
      (buf.splitOn " ").tail |>.forM fun path => do
        if !path.isEmpty then
          try
            let fs <- FS.readFile $ path.takeWhile fun c => c != ';' && !c.isWhitespace
            println fs
            let (PE', E', VE') <- interpret pe e ve fs
            PE.set PE' *> E.set E' *> VE.set VE'
          catch e => 
            println! e;
            println! 
              PrettyPrint.Text.bold 
                "NOTE: Evaluation context is restore as there are errors.\n\
                 Fix those then #load again to update it." true
    else try
      let (PE', E', VE') <- interpret pe e ve buf
      PE.set PE' *> E.set E' *> VE.set VE'
    catch e => println! e

    buf := ""
    prompt := "λ> "

