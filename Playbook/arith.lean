import Parser
open Parser Char

inductive Arith where
  | tmTrue
  | tmFalse
  | tmIf : Arith -> Arith -> Arith -> Arith
  | tmSucc : Arith -> Arith
  | tmZero
  | tmPred : Arith -> Arith
  | tmIsZero : Arith -> Arith
deriving Repr, Nonempty, Inhabited

abbrev ArithParser := SimpleParser Substring Char

namespace Arith
mutual
private partial def term : ArithParser Arith :=
  spaces *>
  (first
    [ parseIf
    , constBool
    , constZero
    , parsePred
    , parseSucc
    , parseIsZero
    ] <|> between '(' term ')')
  <* spaces
private partial def between (l : Char) (t : ArithParser Arith) (r : Char) : ArithParser Arith :=
  char l *> t <* char r

private partial def spaces : ArithParser Unit :=
  dropMany <| tokenFilter [' ', '\n', '\r', '\t'].contains

private partial def constBool : ArithParser Arith :=
      (string "true" *> pure Arith.tmTrue)
  <|> (string "false" *> pure Arith.tmFalse)

private partial def constZero : ArithParser Arith :=
  char '0' *> pure Arith.tmZero

private partial def parseIf : ArithParser Arith := do
  let _ <- string "if"; spaces; let c <- term
  spaces
  let _ <- string "then"; spaces; let e₁ <- term
  spaces
  let _ <- string "else"; spaces; let e₂ <- term
  return tmIf c e₁ e₂
private partial def parsePred : ArithParser Arith := do
  let t <- string "pred" *> spaces *> term
  return tmPred t
private partial def parseIsZero : ArithParser Arith := do
  let t <- string "iszero" *> spaces *> term
  return tmIsZero t

private partial def parseSucc : ArithParser Arith := do
  let t <- string "succ" *> spaces *> term
  return tmSucc t
end

def parse (s : String) : Except String Arith :=
  match Parser.run (spaces *> term <* endOfInput) s with
  | .ok _ t => pure t
  | .error _ s => throw (toString s)
def reconstruct : Arith -> String
  | tmTrue => "true"
  | tmFalse => "false"
  | tmZero => "0"
  | tmIsZero t => s!"iszero {reconstruct t}"
  | tmPred t => s!"pred {reconstruct t}"
  | tmSucc t => s!"succ {reconstruct t}"
  | tmIf c e₁ e₂ => s!"if {reconstruct c} then {reconstruct e₁}\nelse {reconstruct e₂}"

def isNumeric | tmZero => true | tmSucc t => isNumeric t | _ => false
def isVal | tmTrue => true | tmFalse => true | t => if t.isNumeric then true else false

def eval1 : Arith -> Option Arith
  | tmIf tmTrue e₁ _ => .some e₁
  | tmIf tmFalse _ e₂ => .some e₂
  | tmIf c e₁ e₂ => do let c <- eval1 c; .some <| tmIf c e₁ e₂
  | tmSucc t => do let t <- eval1 t; .some <| tmSucc t
  | tmPred tmZero => .some <| tmZero
  | tmPred (tmSucc t) => if t.isNumeric then .some t else none
  | tmPred t => do let t <- eval1 t; .some <| tmPred t
  | tmIsZero tmZero => .some tmTrue
  | tmIsZero (tmSucc t) => if t.isNumeric then .some tmFalse else none
  | tmIsZero t => do let t <- eval1 t; .some <| tmIsZero t
  | _ => none

partial def evalRec (t : Arith) : Arith :=
  let t' := t.eval1
  match t' with
  | some t => evalRec t
  | none => t

def eval : Arith -> Option Arith
  | tmTrue            => some tmTrue
  | tmFalse           => some tmFalse
  | tmZero            => some tmZero
  | tmIf c t1 t2      => do
      let c' <- eval c
      match c' with
      | tmTrue  => eval t1
      | tmFalse => eval t2
      | _       => none
  | tmSucc t          => do
      let t' <- eval t
      if t'.isNumeric then some (tmSucc t') else none
  | tmPred t          => do
      let t' <- eval t
      match t' with
      | tmZero        => some tmZero
      | tmSucc t''    => if t''.isNumeric then some t'' else none
      | _             => none
  | tmIsZero t        => do
      let t' <- eval t
      match t' with
      | tmZero        => some tmTrue
      | tmSucc t''    => if t''.isNumeric then some tmFalse else none
      | _             => none
instance : Inhabited (Bool ⊕ Nat) := ⟨.inl false⟩
def res (t : Arith) : String :=
  let rec asLean : Arith -> Bool ⊕ Nat
    | tmZero => .inr 0
    | tmFalse => .inl false
    | tmTrue => .inl true
    | tmSucc t => match asLean t with
                  | .inr t => .inr (t + 1)
                  | .inl _ => unreachable!
    | tmPred t => match asLean t with
                  | .inr t => .inr (t - 1)
                  | .inl _ => unreachable!
    | _ => unreachable!
  match asLean t with
  | .inl t => toString t
  | .inr t => toString t

end Arith
#eval Arith.parse "if (if true then true else 0) then 0 else succ 0" |>.map Arith.evalRec
open IO.FS.Stream in
def print' (s : String) : IO Unit := IO.getStdout >>= fun out => putStr out s *> IO.FS.Stream.flush out in
def println' (s : String) : IO Unit := print' s!"{s}\n"

def main : IO Unit := do
  let prompt := "λ> "
  let stdin <- IO.getStdin
  repeat do
    print' prompt
    let input <- IO.FS.Stream.getLine stdin
    if input.isEmpty then return ()
    match Arith.parse input with
    | .ok s =>
      match s.eval with
      | some t => println' <| s!"{input}⊢ {reprStr t} → {t.res}"
      | none => println' "SyntaxError somewhere"
    | .error s => println' s
