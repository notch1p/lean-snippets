/-
/--

[result]
def getLast._rarg (x_1 : obj) (x_2 : ◾) : obj :=
  let x_3 : obj := proj[1] x_1;
  inc x_3;
  case x_3 : obj of
  List.nil →
    let x_4 : obj := proj[0] x_1;
    inc x_4;
    dec x_1;
    ret x_4
  List.cons →
    dec x_1;
    let x_5 : u8 := isShared x_3;
    case x_5 : u8 of
    Bool.false →
      let x_6 : obj := getLast._rarg x_3 ◾;
      ret x_6
    Bool.true →
      let x_7 : obj := proj[0] x_3;
      let x_8 : obj := proj[1] x_3;
      inc x_8;
      inc x_7;
      dec x_3;
      let x_9 : obj := ctor_1[List.cons] x_7 x_8;
      let x_10 : obj := getLast._rarg x_9 ◾;
      ret x_10
def getLast (x_1 : ◾) : obj :=
  let x_2 : obj := pap getLast._rarg;
  ret x_2
-/
def getLast : (as : List α) -> as ≠ [] -> α
  | [x], h => x
  | x :: y :: xs, h =>
    getLast (y :: xs) $ by simp -- test
-/
axiom wrong : ∀ xs : List α, xs ≠ []

set_option trace.compiler.ir.result true in
/--

[result]
def head._rarg (x_1 : @& obj) (x_2 : ◾) : obj :=
  let x_3 : obj := proj[0] x_1;
  inc x_3;
  ret x_3
def head (x_1 : ◾) : obj :=
  let x_2 : obj := pap head._rarg._boxed;
  ret x_2
def head._rarg._boxed (x_1 : obj) (x_2 : obj) : obj :=
  let x_3 : obj := head._rarg x_1 x_2;
  dec x_1;
  ret x_3
  -/
def head : (as : List α) -> as ≠ [] -> α
  | x :: _, _ => x

def main : IO Unit :=
  println! head ([1] : List Nat) $ wrong _
