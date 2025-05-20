import Playbook.doug

mutual
def configFromArgs : List String -> (c : Config := {}) -> (s : List System.FilePath := []) -> (Option Config) × List System.FilePath
  | [], c, s => (some c, s)
  | x :: xs, c, s =>
    modifyConfig xs s x c
  termination_by ls => (sizeOf ls, 0)
  decreasing_by
    simp
    · apply Prod.Lex.left
      case h =>
        simp
        apply Nat.pos_of_neZero


def modifyConfig (xs : List String) (s : List System.FilePath) : String -> Config -> (Option Config) × List System.FilePath
  |"-h", _  | "--help",   _ => (none, [])
            | "--ascii",  c => configFromArgs xs {c with useASCII   := true} s
            /- lean sees `modifyConfig xs c s.. = configFromArgs xs...`
               where there isn't a decreasing measure `xs`. instead of `xs`, we use
               `(xs, 0 | 1)` instead to order the calls.
               so that `(xs, 0) < (xs, 1)` is given by `Prod.Lex.right`.
               In this case, `configFromArgs` is assigned measure `(xs, 0)` while
               any other function where the non-decreasing calls of `xs` are is given
               `(xs, 1)` so that `modifyConfig xs c s.. = configFromArgs xs...` are
                                 `~~~~~~(xs, 1)~~~~~~     ~~~~~(xs, 0)~~~~~   `
               still decreasing.
            -/
  |"-a",  c | "--hidden", c => configFromArgs xs {c with showHidden := true} s
  |"-p",  c | "--plain",  c => configFromArgs xs {c with color      := false} s
  |"-d",  c | "--depth",  c =>
    match xs with
    | [] => (some c, s)
    | y :: ys =>
      match y.toNat? with
      | some n => configFromArgs ys {c with maxdepth := n} s
      | none => modifyConfig ys s y c
  | p, c => if p.startsWith "--"
            || p.startsWith "-"
            then (none, [""]) else configFromArgs xs c (p :: s)
  termination_by (sizeOf xs, 1)

end
open IO in
def main (args : List String) : IO UInt32 := do
  match configFromArgs args with
  | (some config@{maxdepth,..}, s) =>
    let cwd <- IO.currentDir
    let template d : IO String := do
      let s <- mkRef ∅
      dirTree d maxdepth s |>.run config
      let {s, fdCount := (d, f)} <- s.get
      return s ++ boldYellow
          s!"Total of {f} files, in {d} dirs"
          config.color
    let workseq <- (if s.isEmpty then [cwd] else s) |>.mapM fun d => template d |>.asTask
    workseq.forM $ println ∘ (·.get.toOption.get!)
    return 0
  | (none, []) => printHelp; return 0
  | (none, _) =>
    printHelp
    eprintln s!"Unknown args in {repr args}\n"
    return 1
