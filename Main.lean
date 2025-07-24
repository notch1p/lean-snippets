import Playbook.doug


def parseArgs : List String -> (c : Config) -> (s : List System.FilePath) -> (Option Config) × List System.FilePath
  | [], c, s => (c, s)
  | x :: xs, c, s =>
    match x with
    |"-h"  | "--help"   => (none, [])
           | "--"       => (c, xs.map Coe.coe)
           | "--ascii"  => parseArgs xs {c with useASCII   := true}  s
    | "-a" | "--hidden" => parseArgs xs {c with showHidden := true}  s
    | "-s" | "--synced" => parseArgs xs {c with synced     := false} s
    | "-p" | "--plain"  => parseArgs xs {c with color      := false} s
           | "--async"  =>
             match xs with
             | [] => panic! "expecting number after --asyncdepth"
             | y :: ys => parseArgs ys {c with asyncdepth := y.toNat!} s
    | "-o" | "--out"    =>
      match xs with
      | [] => panic! "expecting filepath after --output"
      | y :: ys => parseArgs ys {c with output := y} s
    | "-d" | "--depth"  =>
      match xs with
      | [] => panic! "expecting number after --depth"
      | y :: ys => parseArgs ys {c with maxdepth := y.toNat!} s
    | p                 => if p.startsWith "-"
                           then (none, [p])
                           else parseArgs xs c (p :: s)

/-
set_option maxHeartbeats 10000000 in
mutual

partial def configFromArgs : List String -> (c : Config := {}) -> (s : List System.FilePath := []) -> (Option Config) × List System.FilePath
  | [], c, s => (some c, s)
  | x :: xs, c, s =>
    modifyConfig xs s x c
  termination_by ls => (sizeOf ls, 0) -- proof is too large.

partial def modifyConfig (xs : List String) (s : List System.FilePath) : String -> Config -> (Option Config) × List System.FilePath
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
  |"-s",  c | "--synced", c => configFromArgs xs {c with synced     := false} s
  |"-p",  c | "--plain",  c => configFromArgs xs {c with color      := false} s
  |"-d",  c | "--depth",  c =>
    match xs with
    | [] => (some c, s)
    | y :: ys =>
      configFromArgs ys {c with maxdepth := y.toNat!} s
  | p, c => if p.startsWith "--"
            || p.startsWith "-"
            then (none, [""]) else configFromArgs xs c (p :: s)
  termination_by (sizeOf xs, 1)

end
-/
open IO in
def main (args : List String) : IO UInt32 := do
  match parseArgs args {} [] with
  | (some config@{maxdepth,output,asyncdepth,..}, s) =>
    let cwd <- IO.currentDir
    let fs := if s.isEmpty then [cwd] else s
    let template d : IO String := do
      let s <- mkRef ∅
      dirTree d maxdepth asyncdepth s |>.run config
      let {s, fdCount := (d, f)} <- s.get
      return s ++ boldYellow
          s!"Total of {f} files, in {d} dirs"
          config.color
    let workseq <- fs |>.mapM fun d => template d |>.asTask
    if let some s := output then
      FS.withFile s .append fun handle =>
        Task.mapList
          (·.forM $ handle.putStr ∘ toString ∘ fun | .error e => e | .ok s => s)
          workseq
        |>.get
    else
      Task.mapList
        (·.forM $ println ∘ fun | .error e => e | .ok s => s)
        workseq
      |>.get
    return 0
  | (none, []) => printHelp; return 0
  | (none, s) =>
    printHelp
    eprintln s!"Unknown arg {s} in {args}\n"
    return 1
