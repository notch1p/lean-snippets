@[extern "lean_string_repeat"] private def leanStringRepeat (c : @&Char) (n : @&Nat) : String :=
  go c "" n where
  go c acc
  | 0 => acc
  | n + 1 => go c (acc.push c) n

/--
  performs better (w/ `memset`) if `c` is valid ascii char.
  Otherwise it is converted to a 4-bytes sequence in the ffi and requires linear time.
  `n` is `size_t` in runtime.
-/
@[always_inline, inline] def Char.repeat (c : Char) (n : Nat) : String :=
  leanStringRepeat c n

@[extern "lean_disable_stdout_buffer"] opaque setStdoutBuf : Bool -> IO Unit

namespace PrettyPrint
--                      cmd      info
abbrev Spec := Array $ String × String

def calcMaxWidth (s : Spec) : Nat :=
  s.foldl (init := 0) (·.max ∘ (·.fst.length))

open IO in
def formatMsg (s : Spec) (padsAfter : Nat := 2) (padChar := ' ') : String :=
  let maxWidth := calcMaxWidth s
  let pr := padChar.repeat
  s.foldl (init := "") fun a (cmdStr, infoStr) =>
    let padding := maxWidth - cmdStr.length
    if !cmdStr.startsWith "-" then
      s!"{a}{pr padsAfter}{cmdStr}{pr padding}{pr padsAfter}{infoStr}\n"
    else
      s!"{a}\n{pr padsAfter}{cmdStr}{pr padding}{pr padsAfter}{infoStr}\n"

end PrettyPrint
