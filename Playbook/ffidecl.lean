@[extern "lean_string_repeat"] def leanStringRepeat (c : Char) (n : Nat) : String :=
  go c "" n where
    go c acc
    | 0 => acc
    | _ + 1 => acc ++ c.toString

@[always_inline, inline] def Char.repeat (c : Char) (n : Nat) : String :=
  leanStringRepeat c n

@[extern "lean_disable_stdout_buffer"] opaque setStdoutBuf : Bool -> IO Unit

namespace PrettyPrint
--                      cmd      info
abbrev Spec := Array $ String × String


def calcMaxWidth (s : Spec) : Nat :=
  s.foldl (init := 0) (·.max ∘ (·.fst.length))

open IO in
def printMsg (s : Spec) (padsAfter : Nat := 2) (padChar := ' ') : IO Unit :=
  let maxWidth := calcMaxWidth s
  let pr := padChar.repeat
  s.forM fun (cmdStr, infoStr) =>
    let padding := maxWidth - cmdStr.length
    println s!"{pr padsAfter}{cmdStr}{pr padding}{pr padsAfter}{infoStr}\n"

end PrettyPrint
