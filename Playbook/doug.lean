import Playbook.ffidecl
structure Config where
  useASCII := false
  currentPrefix := ""
  showHidden := false
  maxdepth := 3
  color := true

structure Res where
  s : String := ""
  fdCount : Nat × Nat := (0, 0)

instance : EmptyCollection Res := ⟨{}⟩

open IO in
@[always_inline] def gotFile (s : Ref Res) : IO Unit :=
  s.modify fun s => {s with fdCount := (s.fdCount.1, s.fdCount.2 + 1)} in
@[always_inline] def gotDir (s : Ref Res) : IO Unit :=
  s.modify fun s => {s with fdCount := (s.fdCount.1 + 1, s.fdCount.2)}


abbrev ConfigIO := ReaderT Config IO

abbrev boldYellow (s : String)
  | true  => "\x1B[1;33m" ++ s ++ "\x1B[0m"
  | false => s

def Config.preFile (cfg : Config) :=
  if cfg.useASCII then "|--" else "├──"

def Config.preDir (cfg : Config) :=
  if cfg.useASCII then "|  " else "│  "

def Config.fileName (cfg : Config) (file : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"

def Config.dirName (cfg : Config) (dir : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"

def locally (change: Config -> Config) (action : ConfigIO α) : ConfigIO α :=
  fun cfg => action.run (change cfg)


inductive Entry where
  | file (s : String)
  | dir (s : String)

def toEntry (path : System.FilePath) : ConfigIO (Option Entry) := do
  match path.components.filter (· != "") |>.getLast? with
  | none => pure <| some <| .dir ""
  | some "." => pure <| some <| .dir "."
  | some ".." => pure <| some <| .dir ".."
  | some name =>
    if !(<-read).showHidden && name.startsWith "." then pure none
    else
      (<-path.isDir) |> fun
                        | true => pure $ some $ .dir name
                        | false => pure $ some $ .file name


@[always_inline] def showFileName (file : String) (res : IO.Ref Res) : ConfigIO Unit :=
  read >>= fun c => res.modify fun t@{s,..} => {t with s := s ++ c.fileName file ++ "\n"}

@[always_inline] def showDirName (dir : String) (res : IO.Ref Res) : ConfigIO Unit :=
  read >>= fun c => res.modify fun t@{s,..} => {t with s := s ++ c.dirName dir ++ "\n"}


def Config.inDirectory (cfg : Config) : Config :=
  { cfg with
    currentPrefix := s!"{cfg.preDir} {cfg.currentPrefix}"
  }

def List.forA' [Applicative F] : List α -> (α -> F Unit) -> F Unit
  | [], _ => pure ()
  | x :: xs, f =>
    f x *> forA' xs f

open Config IO in
partial def dirTree (path : System.FilePath) (maxdepth := 3) (res : Ref Res) : ConfigIO Unit := do
  match <- toEntry path, maxdepth with
  | none, _ => pure ()
  | some (.file name), _ => gotFile res; showFileName name res
  | some (.dir name), _ =>
    let {color,..} <- read
    gotDir res
    if (<-FS.realPath path) == (<-IO.currentDir) then
      boldYellow name color |> showDirName (res := res)
    else showDirName name res
    let contents <- path.readDir
    if maxdepth == 0 then pure () else
      let maxdp := maxdepth - 1
      locally inDirectory for i in contents do
        dirTree i.path maxdp res

abbrev help :=
  #[ ("--ascii"         , "Output w/ ASCII characters")
   , ("--hidden, -a"    , "Show hidden files/directories")
   , ("--depth[N=3], -d", "Recurse Depth for traversing dirs")
   , ("--plain, -p"     , "Disable colored output")
   , ("--help, -h"      , "Show help info")]

abbrev printHelp :=
  println! "USAGE: doug [-nc|a|d|p|h] [dirs] -- Display a tree-like view of your dirs" *>
  println! "PARAMS:" *>
  PrettyPrint.printMsg help
