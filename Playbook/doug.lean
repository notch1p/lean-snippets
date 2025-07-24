import Playbook.ffidecl
structure Config where
  useASCII := false
  currentPrefix := ""
  showHidden := false
  maxdepth := 3
  asyncdepth := 0
  color := true
  synced := false
  output : Option System.FilePath := none
structure Res where
  s : String := ""
  fdCount : Nat × Nat := (0, 0)
deriving Repr

instance : Append Res :=
  ⟨fun ⟨s, d, f⟩ ⟨s', d', f'⟩ => ⟨s ++ s', d + d', f + f'⟩⟩

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

def Array.partitionM [Monad m] (arr : Array α) (f : α -> m Bool) : m $ Array α × Array α :=
  arr.size.foldM (init := (#[], #[])) fun i _ (a₁, a₂) =>
    (cond · (a₁.push arr[i], a₂) (a₁, a₂.push arr[i])) <$> f arr[i]

infixr:50 " <$ " => Functor.mapConst

instance : ToString IO.FS.DirEntry := ⟨(·.fileName)⟩

open Config IO in
partial def dirTree (path : System.FilePath) (maxdepth : Nat) (asyncdepth : Nat) (res : Ref Res) : ConfigIO Unit := do
  match <- toEntry path with
  | none              => pure ()
  | some (.file name) => gotFile res *> showFileName name res
  | some (.dir name)  =>
    gotDir res
    let {color,showHidden,..} <- read
    if (<-FS.realPath path) == (<-IO.currentDir) then
      boldYellow name color |> showDirName (res := res)
    else showDirName name res
    let contents <- path.readDir
    if maxdepth == 0 then pure () else
      if asyncdepth > 0 then
        let (ds, fs) <- contents.partitionM (·.path.isDir)
        locally inDirectory $ fs.forM fun i => dirTree i.path (maxdepth - 1) (asyncdepth - 1) res

        let ds := ds.filter (if !showHidden && ·.fileName.startsWith "." then false else true)
        let ress <- locally inDirectory $ ds |>.mapM fun d => do
          let s <- mkRef (∅ : Res)
          pure (s, asTask $ (dirTree d.path (maxdepth - 1) (asyncdepth - 1) s).run (<- read))

        for (r, t) in ress do
          () <$ (liftM $ t >>= wait)
          let acc <- res.get
          let r <- r.get
          res.set (acc ++ r)
      else
        locally inDirectory for i in contents do
          dirTree i.path (maxdepth - 1) asyncdepth res

abbrev nb := "NB."

abbrev help :=
  #[ ("--ascii"           , "Output using ASCII characters")
   , ("--async <n>"       , "Experimental async subdir traversal mode")
   , (nb                  , "enable async recursion for funcalls not deeper than <n>")
   , (""                  , "a typical value of 1 should be enough")
   , (""                  , "best suitable for deep directory trees")
   , ("--hidden, -a"      , "Show hidden entries")
   , ("--depth <n>, -d"   , "Specify recursion depth <n> for traversing dirs")
   , ("--plain, -p"       , "Disable colored output")
   , ("--out <p>, -o"     , "Output to given file <p> instead of stdout")
   , (nb                  , "Usually used in conjunction with --ascii --plain")
   , ("--"                , "Argument parsing terminator")
   , (nb                  , "anything beyond this point is considered a path.")
   , ("--help, -h"        , "Show this help string")]



open PrettyPrint in
abbrev printHelp := println! "\
USAGE: doug [-nc|a|d|p|h|o] [--] [dirs] -- Display a tree-like view of your dirs
PARAMS:
{formatMsg help}
Notes on async mode:
  by default each dir specified in <dirs> is computed asynchronously.
  there's also a experimental switch to enable this for subdirs.\
"
