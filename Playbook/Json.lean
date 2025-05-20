import Lean
inductive JSON where
  | TRUE : JSON
  | FALSE : JSON
  | NULL : JSON
  | STRING : String -> JSON
  | NUMBER : Float -> JSON
  | OBJECT : List (String × JSON) -> JSON
  | ARRAY : List JSON -> JSON
deriving Repr

structure Serializer (ContentsT SerializedT : Type) where
  serialize : ContentsT -> SerializedT

def Str : Serializer String JSON := ⟨.STRING⟩

instance : CoeFun (Serializer α JSON) (λ _ => α -> JSON) where
  coe s := s.serialize

def buildRespStr (R : Serializer α JSON) (title : String) (record : α) : JSON :=
  JSON.OBJECT [
    ("title", JSON.STRING title),
    ("status", JSON.NUMBER 256.652),
    ("record", R record), -- CoeFun'd thus R maybe viewed as a function directly.
    ("arr", JSON.ARRAY <| [1,2,3,4].map JSON.NUMBER)
  ]

def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | [] => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))

def printJsonNumber (n : Float) (pad := 0) : String :=
  match n.toString.splitOn "." with
  | []  => ""
  | [x] => x
  | x :: dec :: _ =>
    let decStripped := dec.dropRightWhile (· == '0')
    let declen := decStripped.length
    if declen >= pad then if declen == 0 then s!"{x}" else s!"{x}.{decStripped}"
                     else s!"{x}.{decStripped}{replicate (pad - declen) "0"}"
                     where replicate n s := match n with
                                            | 0 => ""
                                            | 1 => s
                                            | n + 2 =>
                                              s!"{replicate (n + 1) "0"}{s}"

#eval printJsonNumber 123.4567 20

partial def JSON.asString : JSON -> String
  | TRUE => "true"
  | FALSE => "false"
  | NULL => "null"
  | STRING s => "\"" ++ Lean.Json.escape s ++ "\""
  | NUMBER n => printJsonNumber n
  | OBJECT members =>
    let memberToString mem :=
      "\"" ++ Lean.Json.escape mem.fst ++ "\": " ++ asString mem.snd
    "{" ++ ", ".separate (members.map memberToString) ++ "}"
  | ARRAY elements =>
    s!"[{", ".separate $ elements.map asString}]"

#eval buildRespStr Str "FP in LEAN" "PROGRAMMING IS FUN" |>.asString
