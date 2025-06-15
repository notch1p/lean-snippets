import Lean
/--
  A LazyList (in which the elements are computed lazily) of type `α`.
  The notation `[|...|]` is used to construct a literal of this type.

  e.g. `[|1,2,3|] = 1 ::' 2 ::' 3 ::' nil`. Note that
  - `[||] = nil` where `nil = (nil : LazyList α)`
  - `[|_,..|] = .. ::' nil` where `nil = (↑nil : Thunk (LazyList α))`

  **Any side effect within the elements is evaluated just once.**
  - Most tailrec variants of the methods (and catamorphisms) on lazy list (whose identifier ends with 'TR') in this module, 
    by their nature, are strict and will always force the whole list. Meaning these functions will diverge on a infinite sequence.
    (exceptions (methods may terminate even when input is infinite) are explicitly told in documentations)
  - Although Lean facilitates automatic typecasting through `Coe` and
    there is a `Coe` instance from `α` to `Thunk α`, for the sake of clarity we still
    explicitly perform casting with `↑` on functions that have laziness.
-/
inductive LazyList (α : Type u)
  | nil
  | cons : α -> Thunk (LazyList α) -> LazyList α

namespace LazyList
attribute [scoped simp, scoped grind] Thunk.get
infixr : 65 " ::' " => LazyList.cons
private def const {α β} (x : α) := fun (_ : β) => x
private def const2 {α β} (_ : α) (y : β) := y
attribute [inline, always_inline] const const2

def singleton (a : α) := a ::' (.pure nil)
def ofList (as : List α) : LazyList α := as.foldr (· ::' ·) nil
def ofListTR (as : List α) : LazyList α := as.reverse.foldl (flip (· ::' ·)) nil

theorem oflist_nil : ofList ([] : List α) = nil := rfl
theorem oflist_cons : ofList (x :: xs) = x ::' ofList xs := rfl
attribute [simp, grind] oflist_nil oflist_cons

def ofArray (as : Array α) : LazyList α :=
  Nat.foldRev as.size (init := nil) fun i h a => as[i] ::' a

/--
  Generate a lazy sequence on `f`. `f` takes a `Fin n` which increase
  at each call to `f`.

  e.g. (taken from Lean manual)
  ```lean4
  def observe (tag : String) (n : Nat) (i : Fin n) : Nat :=
    dbg_trace "{tag}: {i.val}"
    i.val
  def fx := observe "xs" 3

  #eval ofFunction fx ++ ofFunction fx
  ```
  evaluates to
  ```
  (stdout) =>
    xs: 0
    xs: 1
    xs: 2
  (value) => [0, 1, 2, 0, 1, 2]
  ```
  Note that the side effects introduced by `dbg_trace` is only evaluated once.
-/
def ofFunction (f : Fin n -> α) : LazyList α :=
  Fin.foldr n (init := nil) fun i xs =>
    f i ::' xs
instance : EmptyCollection (LazyList α) := ⟨nil⟩
instance : Singleton α $ LazyList α := ⟨singleton⟩
instance : Inhabited (LazyList α) := ⟨∅⟩

/--
  `beq` is override by `beqI` in the runtime.
  O(1) if `xs` is physically equal to `ys`, otherwise
  using default structural equality, O(n).
  Typically useful for some sequences that share a suffix.
-/
private unsafe def beqI [BEq α] (xs ys : LazyList α) : Bool :=
  if ptrEq xs ys then true else
    match xs, ys with
    | nil, nil => true
    | x ::' xs, y ::' ys =>
      (ptrEq x y || x == y) && beqI xs.get ys.get
    | _, _ => false
@[implemented_by beqI, inherit_doc beqI] def beq [BEq α] : LazyList α -> LazyList α -> Bool
  | nil, nil => true
  | nil, _ | _, nil => false
  | x ::' xs, y ::' ys => x == y && beq xs.get ys.get
def decEq [DecidableEq α] : (xs : LazyList α) -> (ys : LazyList α) -> Decidable (xs = ys)
  | nil, nil => isTrue rfl
  | nil, _ ::' _ | _ ::' _, nil => isFalse nofun
  | x ::' xs, y ::' ys =>
    if h : x = y then
      match decEq xs.get ys.get with
      | isTrue h' =>
        isTrue $ (Thunk.ext h') ▸ h ▸ rfl
      | isFalse h' => isFalse λ | rfl => h' rfl
    else isFalse λ | rfl => h rfl
def isEmpty (l : LazyList α) : Bool := if l matches nil then true else false

instance [BEq α] : BEq (LazyList α) := ⟨beq⟩
instance [DecidableEq α] : DecidableEq (LazyList α) := decEq

theorem cons_neq_nil [BEq α] {a : α} {as : LazyList α} : beq (a ::' as) nil = false := by simp[beq]
theorem nil_neq_cons [BEq α] {a : α} {as : LazyList α} : beq nil (a ::' as) = false := by simp[beq]
theorem nil_beq_nil [BEq α] : beq (nil : LazyList α) (nil : LazyList α) = true := @beq.eq_1 α .. ▸ rfl
theorem cons_beq_cons [BEq α] {a b : α} {as bs : LazyList α} :
  beq (a ::' as) (b ::' bs) = if a == b
                              then beq as bs
                              else false := by simp[beq];
attribute [simp, grind] nil_beq_nil cons_beq_cons
attribute [simp] cons_neq_nil nil_neq_cons

def snoc! [Inhabited α] : LazyList α -> α × LazyList α
  | nil => (panic! "out of bounds", nil)
  | x ::' xs => (x, xs.get)
def head : (as : LazyList α) -> as ≠ nil -> α
  | x ::' _, _ => x
def head? : (as : LazyList α) -> Option α
  | nil => none | x ::' _ => some x
def head! [Inhabited α] : (as : LazyList α) -> α
  | nil => panic! "out of bounds" | x ::' _ => x
def headD : (as : LazyList α) -> α -> α
  | nil, d => d
  | x ::' _, _ => x
def tail : (as : LazyList α) -> as ≠ nil -> LazyList α
  | _ ::' xs, _ => xs.get
def tail? : LazyList α -> Option (LazyList α)
  | nil => none | _ ::' xs => some xs.get
def tail! : LazyList α -> LazyList α
  | nil => panic! "out of bounds" | _ ::' xs => xs.get
def tailD : LazyList α -> LazyList α -> LazyList α
  | nil, d => d | _ ::' xs, _ => xs.get
abbrev pop := @snoc!
abbrev push := @cons
attribute [always_inline, inline] pop push

/--
  guarantees laziness
-/
def map (f : α -> β) (l : LazyList α) : LazyList β :=
  match l with
  | nil => nil
  | x ::' xs => f x ::' ↑(map f xs.get)

instance : Functor LazyList where map := map

def foldl (f : α -> β -> α) (init : α) (l : LazyList β): α :=
  match l with
  | nil => init
  | x ::' xs => foldl f (f init x) xs.get
@[simp, grind] theorem foldl_nil : foldl f init nil = init := by simp[foldl]
@[simp, grind] theorem foldl_cons : foldl f init (x ::' xs) = foldl f (f init x) xs.get := by simp[foldl]

/--
  Note that in order to reverse a lazylist,
  the whole sequence must be forced and allocated again.
-/
@[always_inline, inline] def reverse (as : LazyList α) : LazyList α := as.foldl (flip (· ::' ·)) nil
def foldr (f : α -> β -> β) (init : β) (l : LazyList α) : β :=
  match l with
  | nil => init
  | x ::' xs => f x $ foldr f init xs.get
@[simp, grind] theorem foldr_nil : foldr f init nil = init := by simp[foldr]
@[simp, grind] theorem foldr_cons : foldr f init (x ::' xs) = f x (foldr f init xs.get) := by simp[foldr]

@[inline] def mapTR (f : α -> β) (l : LazyList α) : LazyList β :=
  l.foldl (flip $ (· ::' ·) ∘ f) nil |>.reverse
def forM [Monad m] (xs : LazyList α) (f : α -> m PUnit) : m PUnit :=
  match xs with
  | nil => pure ()
  | x ::' xs => f x *> forM xs.get f
/--
  - LAZINESS
  Unlike `map`, `mapM` is strict because to unwrap a monadic value in a monadic context,
  we have to compute it first.
-/
def mapM [Monad m] (xs : LazyList α) (f : α -> m β) : m (LazyList β) :=
  match xs with
  | nil => pure nil
  | x ::' xs => (· ::' ·) <$> f x <*> (mapM xs.get f)
def foldlM [Monad m] (f : α -> β -> m α) (init : α) (l : LazyList β) : m α :=
  match l with
  | nil => pure init
  | x ::' xs => (foldlM f · xs.get) =<< (f init x)
def foldrM [Monad m] (f : α -> β -> m β) (init : β) (l : LazyList α) : m β :=
  match l with
  | nil => pure init
  | x ::' xs => f x =<< foldrM f init xs.get
instance [Monad m] : ForM m (LazyList α) α := ⟨forM⟩
instance [Monad m] : ForIn m (LazyList α) α := ⟨ForM.forIn⟩

@[inline, always_inline] def toList (l : LazyList α) := foldr (· :: ·) [] l

@[simp, grind]theorem tolist_nil : toList (nil : LazyList α) = [] := by
  simp[toList]
@[simp, grind]theorem tolist_cons : toList (x ::' xs) = x :: toList xs.get := by simp[toList]
def toArray (l : LazyList α) := foldl (·.push) #[] l
def toListRev (l : LazyList α) := foldl (flip (· :: ·)) [] l
def toListTR (l : LazyList α) := toArray l |>.toList

def foldrTR (f : α -> β -> β) (init : β) (l : LazyList α) := l.toArray.foldr f init
attribute [always_inline, inline] toArray toListRev foldrTR

/--
  `mapReducel` and `mapReducelD` fuses `map` and `foldl`, i.e.
    `mapReducel mapf foldf l init = map mapf foldf l |>.foldl foldf init` or
    `mapReducel mapf foldf l = map mapf l |>.foldl1 foldf`
  but more efficient than the RHS.
  - `mapReducelD` is a version that directly calls `foldl` therefore requires `init` and retains the type of `foldl`;
  - `mapReducel` requires the type of the element to be inhabited and panics iff `l` is ∅ and `init` is `none`.
  - When possible, prefer `mapReducelD` over `mapReducel`. As for the latter `foldf` might be called with 0 or 2 args,
    this property is simulated using `Option`, which represent a nullable object, but is less efficient than native.
    This is particularly important for the case where `l` is ∅ and `init` is `none`. 
  The catamorphism (and their variants)
  - `mapReducel`
  - `mapReducer`
  can be optimized to run in parallel within successive recursive call 
  and are functionally quivalent 
  iff the element type is a monoid. i.e. has associativity
-/
def mapReducel [Inhabited β] (mapf : α -> β) (foldf : β -> β -> β) (l : LazyList α) (init : Option β := none) : β :=
  let mf m y := some $ match m with | none => mapf y | some x => (flip (flip foldf ∘ mapf)) x y
  l.foldl mf init |>.getD (panic! "list is empty")
@[inherit_doc mapReducel]def mapReducelD (mapf : α -> β) (foldf : γ -> β -> γ) (l : LazyList α) (init : γ) : γ :=
  l.foldl (flip (flip foldf ∘ mapf)) init
/--
  `mapReducer` and `mapReducerD` fuses `map` and `foldr`, i.e.
    `mapReducer mapf foldf l init = map mapf foldf l |>.foldr foldf init` or
    `mapReducer mapf foldf l = map mapf l |>.foldr1 foldf`
  but more efficient than the RHS.
  - `mapReducerD` is a version that directly calls `foldr` therefore requires `init` and retains the type of `foldr`
  - `mapReducer` requires the type of the element to be inhabited and panics iff `l` is ∅ and `init` is `none`.
  - When possible, prefer `mapReducerD` over `mapReducer`. As for the latter `foldf` might be called with 0 or 2 args,
    this property is simulated using `Option`, which represent a nullable object, but is less efficient than native.
    This is particularly important for the case where `l` is ∅ and `init` is `none`. 
  The catamorphism (and their variants)
  - `mapReducel`
  - `mapReducer`
  can be optimized to run in parallel within successive recursive call
  and are functionally equivalent
  iff the element type is a monoid i.e. has associativity.
-/
def mapReducer [Inhabited β] (mapf : α -> β) (foldf : β -> β -> β) (l : LazyList α) (init : Option β := none) : β :=
  let mf x m := some $ match m with | none => mapf x | some y => (foldf ∘ mapf) x y
  l.foldr mf init |>.getD (panic! "list is empty")
@[inherit_doc mapReducer] def mapReducerD (mapf : α -> β) (foldf : β -> γ -> γ) (l : LazyList α) (init : γ) : γ :=
  l.foldr (foldf ∘ mapf) init
attribute [inline] mapReducelD mapReducerD

@[simp] theorem cons_ne_nil {a : α} {as : Thunk $ LazyList α} : a ::' as ≠ nil := nofun

/-- `foldl1 f l _ = mapReducel id f l`, but is defined directly. -/
def foldl1 (f : α -> α -> α) : (l : LazyList α) -> l ≠ nil -> α
  | x ::' xs, h =>
    match h : xs.get with
    | nil => x
    | y ::' ys =>
      foldl1 f (f x y ::' ys) $ by
        simp
termination_by l _ => l
decreasing_by simp[-Thunk.get, h]; omega
/-- `foldl1D` is defined through foldl1. -/
def foldl1D (f : α -> α -> α) (l : LazyList α) : Option α :=
  match h : l with
  | nil => none
  | _ ::' _ => some $ foldl1 f l $ h ▸ cons_ne_nil
/-- `foldl1! f l := foldl1D f l |>.getD ..` -/
def foldl1! [Inhabited α] (f : α -> α -> α) (l : LazyList α) : α := foldl1D f l |>.getD (panic! "list is empty")

/-- `foldr1 f l _ = mapReducer id f l`, but is defined directly. -/
def foldr1 (f : α -> α -> α) : (l : LazyList α) -> l ≠ nil -> α
  | x ::' xs, _ =>
    match h : xs.get with
    | nil => x | y ::' ys => f x $ foldr1 f xs.get $ h ▸ cons_ne_nil
/-- `foldr1D` is defined through foldr1. -/
def foldr1D (f : α -> α -> α) (l : LazyList α) : Option α :=
  match h : l with
  | nil => none
  | _ ::' _ => some $ foldr1 f l $ h ▸ cons_ne_nil
/-- `foldr1! f l := foldr1D f l |>.getD ..` -/
def foldr1! [Inhabited α] (f : α -> α -> α) (l : LazyList α) : α := foldr1D f l |>.getD (panic! "list is empty")
attribute [always_inline, inline] foldl1! foldr1!

private def getLastI : (as : LazyList α) -> as ≠ nil -> α
  | (x ::' xs), _ => xs.get.foldl const2 x
private def getLast?I (as : LazyList α) : Option α :=
  as.foldl (flip $ const2 ∘ some) none
private def getLast!I [Inhabited α] (as : LazyList α) : α := as.foldl1! const2
private def getLastDI (as : LazyList α) (dflt : α) : α := as.foldl const2 dflt
attribute [always_inline, inline] getLastI getLast?I getLast!I getLastDI

/--
  `getLast`, `getLast!`, `getLast?`, `getLastD` are overrided by their
  equivalent implemented using `foldl`.
-/
@[implemented_by getLastI] def getLast : (as : LazyList α) -> as ≠ nil -> α
  | x ::' xs, _ =>
    match _ : xs.get with
    | nil => x
    | (y ::' ys) => getLast (y ::' ys) cons_ne_nil
termination_by as _ => as
decreasing_by next _ _ h' => simp[-Thunk.get, h']; omega
@[implemented_by getLast!I] def getLast! [Inhabited α] : LazyList α -> α
  | nil => panic! "out of bounds"
  | x ::' xs => if xs.get matches nil then x else getLast! xs.get
@[implemented_by getLast?I] def getLast? : LazyList α -> Option α
  | nil => none
  | x ::' xs => if xs.get matches nil then some x else getLast? xs.get
@[implemented_by getLastDI] def getLastD : LazyList α -> α -> α
  | nil, d => d
  | x ::' xs, d => if xs.get matches nil then x else getLastD xs.get d

/--
  Folds the whole list to force its string representation,
  unlike `peek`, which only peeks at the head of a list.
  This function is usually accessed through `ToString`.
-/
def toStr [ToString α] (l : LazyList α) : String :=
  bracketed (go l) where
  bracketed s := s!"[|{s}|]"
  go | nil => "" | xs => xs.mapReducel toString (· ++ ", " ++ ·)
/--
  Peeks at the head of a list, unlike `toStr`,
  which eagerly triggers the forcing of the whole list.
  The rest of the list is represented as `⋯` i.e.
    `repr $ ofList [1,2,3,4] = [|1, ⋯|]`
  This function is usually accessed through `Repr`.
-/
def peek [Repr α] (l : LazyList α) : String :=
  bracketed (go l) where
  bracketed s := s!"[|{s}|]"
  go | nil => "" | x ::' _ => s!"{reprStr x}, ⋯"
instance [ToString α] : ToString $ LazyList α := ⟨toStr⟩
instance [Repr α] : Repr $ LazyList α := ⟨flip $ const (.text ∘ peek)⟩

private def lengthI (xs : LazyList α) : Nat :=
  xs.foldl (flip $ (· + ·) ∘ const 1) 0

/--
  - LAZINESS
  `contains` is strict. `contains x xs` terminates only for 
    - any finite sequence `xs`
    - any infinite `xs` where `x ∈ xs`
-/
def contains [BEq α] (x : α) (xs : LazyList α) : Bool :=
  match xs with
  | nil => false | x' ::' xs =>
    match x == x' with
    | true  => true
    | false => contains x xs.get
@[always_inline, inline] def elem := @contains

/--
  non tailrec version of `length`. easier to reason about. 
  Override in runtime by a tailrec version using `foldl`.
-/
@[implemented_by lengthI] def length : LazyList α -> Nat | nil => 0 | _ ::' xs => length xs.get + 1
 theorem length_cons : (a ::' as).length = length as.get + 1 := length.eq_def .. ▸ rfl
 theorem length_nil  : length (nil : LazyList α) = 0 := length.eq_def .. ▸ rfl
 theorem length_thunk_nil : length (Thunk.pure (nil : LazyList α)).get = 0 := by simp[Thunk.pure, length_nil]
attribute [simp, grind] length_cons length_nil length_thunk_nil

@[simp] theorem fin_length_imp_ne_nil (h : Fin $ length as) : as ≠ nil :=
  λ nh =>
    let ⟨v, nh⟩ := length_nil ▸ nh ▸ h;
    Nat.not_succ_le_zero v nh
@[simp, grind] theorem oflist_length_eq_length : (ofList as).length = as.length := by
  induction as with
  | nil => simp[ofList,length]
  | cons x xs ih => simp[oflist_cons]; apply ih
@[simp, grind] theorem list_of_tolist_of_oflist : (ofList as).toList = as := by
  induction as with
  | nil => simp[toList]
  | cons x xs h => simp[tolist_cons]; apply h

@[simp, grind] theorem length_nil_eq_list_length_nil : length (nil : LazyList α) = ([] : List α).length := by simp
@[simp, grind] theorem length_cons_eq_list_length_cons : length (x ::' (ofList xs)) = (x :: xs).length := by simp

/--
  - LAZINESS
  `get` and its variants are strict. `get xs n _` terminates only for 
    - any finite sequence `xs`
    - any infinite `xs` where `xs[n] ∈ xs`
-/
def get : (as : LazyList α) -> (H : Fin (length as)) -> (_ : as ≠ nil := fin_length_imp_ne_nil H) -> α
  | a ::' _, ⟨0, _⟩, _ => a
  | _ ::' as, ⟨n + 1, h⟩, _ =>
    get as.get ⟨ n, have : n + 1 < length as.get + 1 := length_cons ▸ h
                  ; Nat.succ_lt_succ_iff.mp this⟩
               ( show as.get ≠ (nil : LazyList α) from λ h' =>
                  Nat.not_succ_le_zero _
                  ( Nat.succ_lt_succ_iff.mp
                  $ length_nil
                  ▸ h'
                  ▸ length_cons
                  ▸ h))
def get? : LazyList α -> Nat -> Option α
  | nil, _ => none
  | x ::' _, 0 => some x
  | _ ::' xs, n + 1 => get? xs.get n
def get! [Inhabited α] : LazyList α -> Nat -> α
  | nil, _ => panic! "out of bounds"
  | x ::' _, 0 => x
  | _ ::' xs, n + 1 => get! xs.get n
def getD [Inhabited α] : LazyList α -> Nat -> α -> α
  | nil, _, d => d
  | x ::' _, 0, _ => x
  | _ ::' xs, n + 1, d => getD xs.get n d

instance : GetElem (LazyList α) Nat α fun as i => i < as.length where
  getElem as i h := get as ⟨i, h⟩

instance : GetElem? (LazyList α) Nat α fun as i => i < as.length where
  getElem? := get?
  getElem! := get!

/--
  guarantees laziness.
-/
def set : LazyList α -> Nat -> α -> LazyList α
  | nil, _, _ => nil
  | _ ::' xs, 0, s => s ::' ↑xs
  | x ::' xs, n + 1, s => x ::' ↑(set xs.get n s)

/--
  - `append` is the canonical method for concatenating 2 sequence, guarantees laziness.
  - `appendTR` is the strict, tailrec version of `append`, implemented using `revAppend`
  - `revAppend xs ys = xs.reverse ++ ys`, implemented using `foldl`.
-/
def revAppend {α} xs ys := show LazyList α from foldl (flip (· ::' ·)) ys xs
@[inherit_doc revAppend]def appendTR {α} xs ys := show LazyList α from revAppend (reverse xs) ys
attribute [inline] revAppend appendTR
@[inherit_doc revAppend]def append : LazyList α -> LazyList α -> LazyList α
  | nil, l | l, nil => l
  | x ::' xs, l => x ::' ↑(append xs.get l)
instance : Append (LazyList α) := ⟨append⟩

def concat (xs : LazyList α) (x : α) := xs.foldr (· ::' ·) {x}
@[always_inline, inline] abbrev pushBack := @concat

/--
  - LAZINESS
  insert depends on `contains`. Thus behaves the same if given an infinite sequence.
-/
def insert [BEq α] (a : α) (l : LazyList α) : LazyList α :=
  if l.contains a then l else a ::' l
instance [BEq α] : Insert α (LazyList α) := ⟨insert⟩

/--
  guarantees laziness.
-/
def takeWhile : (α -> Bool) -> LazyList α -> LazyList α
  | _, nil => nil
  | f, x ::' xs =>
    if f x then
      x ::' ↑(takeWhile f xs.get)
    else nil
/--
  Extract the first `n` elements from the sequence. The rest is not forced. guarantees laziness.
  This way it is more efficient but also may change the evalution semantics compared
  to that of a normal strict `List`:

  Suppose the Ω-term
  (which can be introduced in Lean using the unsafe rectype constructor μ)
  ```lean4
    Ω = λ x => x x
  ```
  where `Ω ->* Ω`, and for a polymorphic sequence
  ```lean4
    l := [|⟨"123"⟩, ⟨123⟩, ⟨Ω⟩|] : LazyList Obj
  ```
  which elements are encoded using existentials `Obj`, we have

  - `l.take 2` terminates while
  - `l.take 3` doesn't.
-/
def take (n : Nat) (l : LazyList α) : LazyList α :=
  match l, n with
  | nil, _ | _ ::' _, 0 => nil
  | x ::' xs, n + 1 => x ::' ↑(take n xs.get)
def takeTR (n : Nat) (l : LazyList α) : LazyList α := go #[] n l |> ofArray where
  go acc
  | _, nil | 0, _ => acc
  | n + 1, x ::' xs => go (Array.push acc x) n xs.get

/--
  - LAZINESS
  `dropWhile` is strict. `dropWhile f l` terminates only for
    - any finite sequence l
    - any infinite sequence l where `∃x ∈ l, f x -> false`.
-/
def dropWhile (f : α -> Bool) (l : LazyList α) : LazyList α :=
  match l with
  | nil => nil
  | t@(x ::' xs) =>
    if f x then
      dropWhile f xs.get
    else t
def drop (n : Nat) (l : LazyList α) : LazyList α :=
  match l, n with
  | nil, _ => nil
  | xs, 0 => xs
  | _ ::' xs, n + 1 =>
    drop n xs.get

/--
  - LAZINESS
  `extract l start stop` is strict on `[0, start)`, lazy on `[start, stop]`.
-/
def extract (l : LazyList α) (start : Nat) (stop : Nat := l.length) : LazyList α :=
  match l, start, stop with
  | nil, _, _ | _, _, 0 => nil
  | x ::' xs, 0, n + 1 => x ::' ↑(extract xs.get 0 n)
  | _ ::' xs, n + 1, n' + 1 => extract xs.get n n'
/--
  - LAZINESS
  `filter f l` is lazy after the first `x` where `x ∈ l ∧ f x`. That is,
  it terminates if `∃x ∈ l, f x -> true` otherwise not.
-/
def filter (f : α -> Bool) (l : LazyList α) : LazyList α :=
  match l with
  | nil => nil
  | x ::' xs =>
    if f x then x ::' ↑(filter f xs.get)
    else filter f xs.get
@[inline] def filterTR (f : α -> Bool) (l : LazyList α) : LazyList α := go f #[] l |> ofArray where
  go f acc
  | nil => acc | x ::' xs => go f (if f x then acc.push x else acc) xs.get
/--
  - LAZINESS
  `filterMap f l` is lazy after the first `x` where `x ∈ l ∧ (f x -> some _)`. That is,
  it terminates if `∃x ∈ l, f x -> some _` otherwise not.
-/
def filterMap (f : α -> Option β) (l : LazyList α) : LazyList β :=
  match l with
  | nil => nil
  | x ::' xs =>
    if let (some x) := f x then
      x ::' filterMap f xs.get
    else filterMap f xs.get
@[inline] def filterMapTR (f : α -> Option β) (l : LazyList α) : LazyList β := go #[] l |> ofArray where
  go acc
  | nil => acc | x ::' xs => go (if let (some x) := f x then acc.push x else acc) xs.get
/--
  - LAZINESS
  Like `mapM`, `filterMapM f l` is strict.
-/
def filterMapM [Monad m] (f : α -> m (Option β)) : LazyList α -> m (LazyList β)
  | nil => pure nil
  | x ::' xs =>
    f x >>= fun
            | none => filterMapM f xs.get
            | some x =>
              (x ::' ·) <$> filterMapM f xs.get

/--
  guarantees laziness
-/
def flatten : LazyList (LazyList α) -> LazyList α
  | nil => nil
  | x ::' xs => x ++ flatten xs.get
/--
  guarantees laziness
-/
def flatMap (f : α -> LazyList β) : LazyList α -> LazyList β
  | nil => nil
  | x ::' xs => f x ++ flatMap f xs.get
@[inline] def flatMapTR (f : α -> LazyList β) (l : LazyList α) : LazyList β := l.foldl (· ++ f ·) nil
@[inline] def flattenTR {α} l := show LazyList α from flatMapTR id l
/--
  - LAZINESS
  Like `mapM`, `flatMapM f l` is strict.
-/
def flatMapM [Monad m] (f : α -> m (LazyList β)) : LazyList α -> m (LazyList β)
  | nil => pure nil
  | x ::' xs =>
    (· ++ ·) <$> f x <*> flatMapM f xs.get
  #check List.zipWith
/--
  guarantees laziness
-/
def zipWith (f : α -> β -> γ) : LazyList α -> LazyList β -> LazyList γ
  | nil, _ => nil
  | _, nil => nil
  | x ::' xs, y ::' ys => f x y ::' zipWith f xs.get ys.get
/--
  guarantees laziness.
  `zip xs ys = zipWith (· , ·) xs ys`
-/
@[inline]def zip : LazyList α -> LazyList β -> LazyList (α × β) := zipWith (· , ·)
/--
  Generate a potentially infinite sequence of objects of `(S, 0, 1, +, <)`, guarantees laziness.
  Note that the commutativity of `(· + ·)` isn't enforced.
  Codepaths are duplicated on purpose to avoid extra comparing and destructuring.

  - generates an infinite lazy sequence if
    lower bound not provided (this is the case of `nats` and `ints`).
  - generates an infinite **decreasing** lazy sequence if
    `start > stop` and `step < 0`. (this is the case `ints` if set to countdown)
  (That is, if every instances involved above are implemented in a common-sense way.)

  - This function is usually accessed through the notation `[|start ~~ stop : step|]` and
    used in conjunction with list comprehension:

  ```lean4
  gen 0 |>.filter (· ^ 2 > 4) = [|id <- [|0~~|], (· ^ 2 > 4)|]
                              = [3, ⋯]
                     take 3 _ = [3, 4, 5]
  ∀ x ∈ gen 1, x > 0  = ∅ -- diverge as the whole list is forced.
  ∃ x ∈ gen 1, x > 20 = true
  ```
-/
partial def gen [Add α] [Zero α] [One α] [LT α] [DecidableLT α]
  (start : α) (stop : Option α) (step : α) : LazyList α :=
  if step > 0 then stepPos start stop else stepNeg start stop where

  goInf start := start ::' ↑(goInf (start + step))
  stepPos start stop :=
    let rec go start stop := if stop > start 
                             then start ::' ↑(go (start + step) stop)
                             else nil
    if let some stop := stop then go start stop else goInf start

  stepNeg start stop :=
    let rec go start stop := if stop < start 
                             then start ::' ↑(go (start + step) stop)
                             else nil
    if let some stop := stop then go start stop else goInf start
attribute [inline] gen.stepPos gen.stepNeg gen
def nats (start := 0) (step := 1) := show LazyList Nat from gen start none step
def ints start (step : Int := 1) := show LazyList Int from gen start none step
attribute [always_inline, inline, inherit_doc gen] nats ints

/--
  Generate a sequence of number from `Std.Range`. guarantees termination.
-/
@[always_inline, inline] def fromRange : Std.Range -> LazyList Nat
  | {start, step, stop,..} => gen start stop step

inductive Mem (a : α) : (as : LazyList α) -> Prop where
  | head (xs : LazyList α) : Mem a $ a ::' xs
  | step (x : α) {xs : LazyList α} : Mem a xs -> Mem a (x ::' xs)
instance : Membership α (LazyList α) := ⟨flip Mem⟩

theorem mem_of_elem_eq_true [BEq α] [LawfulBEq α] {a : α} {as : LazyList α} :
  contains a as = true -> a ∈ as := by
    match as with
    | nil => simp [contains]
    | x ::' xs =>
      simp [contains]
      split
      case h_1 _ heq =>
        intros; simp_all[(· == ·)]; rw[<-heq]
        exact Mem.head xs.get
      next _ heq =>
        intro h
        have h := mem_of_elem_eq_true h
        have h' := Mem.step x (xs := xs.get) (a := a)
        exact h' h

theorem elem_eq_true_of_mem [BEq α] [ReflBEq α] {a : α} {as : LazyList α} :
  a ∈ as -> contains a as = true := by
  intro h
  induction h with
  | head _ => simp [contains]
  | step _ _ ih => simp [contains]; split <;> trivial

instance [BEq α] [LawfulBEq α] (a : α) (as : LazyList α) : Decidable (a ∈ as) :=
  decidable_of_decidable_of_iff (Iff.intro mem_of_elem_eq_true elem_eq_true_of_mem)

def isPrefix [BEq α] : LazyList α -> LazyList α -> Bool
  | nil, _ => true
  | _, nil => false
  | x ::' xs, y ::' ys => if x == y then isPrefix xs.get ys.get else false
scoped infixl:50 " <+: " => isPrefix

def isSuffix [BEq α] : LazyList α -> LazyList α -> Bool
  | xs, ys => xs.reverse <+: ys.reverse
scoped infixl:50 " <:+ " => isSuffix

def isSub [BEq α] : LazyList α -> LazyList α -> Bool
  | nil, _ => true
  | _, nil => false
  | t@(x ::' xs), y ::' ys =>
    if x == y then
      isSub xs.get ys.get
    else isSub t ys.get
termination_by _ ys => ys
scoped infixl:50 " <+ " => isSub
def findIdx? [BEq α] (p : α -> Bool) : LazyList α -> Option Nat := go p 0 where
  go p i
  | nil => none
  | x ::' xs => if p x then some i else go p (i + 1) xs.get

/--
  A naive version of finding a pattern in a lazy sequence.
  O(|mn|) for `pat` of length `m` and `ctx` of `n`.
-/
def find? [BEq α] (pat ctx : LazyList α) : Option Nat :=
  let rec go i
    | nil => none
    | t@(_ ::' xs)  =>
      if pat <+: t then some i
      else
        go (i + 1) xs.get
  go 0 ctx
scoped infixl:50 " <:+: " => find?

/--
  Applies a (monadic) function `f` over a lazylist,
  For any element `e` and any subterm `es`,
  if `f e` and `e` as well as `es` and `mapMonoI f es`
  is physically equal (that is, pointer equality),
  then we do not allocate a new list.
-/
private unsafe def mapMonoI [Monad m] (f : α -> m α) (as : LazyList α) : m $ LazyList α := do
  match as with
  | nil => pure nil
  | x ::' xs =>
    let xs' <- mapMonoI f xs.get
    let x' <- f x
    if ptrEq x x' && ptrEq xs xs'
    then pure as
    else pure $ x' ::' xs'
@[implemented_by mapMonoI]
opaque mapMonoM [Monad m] : (α -> m α) -> LazyList α -> m (LazyList α)
def mapMono (f : α -> α) (l : LazyList α) : LazyList α := Id.run $ mapMonoM f l

protected def Subset (xs ys : LazyList α) := ∀ ⦃a : α⦄, a ∈ xs -> a ∈ ys
instance : HasSubset (LazyList α) := ⟨LazyList.Subset⟩

instance decidableExists (P : α -> Prop) [DecidablePred P] :
  (xs : LazyList α) -> Decidable (∃x ∈ xs, P x)
  | nil => isFalse nofun
  | x ::' xs =>
    if h₁ : P x then isTrue ⟨x, Mem.head xs.get, h₁⟩
    else
      match decidableExists P xs.get with
      | isTrue h => isTrue $ by
          rcases h with ⟨w, h, h'⟩
          have := Mem.step x h
          exact ⟨w, this, h'⟩
      | isFalse h => isFalse $ by
          rintro ⟨w, h', h''⟩
          cases h' with
          | head => exact h₁ h''
          | step _ hw => exact h ⟨w, hw, h''⟩

instance decidableForall (P : α -> Prop) [DecidablePred P] :
  (xs : LazyList α) -> Decidable (∀x ∈ xs, P x)
  | nil => isTrue nofun
  | x ::' xs =>
    if h : P x then
      match decidableForall P xs.get with
      | isTrue h' =>
        isTrue $ λ
                 | y, Mem.head _ => h
                 | y, Mem.step _ hstep => h' y hstep
      | isFalse h' =>
        isFalse $ λ nh =>
          h' λ n nh' => nh n (Mem.step x nh')
    else isFalse $ λ nh => h $ nh x $ Mem.head xs.get
instance [DecidableEq α] : DecidableRel (Subset : LazyList α -> LazyList α -> Prop) :=
  fun _ _ => decidableForall _ _

/--
  right folds a lazy sequence using `(· <|> ·)`, throws `failure` for a empty list,
  i.e. `firstM f l = foldr (· <|> ·) failure l`.
  In practice, this means `firstM` tries every actions
  and stop after the first successful action and returns its result.

  e.g.
  ```lean4
  def div10 y := if y == 0 then none else some $ 10 / y
  [|0, 0, 10, 20|].firstM div10 = some 1
  ```
-/
def firstM [Alternative m] (f : α -> m β) : LazyList α -> m β
  | nil => failure
  | x ::' xs => f x <|> firstM f xs.get
@[always_inline, inline, inherit_doc firstM] def asum := @firstM

/--
  The notation `[|...|]` is used to construct a literal of this type.

  e.g. `[|1,2,3|] = 1 ::' 2 ::' 3 ::' nil`. Note that
  - `[||] = nil` where `nil = (nil : LazyList α)`
  - `[|_,..|] = .. ::' nil` where `nil = (↑nil : Thunk (LazyList α))`
-/
syntax (name := «term[|_|]») "[|" withoutPosition(term,*,?) "|]" : term

/--
  The notation for list comprehension.
  `[|f <- l, p|]` = l.map f <| l.filter p`
-/
syntax "[|" term (" ← " <|> " <- ") term (" , " term)? "|]" : term
@[inherit_doc gen] syntax "[|" term " ~~ " (term)? (" : " term)? "|]" : term
recommended_spelling "nil" for "[||]" in [LazyList.nil, «term[|_|]»]
recommended_spelling "singleton" for "[|a|]" in [LazyList.cons, «term[|_|]»]

open Lean in
macro_rules
  | `([| $elems,* |]) =>
    let rec expand (result : TSyntax `term)
      | 0, _ => pure result
      | i + 1, true => expand result i false
      | i + 1, false =>
        (expand · i true) =<< ``(LazyList.cons $(⟨elems.elemsAndSeps.get!Internal i⟩) $result)
    let l := elems.elemsAndSeps.size
    bif l == 0 then
      (expand · l (l &&& 1 == 0)) =<< ``(LazyList.nil)
    else
      (expand · l (l &&& 1 == 0)) =<< ``(Thunk.pure LazyList.nil)

  | `([| $start ~~ $(stop)? $[: $step]? |]) => do
    let stop <- if let .some e := stop then ``(Option.some $e) else ``(Option.none)
    let step <- if let .some e := step then pure e else ``(One.one)
    ``(LazyList.gen $start $stop $step)

  | `([| $f <- $l $[, $p]? |]) =>
    match p with 
    | none => ``(LazyList.map $f $l)
    | some p => ``(LazyList.map $f (LazyList.filter $p $l))
  | `([| $f ← $l $[, $p]? |]) => ``([| $f <- $l $[, $p]? |])

instance : ToStream (LazyList α) (LazyList α) := ⟨id⟩

theorem beq.refl [BEq α] [ReflBEq α] {as : LazyList α} : (as == as) = true := 
  match as with
  | [||] => nil_beq_nil
  | x ::' xs => by simp[BEq.beq, beq, -Thunk.get]; exact beq.refl

instance [BEq α] [ReflBEq α] : ReflBEq (LazyList α) := ⟨beq.refl⟩
theorem beq.eq_of_beq [BEq α] [LawfulBEq α] {as bs : LazyList α} : (as == bs) = true -> as = bs := λ h =>
  match h' : as with
  | nil => by cases bs <;> first | rfl | simp_all[BEq.beq, beq]
  | cons x xs => by
    cases bs with
    | nil => simp_all[BEq.beq, beq]
    | cons x xs => 
      simp_all[BEq.beq, beq]
      exact Thunk.ext $ beq.eq_of_beq h.2
instance [BEq α] [LawfulBEq α] : LawfulBEq (LazyList α) := ⟨beq.eq_of_beq⟩

end LazyList

structure LazyListD (α : Type u) (n : Nat) where
  data : LazyList α
  size_of : data.length = n := by simp
deriving Repr, DecidableEq
attribute [simp] LazyListD.size_of

abbrev LazyList.toLazyListD (xs : LazyList α) : LazyListD α xs.length := ⟨xs, rfl⟩
abbrev LazyList.ofLazyListD (xs : LazyListD α n) : LazyList α := xs.data

namespace LazyListD
open LazyList

@[inline] def get (xs : LazyListD α n) (i : Fin n) : α := xs.data[i]
@[inline] def length {n : Nat} (_ : LazyListD α n) : Nat := n

instance : GetElem (LazyListD α n) Nat α fun _ i => i < n where
  getElem xs i h := get xs ⟨i, h⟩

inductive Mem {α n} (a : α) (as : LazyListD α n) : Prop where
  | mk : a ∈ as.data -> Mem a as
instance : Membership α (LazyListD α n) := ⟨flip Mem⟩

end LazyListD
