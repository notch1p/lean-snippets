import Lean
theorem unitNotNat : Unit ≠ Nat := by
  intro eq
  have ⟨allEq⟩ := eq ▸ inferInstanceAs (Subsingleton Unit)
  specialize allEq 0 1
  contradiction

noncomputable abbrev nonParametric (xs : List α) : List α :=
  have := Classical.propDecidable
  if α = Nat then [] else xs

axiom List.free_theorem {α β}
  (f : {α : _} → List α → List α) (g : α → β) :
  f ∘ (List.map g) = (List.map g) ∘ f

abbrev c := List.free_theorem nonParametric (fun () => 1)

example : False := by
  have := c
  unfold nonParametric at this
  simp [unitNotNat] at this
  have := congrFun this [()]
  simp at this

def nextOdd (k : Nat) :
  {n // n % 2 = 1 ∧ (n = k ∨ n = k + 1)} where
  val := if k % 2 == 1 then k else k + 1
  property := by
    simp
    by_cases k % 2 = 1 <;> simp [*] <;> omega


def sumST (xs : List Nat) : Nat :=
  runST $ go xs where
  go (xs) (σ) : ST σ Nat := do
    let n : ST.Ref σ Nat <- ST.mkRef 0
    xs.forM fun x =>
      n.modify (· + x)
    n.get

def foldlST : (α -> β -> α) -> α -> List β -> α
  | f, acc, xs => runST fun σ => do
    let acc' : ST.Ref σ α <- ST.mkRef acc
    xs.forM fun x => do
      let a <- acc'.get
      acc'.set $ f a x
    acc'.get

inductive Error where
  | E1 | E2 deriving Repr

abbrev ES σ := StateRefT Nat $ EST Error σ

def f₁ (x y : Nat) : ES σ Unit := do
  if y = 0 then throw Error.E1
  else modify fun _ => x / y

def f₂ : ES σ Unit := do
  modify fun s => s + 100000

def f₃ : ES σ Nat := do
  f₁ 6 3
  f₂
  let x <- get
  pure x

open IO in
def prog {α : Type} : IO Unit :=
  mkRef none >>= fun (_ : Ref $ Option α) =>
    pure ()

inductive Three where
  | y | n | m

inductive StringList where
  | nilS
  | conS : String -> StringList -> StringList

def StringList.ofList (as : List String) :=
  as.foldl (flip conS) nilS

def StringList.decEq : (as : StringList) -> (bs : StringList) -> Decidable (as = bs)
  | nilS, nilS => isTrue rfl
  | conS a as, conS b bs =>
    if h : a = b then
      match decEq as bs with
      | isTrue h' =>
        isTrue $ h ▸ h' ▸ rfl
      | isFalse h' => isFalse λ | rfl => h' rfl
    else isFalse λ | rfl => h rfl
  | nilS, conS _ _
  | conS _ _, nilS => isFalse nofun

def StringList.beq : StringList -> StringList -> Bool
  | nilS, nilS => true
  | _, nilS
  | nilS, _ => false
  | conS a as, conS b bs => a == b && as.beq bs
instance : DecidableEq StringList := StringList.decEq
instance : BEq StringList := ⟨StringList.beq⟩

open StringList in
example : ofList ["1", "2", "3"] = ofList ["1", "2", "3"] := rfl

namespace StringList
inductive Mem (x : String) : StringList -> Prop where
  | head (xs : StringList) : Mem x $ conS x xs
  | rest (y : String) {ys : StringList} : Mem x ys -> Mem x (conS y ys)
instance : Membership String StringList := ⟨flip Mem⟩
end StringList



instance aNonemptySumInstance (α : Type) {β : Type} [inst : Nonempty α] : Nonempty (α ⊕ β) :=
  let ⟨x⟩ := inst
  ⟨.inl x⟩
set_option pp.explicit true in
#synth Nonempty (Nat ⊕ Empty)

example (h : Nonempty α) : α :=
  h.casesOn (fun val _ => val) (rfl : h = h)

class IsEnum (α : Type) where
  size : Nat
  toIdx : α -> Fin size
  fromIdx : Fin size -> α
  to_from_id : ∀ (i : Fin size), toIdx (fromIdx i) = i
  from_to_id : ∀ (x : α), fromIdx (toIdx x) = x

section
open Lean Elab Parser Term Command

def isEnumHandler (ns : Array Name) : CommandElabM Bool := do
  if h : ns.size = 1 then
    let E <- getEnv
    if let some (.inductInfo ind) := E.find? ns[0] then
      let mut tos : Array (TSyntax ``matchAlt) := #[]
      let mut froms := #[]
      let mut to_froms := #[]
      let mut from_tos := #[]
      let mut i := 0

      for C in ind.ctors do
        let c := mkIdent C
        let n := Syntax.mkNumLit (toString i)

        tos      := tos.push      (<- `(matchAltExpr| | $c => $n))
        from_tos := from_tos.push (<- `(matchAltExpr| | $c => rfl))
        froms    := froms.push    (<- `(matchAltExpr| | $n => $c))
        to_froms := to_froms.push (<- `(matchAltExpr| | $n => rfl))

        i := i + 1
      have : ns.size > 0 := by rw[h]; decide
      let cmd <-
        `( instance : IsEnum $(mkIdent ns[0]) :=
            { size :=    $(quote ind.ctors.length)
            , toIdx      $tos:matchAlt*
            , fromIdx    $froms:matchAlt*
            , to_from_id $to_froms:matchAlt*
            , from_to_id $from_tos:matchAlt* })
      elabCommand cmd
      pure true
    else pure false
  else pure false
initialize
  registerDerivingHandler ``IsEnum isEnumHandler
end
