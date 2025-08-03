namespace ML

section
variable {A B C J : Prop}

def mp : (A -> B) -> A -> B := λ h a => h a
def ax_s : (A -> B -> C) -> (A -> B) -> A -> C := λ hab ha a => hab a (ha a)
def ax_k : A -> B -> A := λ a _ => a

inductive Valid (A : Prop) : Prop
  | fromTrue (h : A) : Valid A
export Valid (fromTrue)
prefix : 90 " □" => Valid

theorem true_imp : A -> □A := fromTrue
theorem valid_imp : □A -> A | ⟨a⟩ => a

theorem sub : B -> (□B -> J) -> J
  | h, h' => h' $ fromTrue h


end

def f (α : Type u) (β : α -> Type v) : (a : α) -> β a -> α × β a
  | a, b => ⟨a, b⟩

def f' {α : Type u} {β : α -> Type v} (a : α) (b : β a) : Σa, β a :=
  ⟨a, b⟩

#reduce f' Nat (nat_lit 2) (β := id) 
#reduce f' (nat_lit 1) (nat_lit 2) (β := Function.const Nat Nat)

#eval
  let x := show Option Nat from some 1
  x.casesOn 
    (motive := fun _ => Nat)
    (none := 0)
    (some := fun x => x )

#eval
  let x := show Option Nat from none
  match x with
  | none => 0
  | some x => x

example (n : Nat) : 0 + n = n := 
  n.recOn (motive := λ x => 0 + x = x)
    (zero := show 0 + 0 = 0 from rfl)
    (succ := fun n ih =>
      show 0 + n.succ = n.succ from
      calc 0 + n.succ
        _ = (0 + n).succ := rfl
        _ = n.succ := by rw[ih])

unsafe inductive Bad where 
  | bad : (Bad -> Bad) -> Bad

unsafe def mkBad : Bad -> Bad
  | k@(.bad k') => k' k

unsafe def ω : Bad := mkBad (.bad mkBad)

unsafe def collapse : Bad -> False
  | .bad k => collapse $ k (.bad k)
unsafe def consBad : False -> Bad := False.elim

noncomputable unsafe example {C} (b : Bad) : C :=
  b.recOn (motive := fun _ => C)
    fun f step => step (.bad f)

unsafe example {C} : C := 
  False.elim $ collapse $ .bad $ consBad ∘ collapse

unsafe inductive Bad' where
  | bad' : (Bad' -> Empty) -> Bad'

unsafe def recBad' : Bad' -> Empty
  | .bad' f => f (.bad' f)

unsafe example {C} : C :=
  let bot : Empty := recBad' (.bad' recBad')
  bot.elim

example [Decidable p] : ¬¬p -> p := Decidable.not_not.mp
example : ¬¬p -> p := Classical.not_not.mp

variable (C : Nat → Type u)

#check (@Nat.below C : Nat → Type u)
#reduce (types := true) @Nat.below C (3 : Nat)

#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)


theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => Nat.sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    f (x - y) (div_lemma h) y + 1
  else
    0


def f₁ (a : Nat) := 2 * (5 + a)
def f₂ (a : Nat) := 2 * 5 + 2 * a
example : f₁ = f₂ := funext fun x => Nat.mul_add 2 5 x

noncomputable def div := WellFounded.fix (measure id).wf div.F

#reduce div 8 2 -- 4

#print Vector.map
inductive ImageOf {α β : Type u} (f : α → β) : β → Type u where
  | imf : (a : α) → ImageOf f (f a)

open ImageOf

def inverse {f : α → β} : (b : β) → ImageOf f b → α
  | .(f a), imf a => a

def inverse' {f : α → β} : (b : β) → ImageOf f b → α
  | _, imf a => a

end ML

def Mod7Rel (x y : Nat) : Prop := x % 7 = y % 7
#check (Quot Mod7Rel)

example {α : Type u} : Nonempty α <-> ∃_ : α, True :=
  ⟨fun ⟨a⟩ => ⟨a, .intro⟩, fun ⟨a, _⟩ => ⟨a⟩⟩


def natEm : Nonempty Nat := .intro 0

open Classical in 
noncomputable 
def indefiniteDescription 
  {α : Sort u} 
  (p : α → Prop)
  (h : ∃ x, p x) 
  : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩

structure Person where 
  age : Nat 
  name : String
def eqPerson : (a : Person) -> (b : Person) -> Prop
  | {name,..}, {name := name',..} =>
    name = name'

def eqv_eqPerson : Equivalence eqPerson where
  refl _ := rfl
  symm := Eq.symm
  trans := Eq.trans

instance : Setoid Person := ⟨eqPerson, eqv_eqPerson⟩
def PPerson := Quotient $ inferInstanceAs $ Setoid Person

def PPerson.mk (age : Nat) (name : String) : PPerson :=
  Quotient.mk' {age, name}

theorem mk_eq_mk (age₁ age₂ : Nat) : (PPerson.mk age₁ name) = (PPerson.mk age₂ name) := by
  apply Quot.sound
  simp[Setoid.r, eqPerson]


