import Mathlib
/--
The Category typeclass is defined in Mathlib.CategoryTheory.Category.Basic. It depends on the type of the objects, so for example we might write Category (Type u) if we're talking about a category whose objects are types (in universe u).

- Functors (which are a structure, not a typeclass) are defined in Mathlib.CategoryTheory.Functor.Basic, along with identity functors and functor composition.

- Natural transformations, and their compositions, are defined in Mathlib.CategoryTheory.NatTrans.

- The category of functors and natural transformations between fixed categories C and D is defined in Mathlib.CategoryTheory.Functor.Category.

- Cartesian products of categories, functors, and natural transformations appear in Mathlib.CategoryTheory.Products.Basic.

- The category of types, and the hom pairing functor, are defined in Mathlib.CategoryTheory.Types.

## Notation
### Categories
We use the ⟶ (\hom) arrow to denote sets of morphisms, as in X ⟶ Y. This leaves the actual category implicit; it is inferred from the type of X and Y by typeclass inference.

We use 𝟙 (\b1) to denote identity morphisms, as in 𝟙 X.

We use ≫ (\gg) to denote composition of morphisms, as in f ≫ g, which means "f followed by g". You may prefer write composition in the usual convention, using ⊚ (\oo or \circledcirc), as in f ⊚ g which means "g followed by f". To do so you'll need to add this notation locally, via

local notation f ` ⊚ `:80 g:80 := category.comp g f
### Isomorphisms
We use ≅ for isomorphisms.

### Functors
We use ⥤ (\func) to denote functors, as in C ⥤ D for the type of functors from C to D.

We use F.obj X to denote the action of a functor on an object. We use F.map f to denote the action of a functor on a morphism`.

Functor composition can be written as F ⋙ G.

### Natural transformations
We use τ.app X for the components of a natural transformation.

Otherwise, we mostly use the notation for morphisms in any category:

We use F ⟶ G (\hom or -->) to denote the type of natural transformations, between functors F and G. We use F ≅ G (\iso) to denote the type of natural isomorphisms.

For vertical composition of natural transformations we just use ≫. For horizontal composition, use hcomp.
-/
def help := ()

section «1.1.1»
open Function
variable [Nontrivial X] [Nontrivial Y] [Nontrivial Z]
variable {x : X} {y : Y} {z : Z}
def Monic (f : X -> Y) := ∀ (g h : Z -> X), (f ∘ g = f ∘ h) -> g = h
def Epic  (f : X -> Y) := ∀ (g h : Y -> Z), (g ∘ f = h ∘ f) -> g = h
example {f : X -> Y} : Injective f <-> Monic f (Z := Z) := by
  constructor <;> intro h'
  intros g h h''
  have : ∀z, f (g z) = f (h z) := fun z => by
    calc _ = comp f g z := by rfl
         _ = comp f h z := by rw[h'']
  have : ∀z, g z = h z := fun z => h' $ this z
  apply funext this
  next =>
    intro x y h
    unfold Monic at h'
    let F : ∀ x : X, Z -> X := fun x => fun _ => x
    have H : ∀x z, F x z = x := by simp[F]
    have : ∀ x x' : X, f ∘ (F x) = f ∘ (F x') -> (F x) = (F x') :=
      fun x x' a => h' (F x) (F x') $ a
    have := this x y
    have hx := H x
    have hy := H y
    have := this $ by
      funext z'
      simp; rw[hx z', hy z']
      exact h
    rw[<- hx z, <- hy z]
    rw[this]
open Classical in
example {f : X -> Y} : Surjective f <-> Epic f (Z := Z) := by
  constructor <;> intro h₁ <;> unfold Surjective Epic at *
  case mp =>
    intro g h h₂
    funext y
    have ⟨a, eq⟩ := h₁ y
    have H : ∀ x, comp g f x = comp h f x := λ x => by rw[h₂]
    simp at H
    exact eq ▸ H a
  next =>
    have ⟨z, z', neq⟩ := exists_pair_ne Z
    intro b
    let g := λ (_ : Y) => z
    let h := (if · = b then z' else z)
    by_contra! nh
    have h' : g ∘ f = h ∘ f := by
      funext y
      simp[g, h, nh]
    have := h₁ g h h'
    have : g ≠ h := by
      have : g b ≠ h b := by simpa[g, h]
      exact ne_iff.mpr ⟨b, this⟩
    contradiction
end «1.1.1»

section «1.1»
open CategoryTheory
variable [instC : Category 𝒞] {A B C : 𝒞}

example
  [Group G]
  [Group H]
  (f : G -> H)
  (h₁ : ∀ g₁ g₂, f (g₁ * g₂) = f g₁ * f g₂)
  (h₂ : f 1 = 1) : (∀m₁ m₂ : G, f (m₁ * m₂) = f m₁ * f m₂) ∧ f 1 = 1 :=
    ⟨λ m₁ m₂ => h₁ m₁ m₂, h₂⟩

example {f : A ⟶ B} {g : B ⟶ C} (h : Mono (f ≫ g)) : Mono f where
  right_cancellation := λ g' h' H => by
    have := h.right_cancellation g' h'
    rw[<- instC.assoc, <- instC.assoc, H] at this
    exact this rfl

example {f : A ⟶ B} (sf : SplitEpi f) : Epi f where
  left_cancellation g h H := by
    have := sf.section_ ≫= H
    have eq := sf.id
    repeat rw[<- instC.assoc, eq, instC.id_comp] at this
    assumption

example {f : A ⟶ B} {g : B ⟶ C} [h₁ : IsIso f] [h₂ : IsIso $ f ≫ g] : IsIso g where
  out := by
    have ⟨inv₁, id₁, id₁'⟩ := h₁.out
    have ⟨inv₂, id₂, id₂'⟩ := h₂.out
    use inv₂ ≫ f
    rw[<-instC.assoc] at id₂'
    refine ⟨?_, id₂'⟩
    simp at id₂
    calc
      _ = 𝟙 B ≫ g ≫ inv₂ ≫ f := by simp
      _ = inv₁ ≫ (f ≫ g ≫ inv₂) ≫ f := by rw[<- id₁']; simp
      _ = inv₁ ≫ 𝟙 A ≫ f := by rw[id₂]
      _ = 𝟙 B := by rw[instC.id_comp, <- id₁'];

example {f : A ⟶ B} [h₁ : Mono f] (h₂ : SplitEpi f) : IsIso f where
  out := ⟨h₂.section_, by simp[h₁.right_cancellation (f ≫ h₂.section_) (𝟙 A)], h₂.id⟩

end «1.1»
