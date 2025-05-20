structure Animal where
  name : String

instance : ToString Animal := ⟨Animal.name⟩
def Animal.printNames : Animal -> IO Unit
  | self => println! self
def Animal.combine : List Animal -> List Animal -> String
  | l₁, l₂ => l₁ ++ l₂ |>.foldl (·.append ∘ Animal.name) (init := "")
structure Dog extends Animal where
  footNum : Nat

#print Dog

#eval Animal.combine [(Dog.mk ⟨"Dog#1"⟩ 4).toAnimal] [(Dog.mk ⟨"Dog#2"⟩ 4).toAnimal]

#check True.intro
