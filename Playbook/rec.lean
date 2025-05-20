noncomputable def half'' (n : Nat) : Nat :=
  Nat.brecOn n (motive := fun _ => Nat)
    fun k soFar =>
      match k, soFar with
      | 0, _ | 1, _ => 0
      | _ + 2, ⟨_, ⟨h, _⟩⟩ => h + 1

#reduce [0,1,2,3,4,5,6,7,8].map half''

def div n k :=
  if k = 0 then panic! "division by zero"
  else if k > n then 0
  else 1 + div (n - k) k

#check List.attach

def thirdChar : Array Char -> Char
  | cv => cv[2]!

example : thirdChar #['!'] = 'A' := rfl

structure Tri (α : Type v) (β : Type w) (γ : Type u) extends Prod α β where
  thd : γ

structure EvenNumber where
  val : Nat
  isEven : 2 ∣ val := by decide

structure EvenPrime extends EvenNumber where
  notOne : val ≠ 1 := by decide
  isPrime : ∀ n, n <= val -> n ∣ val -> n = 1 ∨ n = val


unsafe inductive Bad where
  | bad : (Bad → Bad) → Bad

unsafe def loop (x : Bad) : Bad :=
  match x with
  | .bad f => f x

/-#check
let x := Bad.bad loop
match x with
| .bad f =>
  have : f x = loop (Bad.bad loop) := rfl
  have : f x = x := rfl
  False.elim (f x)
-/
-- theorem bad_false : False :=
--   let x := Bad.bad loop
--   match x with
--   | Bad.bad f =>
--     -- Here x = Bad.bad loop
--     -- So f = loop
--     -- Therefore f x = loop (Bad.bad loop)
--     -- Which matches again, creating an infinite loop
--     have : f x = loop (Bad.bad loop) := rfl
--     have : f x = x := rfl
--     False.elim (f x)

/--
A min-heap.
-/
structure Heap (α) [Ord α] where
  contents : Array α

open Ord in
def Heap.balance [Ord α] (i : Nat) (xs : Heap α) :=
  let ⟨s⟩ := xs
  if _ : i = 0 then xs
  else if _ : i >= s.size then xs
  else
    let j := i / 2
    match compare s[i] s[j] with
    | .lt => balance j ⟨s.swap i j⟩
    | _ => xs

def Heap.insert [Ord α] (x : α) (xs : Heap α) :=
  let i := xs.contents.size
  {xs with contents := xs.contents.push x}.balance i

instance [Ord α] [Repr α] : ToString $ Heap α where
  toString | ⟨s⟩ => reprStr s

#eval
let x : Heap Nat := ⟨#[]⟩
x.insert 5 |>.insert 7 |>.insert 1 |>.insert 10 |>.insert 3
