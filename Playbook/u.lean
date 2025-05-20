inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite -> Finite -> Finite
  | arr : Finite -> Finite -> Finite

abbrev Finite.asType : Finite -> Type
  | .unit => Unit
  | .bool => Bool
  | .pair t1 t2 => asType t1 × asType t2
  | .arr t1 t2 => asType t1 -> asType t2
