import Mathlib

#check (inferInstance : NatCast (Fin 11))
example (a : Fin 11) : (Nat.cast (a.val) : Fin 11) = a := by exact?
