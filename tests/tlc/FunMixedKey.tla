---- MODULE FunMixedKey ----
\* A function over an integer and a model value, joined with @@ from a tuple
EXTENDS Naturals, TLC
CONSTANT m
VARIABLE f
Init == f = <<0>>
Next == f' = ((m :> 1) @@ f)
NextRight == f' = [(f @@ (m :> 1)) EXCEPT ![1] = 2]
====
