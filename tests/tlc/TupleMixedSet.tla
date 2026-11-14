---- MODULE TupleMixedSet ----
\* A set of functions over an integer and a model value, and functions over 1..1 (a tuple)
EXTENDS Naturals, FiniteSets, TLC
CONSTANT m
VARIABLE s
Init == s = {(1 :> 0 @@ m :> 1), (1 :> 1)}
InitTuple == s = {<<1>>, (1 :> 0 @@ m :> 1)}
Next == \E f \in s : s' = s \ {f}
Inv == Cardinality(s) <= 2
====
