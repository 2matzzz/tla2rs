---- MODULE FunSetDom ----
\* f \in [D -> R] for a function whose type covers only part of D: (Pa :> 0) @@ (Pb :> z) has the
\* type of Pa and Pb as its domain, and is not a function over the three elements of Procs
EXTENDS Naturals, TLC
CONSTANTS Pa, Pb, Procs
VARIABLE y, z
Init == y = [p \in Procs |-> 0] /\ z = 0
Join == /\ z' = 1 - z
        /\ y' = (LET t == (Pa :> 0) @@ (Pb :> z) IN IF t \in [Procs -> 0..2] THEN t ELSE [y EXCEPT ![Pa] = 2])
Cons == /\ z' = 1 - z
        /\ y' = (LET t == [p \in {Pa, Pb} |-> z] IN IF t \in [Procs -> 0..2] THEN t ELSE [y EXCEPT ![Pa] = 2])
====
