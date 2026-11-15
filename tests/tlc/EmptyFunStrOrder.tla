---- MODULE EmptyFunStrOrder ----
\* In a spec that builds no empty tuple, a set from the state holding an empty function and a
\* non-empty one prints the empty one first, in states, PrintT and ToString
EXTENDS Naturals, TLC
VARIABLES p, s, n
Init == /\ p = 4 :> 1
        /\ s = {4 :> 1}
        /\ n = 0
Next == /\ n < 2
        /\ n' = n + 1
        /\ p' = IF n = 0 THEN [i \in DOMAIN p \ {4} |-> p[i]] ELSE 4 :> 1
        /\ s' = {p', 4 :> 1}
        /\ PrintT(<<s', ToString(s')>>)
Inv == ToString(s) = IF n = 1 THEN "{<< >>, (4 :> 1)}" ELSE "{(4 :> 1)}"
InvViol == n < 2
====
