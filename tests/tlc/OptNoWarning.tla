---- MODULE OptNoWarning ----
\* TLC's -nowarning: TLC's warnings are left out (not those of the parser)
EXTENDS Naturals, TLC
CONSTANT P
VARIABLES f, g
TypeOK == f \in [P -> 0..2] /\ g \in [1..2 -> 0..1]
Init == f = [p \in P |-> 0] /\ g = [i \in 1..2 |-> 0]
Next == \E p \in P : /\ f[p] < 2
                     /\ f' = [f EXCEPT ![p] = f[p] + 1]
                     /\ g' = [g EXCEPT ![3] = 1]
Spec == Init /\ [][Next]_<<f, g>> /\ WF_<<f, g>>(Next)
Done == <>(\A p \in P : f[p] = 2)
Sym == Permutations(P)
====
