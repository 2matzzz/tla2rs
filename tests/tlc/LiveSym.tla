---- MODULE LiveSym ----
\* Liveness on the graph folded by SYMMETRY (TLC warns that this may miss violations)
EXTENDS Naturals, TLC
CONSTANT P
VARIABLE owner
vars == <<owner>>
Init == owner = "none"
Take(p) == owner = "none" /\ owner' = p
Give == owner # "none" /\ owner' = "none"
Next == (\E p \in P : Take(p)) \/ Give
Spec == Init /\ [][Next]_vars /\ WF_vars(Give)
Sym == Permutations(P)
Live == \A p \in P : []<>(owner = p)
Live2 == []<>(owner = "none")
====
