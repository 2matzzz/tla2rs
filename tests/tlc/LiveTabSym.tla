---- MODULE LiveTabSym ----
\* A property TLC checks with its tableau, on the graph folded by SYMMETRY
EXTENDS Naturals, TLC
CONSTANT P
VARIABLE owner, n
Init == owner = "none" /\ n = 0
Take(p) == owner = "none" /\ owner' = p /\ n' = (n + 1) % 3
Give == owner # "none" /\ owner' = "none" /\ UNCHANGED n
Next == (\E p \in P : Take(p)) \/ Give
Spec == Init /\ [][Next]_<<owner, n>> /\ WF_<<owner, n>>(Next)
Sym == Permutations(P)
Gets == \A p \in P : (owner = "none") ~> (owner = p)
====
