---- MODULE LiveSymTurn ----
\* A liveness counterexample under a SYMMETRY: the cycle of the folded graph returns to another
\* member of the entry's class, and the actual behavior goes round twice before it repeats a state
EXTENDS Naturals, TLC
CONSTANT P
VARIABLES x, y
vars == <<x, y>>
Init == x = (CHOOSE p \in P : TRUE) /\ y = 0
Next == /\ y' = 1 - y
        /\ x' = IF y = 1 THEN CHOOSE p \in P : p # x ELSE x
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Settles == <>[](y = 0)
Sym == Permutations(P)
====
