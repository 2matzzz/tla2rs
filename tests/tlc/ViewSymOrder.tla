---- MODULE ViewSymOrder ----
\* VIEW and SYMMETRY together: TLC takes the smallest of the permuted states, comparing the
\* variables in the order it prints them (flag before count here), and keeps the view of that
\* state. The view leaves flag out, so states with the same counts up to a permutation of the
\* nodes are kept apart when their flags make TLC pick different permutations
EXTENDS Naturals, TLC
CONSTANTS Nodes
VARIABLES count, flag
Init == count = [n \in Nodes |-> 0] /\ flag = [n \in Nodes |-> 0]
Bump(n) == count[n] < 2 /\ count' = [count EXCEPT ![n] = @ + 1] /\ UNCHANGED flag
Mark(n) == flag[n] < 1 /\ flag' = [flag EXCEPT ![n] = 1] /\ UNCHANGED count
Next == \E n \in Nodes : Bump(n) \/ Mark(n)
View == count
Sym == Permutations(Nodes)
====
