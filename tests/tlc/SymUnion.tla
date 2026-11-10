---- MODULE SymUnion ----
EXTENDS TLC
CONSTANTS A, B
VARIABLES x, y

Init == x \in A /\ y \in B
Next == x' \in A /\ y' \in B
Symmetry == Permutations(A) \cup Permutations(B)
====
