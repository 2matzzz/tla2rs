---- MODULE ExceptSetKey ----
\* EXCEPT on a function over sets, with a set the domain does not hold whose elements are outside
\* those of the domain's sets: the function stays as it is, and TLC warns
EXTENDS Naturals
VARIABLES f, k
Init == f = [s \in {{1}, {2}} |-> 0] /\ k \in {{1}, {3}, {1, 3}}
Next == f[{1}] < 2 /\ f' = [f EXCEPT ![k] = @ + 1] /\ UNCHANGED k
NextConst == f' = [f EXCEPT ![{3}] = 1, ![{2}] = 2] /\ UNCHANGED k
\* The type the checker holds f in, from the type invariant, has no room for the key
TypeOK == f \in [{{1}, {2}} -> 0..2] /\ k \in SUBSET {1, 3}
====
