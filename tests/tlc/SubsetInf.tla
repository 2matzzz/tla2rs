---- MODULE SubsetInf ----
EXTENDS Integers
VARIABLES f, b
P == {1, 2}
\* A set of records with a field in Int or Nat cannot be enumerated: \subseteq tests each element
TypeOK == f[1] \in Int /\ b \subseteq [c : P, age : Int]
TypeNat == f[1] \in Int /\ b \subseteq [c : P, age : Nat]
Init == f = [p \in P |-> 0] /\ b = {}
Next == f' = [f EXCEPT ![1] = (@ + 1) % 3] /\ b' = {[c |-> 1, age |-> f[1] - 1]}
====
