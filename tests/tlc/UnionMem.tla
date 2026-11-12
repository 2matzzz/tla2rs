---- MODULE UnionMem ----
\* Membership in UNION of a set of one set that cannot be enumerated (Int inside): TLC tests it in
\* that set without enumerating it
EXTENDS Integers
CONSTANT Gap
VARIABLE f
Init == f = [i \in 0..2 |-> Gap]
Next == \E i \in 0..2 : f[i] = Gap /\ f' = [f EXCEPT ![i] = i - 1]
TypeOK == f \in UNION {[0..2 -> Int \cup {Gap}]}
Narrow == f \in UNION {[0..2 -> Nat \cup {Gap}]}
====
