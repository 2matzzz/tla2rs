---- MODULE Counter ----
\* A counter module, instantiated by Inst.tla (it has no cfg of its own)
EXTENDS Naturals
CONSTANT Limit
VARIABLE c
ASSUME Limit > 0
LOCAL Inc(v) == v + 1
TypeOK == c \in 0..Limit
Init == c = 0
Next == c < Limit /\ c' = Inc(c)
Total(k) == \E i \in 0..k : c = i
====
