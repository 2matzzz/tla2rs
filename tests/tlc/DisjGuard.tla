---- MODULE DisjGuard ----
EXTENDS Naturals
VARIABLE x
TypeOK == x \in 0..3
Init == x = 0
Next == /\ x < 3
        /\ x' = x + 1
        /\ \/ x' > 0
           \/ x' > 1
           \/ \E i \in 0..3 : i < x'
Inv == TRUE
====
