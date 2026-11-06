---- MODULE DisjState ----
EXTENDS Naturals
VARIABLE x
TypeOK == x \in 0..3
Init == x = 0
Next == /\ x < 3
        /\ \/ x = 0
           \/ x < 2
           \/ \E i \in 0..3 : i <= x
        /\ x' = x + 1
Inv == TRUE
====
