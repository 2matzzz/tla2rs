---- MODULE DisjGuard2 ----
EXTENDS Naturals
VARIABLE x, y
TypeOK == x \in 0..3 /\ y \in 0..1
Init == x = 0 /\ y = 0
Next == /\ x < 3
        /\ x' = x + 1
        /\ \/ x' > 0
           \/ x' > 1
        /\ y' = 0
Inv == TRUE
====
