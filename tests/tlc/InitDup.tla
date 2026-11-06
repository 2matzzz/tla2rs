---- MODULE InitDup ----
EXTENDS Naturals
VARIABLE x, y
TypeOK == x \in 0..3 /\ y \in 0..3
Init == /\ \/ x = 1
           \/ x = 1
           \/ x \in {1, 2}
        /\ y \in {x, 0}
Next == /\ x' \in {x, 3}
        /\ y' = y
Inv == x + y < 6
====
