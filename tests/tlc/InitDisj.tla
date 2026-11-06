---- MODULE InitDisj ----
EXTENDS Naturals
VARIABLE x, y
TypeOK == x \in 0..3 /\ y \in 0..3
Init == /\ x \in 0..2
        /\ x < 1 \/ x < 2 \/ \E i \in 0..3 : i >= x
        /\ y = 0
Next == UNCHANGED <<x, y>>
Inv == TRUE
====
