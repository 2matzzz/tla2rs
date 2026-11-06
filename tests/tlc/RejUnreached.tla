---- MODULE RejUnreached ----
EXTENDS Naturals
VARIABLE x, y
TypeOK == x \in 0..3 /\ y \in 0..3
Init == x = 0 /\ y = 0
Next == \/ x < 3 /\ x' = x + 1 /\ y' = y
        \/ FALSE /\ x' = 0
Inv == TRUE
====
