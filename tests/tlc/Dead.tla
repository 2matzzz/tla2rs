---- MODULE Dead ----
EXTENDS Naturals
VARIABLE x, y
TypeOK == x \in 0..5 /\ y \in 0..5
Init == x \in 0..1 /\ y = 0
Next == \/ x < 3 /\ x' = x + 1 /\ y' = y
        \/ y < 2 /\ y' = y + 1 /\ x' = x
====
