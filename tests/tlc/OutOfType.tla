---- MODULE OutOfType ----
EXTENDS Naturals
VARIABLE x, y
TypeOK == /\ x \in 0..3
          /\ y \in BOOLEAN
Init == x = 0 /\ y \in BOOLEAN
Next == x' = x + 1 /\ y' = ~y
====
