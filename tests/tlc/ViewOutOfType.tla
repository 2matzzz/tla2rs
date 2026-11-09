---- MODULE ViewOutOfType ----
EXTENDS Naturals
VARIABLE x, y
TypeOK == /\ x \in 0..3
          /\ y \in 0..1
Init == x = 0 /\ y = 0
\* Every successor has the same view as the initial state, so it is never new and TLC does not
\* check TypeOK on it, although x' = 5 is out of type
Next == x' = x + 5 /\ y' = y
View == y
====
