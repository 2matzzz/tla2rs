---- MODULE PrecMod ----
EXTENDS Integers
VARIABLE x, y
TypeOK == x \in -8..8 /\ y \in -8..8
Init == x = 7 /\ y = 0
Next == y = 0 /\ y' = x % 2 * 3 /\ x' = x
Inv == ~(y = 1 /\ (x = 2 \/ x = 7))
====
