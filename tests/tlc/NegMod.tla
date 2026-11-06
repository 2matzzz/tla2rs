---- MODULE NegMod ----
EXTENDS Integers
VARIABLE x
TypeOK == x \in -8..8
Init == x = 7
Next == x' = x % (-3)
Inv == TRUE
====
