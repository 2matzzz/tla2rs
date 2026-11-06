---- MODULE NegDiv ----
EXTENDS Integers
VARIABLE x
TypeOK == x \in -8..8
Init == x = 7
Next == x' = x \div (-2)
Inv == x # -4
====
