---- MODULE InitViol ----
EXTENDS Naturals
VARIABLE x
TypeOK == x \in 0..3
Init == x \in 0..3
Next == x' = x
Inv == x < 2
====
