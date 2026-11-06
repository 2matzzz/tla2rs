---- MODULE ParenMap ----
EXTENDS Naturals, FiniteSets
VARIABLE x
TypeOK == x \in 0..3
Init == x = 0
Next == x < 3 /\ x' = x + 1
Inv == x = 0 \/ Cardinality({(y \in {x}) : y \in 0..1}) # 2
====
