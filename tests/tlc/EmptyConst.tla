---- MODULE EmptyConst ----
EXTENDS Naturals
CONSTANT S
VARIABLE x
TypeOK == x \in 0..3
Init == x = 0
Next == /\ x < 3
        /\ \A i \in S : i < x
        /\ x' = x + 1
Inv == \A i \in S : i + x > 100
====
