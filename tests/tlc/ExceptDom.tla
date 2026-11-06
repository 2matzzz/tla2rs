---- MODULE ExceptDom ----
EXTENDS Naturals
VARIABLE f, i
TypeOK == f \in [1..2 -> 0..1] /\ i \in 1..3
Init == f = [k \in 1..2 |-> 0] /\ i = 1
Next == i < 3 /\ i' = i + 1 /\ f' = [f EXCEPT ![i'] = 1]
Inv == TRUE
====
