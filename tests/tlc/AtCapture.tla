---- MODULE AtCapture ----
EXTENDS Naturals
VARIABLE f, g
TypeOK == /\ f \in [1..2 -> 0..3]
          /\ g \in [1..2 -> 0..3]
Id(v) == [g EXCEPT ![1] = v][1]
Init == f = [i \in 1..2 |-> 1] /\ g = [i \in 1..2 |-> 0]
Next == /\ f[1] = 1
        /\ f' = [f EXCEPT ![1] = Id(@) + 1]
        /\ g' = g
Inv == f[1] # 2
====
