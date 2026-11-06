---- MODULE Wide ----
EXTENDS Naturals, FiniteSets
VARIABLE f, s, b
TypeOK == /\ f \in [1..5 -> 0..15]
          /\ s \subseteq 0..100
          /\ b \in BOOLEAN
Init == f = [i \in 1..5 |-> i] /\ s = {0, 63, 64, 100} /\ b = FALSE
Next == \/ \E i \in 1..5 : /\ f[i] < 15
                           /\ f' = [f EXCEPT ![i] = (@ * 3 + 1) % 16]
                           /\ s' = IF (f[i] * 7) \in s THEN s \ {f[i] * 7} ELSE s \cup {f[i] * 6 + 10}
                           /\ b' = ~b
        \/ /\ Cardinality(s) > 6
           /\ s' = {x \in s : x > 50}
           /\ UNCHANGED <<f, b>>
Inv == Cardinality(s) < 40
====
