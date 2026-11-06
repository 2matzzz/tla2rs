---- MODULE SetOut ----
EXTENDS Naturals
VARIABLE s, n
TypeOK == /\ s \subseteq 1..3
          /\ n \in 0..4
Init == s = {} /\ n = 0
Next == n < 4 /\ n' = n + 1 /\ s' = s \cup {n + 1}
====
