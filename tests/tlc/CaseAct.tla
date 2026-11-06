---- MODULE CaseAct ----
EXTENDS Naturals
VARIABLE x
TypeOK == x \in 0..5
Init == x = 0
Next == CASE x = 0 -> x' = 1
          [] x = 1 -> x' = 2
Inv == TRUE
====
