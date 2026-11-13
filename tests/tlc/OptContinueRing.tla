---- MODULE OptContinueRing ----
\* TLC's -continue with an action property, a temporal property and a failing invariant
EXTENDS Naturals
VARIABLES x
TypeOK == x \in 0..3
Init == x = 0
Next == x' = (x + 1) % 4
NotTwo == x # 2
Grows == [][x' > x]_x
Reaches == <>(x = 5)
Fails == x # 3 \/ (1 \div 0 = 1)
Spec == Init /\ [][Next]_x /\ WF_x(Next)
====
