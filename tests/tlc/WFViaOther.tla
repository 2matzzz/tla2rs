---- MODULE WFViaOther ----
EXTENDS Naturals
VARIABLE x
TypeOK == x \in 0..2
Init == x = 0
A == x' \in (0..2) \ {x}
B == x # 2 /\ x' = 1 - x
Next == (x' = 2 /\ A) \/ B
Spec == Init /\ [][Next]_x /\ WF_x(A)
Prop == <>(x = 2)
====
