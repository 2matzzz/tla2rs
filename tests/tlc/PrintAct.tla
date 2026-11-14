---- MODULE PrintAct ----
\* TLC checks the action properties on the step to each successor after the successor is added
\* (if new) and its invariants are checked, so what they print comes after what the invariants
\* print on the successor and before the next action is evaluated; with -continue, before the
\* violation of an action property is reported
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0, 1} /\ PrintT(<<"init", x>>)
A == x < 5 /\ PrintT(<<"A", x>>) /\ x' = x + 1
B == x < 4 /\ PrintT(<<"B", x>>) /\ x' = x + 2
Next == A \/ B
Spec == Init /\ [][Next]_x
NotTwo == PrintT(<<"inv", x>>) /\ x # 2
Act == [][PrintT(<<"act", x, x'>>) /\ x' # 3]_x
Live == <>(x = 100)
====
