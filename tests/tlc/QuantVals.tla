---- MODULE QuantVals ----
\* Fairness and properties quantified over tuples, sets, functions and records
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_vars /\ \A t \in {<<0, 1>>, <<1, 2>>} : WF_vars(x = t[1] /\ x' = t[2])
STup == \A t \in {<<0, 1>>, <<1, 2>>} : []<>(x = t[2])
SSet == \A s \in {{0, 1}, {2}} : []<>(x \in s)
SFun == \A f \in {[i \in {0, 1} |-> i + 1]} : []<>(x = f[1])
SRec == \E r \in {[a |-> 0], [a |-> 5]} : <>[](x # r.a)
SSetInv == \A s \in {{0, 1, 2}} : [](x \in s)
====
