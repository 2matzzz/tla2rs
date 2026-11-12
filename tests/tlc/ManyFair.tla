---- MODULE ManyFair ----
\* More than 64 fairness conditions (one per p): the checker holds them in a wider bit mask
EXTENDS Naturals
VARIABLE c
Step(p) == c' = (c + p) % 3
Init == c = 0
Next == \E p \in 1..70 : Step(p)
Spec == Init /\ [][Next]_c /\ \A p \in 1..70 : WF_c(Step(p))
Leaves == []<>(c # 0)
Visits == []<>(c = 2)
====
