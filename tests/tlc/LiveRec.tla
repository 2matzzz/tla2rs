---- MODULE LiveRec ----
\* Fairness and properties quantified over a set of records
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Rs == {[a |-> 0, b |-> 1], [a |-> 1, b |-> 2], [a |-> 2, b |-> 0]}
Init == x = 0
Move(r) == x = r.a /\ x' = r.b
Next == \E r \in Rs : Move(r)
Spec == Init /\ [][Next]_vars /\ \A r \in Rs : WF_vars(Move(r))
SpecSome == Init /\ [][Next]_vars /\ \A r \in Rs \ {[a |-> 2, b |-> 0]} : WF_vars(Move(r))
Visits == \A r \in Rs : []<>(x = r.b)
Pairs == \E r \in Rs : <>[](x # r.a)
====
