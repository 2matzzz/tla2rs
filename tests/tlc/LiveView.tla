---- MODULE LiveView ----
\* A liveness counterexample under a VIEW that leaves out a counter that only grows: the first state
\* reached of a view (x = 2 by Jump) is not the successor of the state before it on the lasso, and
\* the lasso never returns to an actual state it went through, only to one with the same view
EXTENDS Naturals
VARIABLES x, n
vars == <<x, n>>
Init == x = 0 /\ n = 0
Step == x < 3 /\ x' = x + 1 /\ n' = n + 1
Jump == x = 0 /\ x' = 2 /\ n' = n + 10
Reset == x = 3 /\ x' = 0 /\ n' = n + 1
Next == Step \/ Jump \/ Reset
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
NeverOne == <>[](x # 1)
View == x
====
