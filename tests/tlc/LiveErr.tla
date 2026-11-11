---- MODULE LiveErr ----
\* Errors in the liveness checks. TLC evaluates the state predicates of a temporal property on each
\* new state, and the fairness of a state after its successors; an error stops it with an
\* unexpected exception, no behavior, and exit 255 whatever the error
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Init == x = 0
InitAll == x \in 0..3
Next == x < 3 /\ x' = x + 1
Stay == x' = x
B == x = 2 /\ (CASE x = 7 -> TRUE) /\ x' = 0
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
SpecB == Init /\ [][Next]_vars /\ WF_vars(Next) /\ WF_vars(B)
SpecInit == InitAll /\ [][Stay]_vars
Reach == <>(x = 2 /\ 1 \div (x - x) = 0)
Done == <>(x = 3)
====
