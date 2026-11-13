---- MODULE LiveOrder ----
\* After a state's successors TLC computes whether each fair action is enabled before it checks
\* the steps against the properties, and stops at the first error. Two properties are not used:
\* TLC checks the parts of their negation in an order that changes from run to run
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x < 3 /\ x' = x + 1
Stuck == x = 2 /\ (CASE x = 7 -> TRUE) /\ x' = 0
Step == x = 2 /\ 1 \div (x - x) = 0
Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ WF_vars(Stuck)
StepOften == []<><<Step>>_vars
====
