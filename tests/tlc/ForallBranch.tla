---- MODULE ForallBranch ----
\* TLC takes \A apart while a variable is unassigned, and an \E or \/ in it branches: each
\* successor is generated once per branch that holds
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == /\ \A i \in {1, 2} : \E j \in {3, 4} : j > i
        /\ x' = (x + 1) % 3
NextOr == /\ \A i \in {1, 2} : (i > 0 \/ x >= 0)
          /\ x' = (x + 1) % 3
NextLate == /\ x' = (x + 1) % 3
            /\ \A i \in {1, 2} : \E j \in {3, 4} : j > i
====
