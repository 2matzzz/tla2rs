---- MODULE EvalNext ----
\* An evaluation error in Next after an earlier disjunct has produced a successor. TLC checks each
\* successor as soon as it is generated, so that one is counted, and an invariant it violates is
\* reported instead of the error. TLC exits with 255 for \div and 75 for CASE
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == \/ x < 3 /\ x' = x + 1
        \/ x = 2 /\ 1 \div (x - x) = 0 /\ x' = 0
NextCase == \/ x < 3 /\ x' = x + 1
            \/ x = 2 /\ (CASE x = 7 -> TRUE) /\ x' = 0
Inv == x # 3
====
