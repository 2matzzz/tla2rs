---- MODULE OptView ----
\* TLC's -view: a behavior shows the VIEW of each state instead of the state
EXTENDS Naturals
VARIABLES n, steps
TypeOK == n \in 0..4 /\ steps \in 0..8
Init == n = 0 /\ steps = 0
Next == /\ steps < 8
        /\ \/ n' = (n + 1) % 5
           \/ n' = n
        /\ steps' = steps + 1
Bound == n < 4
V == <<n, n % 2 = 0>>
====
