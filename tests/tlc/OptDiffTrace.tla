---- MODULE OptDiffTrace ----
\* TLC's -difftrace: each state of a behavior shows only the variables that changed
EXTENDS Naturals
VARIABLES a, b, c
TypeOK == a \in 0..3 /\ b \in 0..3 /\ c \in BOOLEAN
Init == a = 0 /\ b = 0 /\ c = FALSE
IncA == a < 3 /\ a' = a + 1 /\ UNCHANGED <<b, c>>
IncB == b < 3 /\ b' = b + 1 /\ c' = ~c /\ UNCHANGED a
Next == IncA \/ IncB
Small == a + b < 5
Spec == Init /\ [][Next]_<<a, b, c>> /\ WF_<<a, b, c>>(Next)
Never == <>(a = 3 /\ b = 3 /\ ~c)
====
