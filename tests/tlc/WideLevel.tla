---- MODULE WideLevel ----
\* Each level splits into many chunks, and every chunk produces many new states. The table overflows
\* unless its entry count is recomputed per chunk
EXTENDS Naturals
VARIABLES a, b
TypeOK == a \in 0..40000 /\ b \in 0..20
Init == a = 0 /\ b = 0
Next == \/ a = 0 /\ a' \in 1..40000 /\ b' = 0
        \/ a > 0 /\ b = 0 /\ b' \in 1..20 /\ a' = a
====
