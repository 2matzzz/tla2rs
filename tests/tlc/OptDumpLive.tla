---- MODULE OptDumpLive ----
\* Checking liveness, TLC writes each state to -dump FILE again after its new successors
EXTENDS Naturals
VARIABLE x
Init == x \in {0, 5}
Next == x' = IF x < 3 THEN x + 1 ELSE IF x = 5 THEN 6 ELSE 0
Live == []<>(x = 0)
Ev == <>(x = 0)
Stop == x < 3 /\ x' = x + 1
====
