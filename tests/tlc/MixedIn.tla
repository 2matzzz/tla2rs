---- MODULE MixedIn ----
\* Testing whether a string is in a set of integers stops TLC with an error
EXTENDS Naturals
VARIABLES x, n
Init == x = "idle" /\ n = 0
Next == /\ n' = (n + 1) % 3
        /\ x' = IF n = 1 THEN 5 ELSE "idle"
        /\ n = 0 \/ x \in {5, 6}
====
