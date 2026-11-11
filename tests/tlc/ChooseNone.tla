---- MODULE ChooseNone ----
\* CHOOSE with no element satisfying the predicate stops with an evaluation error
EXTENDS Naturals
VARIABLES S, c
TypeOK == S \subseteq 0..3 /\ c \in 0..3
Init == S = {0} /\ c = 0
Next == /\ S' = S \cup {c + 1}
        /\ c' = CHOOSE x \in S' : x > c /\ x < 3
====
