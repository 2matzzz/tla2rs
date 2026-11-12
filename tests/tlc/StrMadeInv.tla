---- MODULE StrMadeInv ----
\* TLC checks the invariant on each successor as soon as it computes it: the invariant makes "cb"
\* on the first successor before the next action makes "ca"
EXTENDS Naturals, FiniteSets, Sequences
VARIABLES x, n, s
Init == x = "c" /\ n = 0 /\ s = {}
Next == \/ n = 0 /\ n' = 1 /\ x' = x /\ s' = s
        \/ n = 0 /\ n' = 2 /\ x' = x /\ s' = {x \o "a"}
        \/ n = 2 /\ n' = 3 /\ x' = x /\ s' = s \cup {x \o "b"}
Inv == /\ n = 1 => x \o "b" # "q"
       /\ Cardinality(s) < 2
====
