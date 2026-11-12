---- MODULE StrMadeToString ----
\* ToString makes "3", then "2", then "1" while n counts down, but TLC created "1" when it parsed
\* the number 1 in its TLC module, so the set prints as {"3", "1", "2"}
EXTENDS Naturals, FiniteSets, TLC
VARIABLES n, s
Init == n = 3 /\ s = {}
Next == /\ n > 0
        /\ n' = n - 1
        /\ s' = s \cup {ToString(n)}
TypeOK == n \in 0..3
Inv == Cardinality(s) < 3
====
