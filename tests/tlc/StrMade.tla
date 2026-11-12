---- MODULE StrMade ----
\* Strings made while exploring come in the order TLC first makes them: x \o "b" is made one step
\* before x \o "a", so the set prints as {"cb", "ca"} and CHOOSE picks "cb" (written the other way
\* round, which is the order a compiler meets them in)
EXTENDS Naturals, FiniteSets, Sequences
VARIABLES x, s, c
Init == x = "c" /\ s = {} /\ c = ""
Next == /\ Cardinality(s) < 2
        /\ x' = x
        /\ s' = IF s # {} THEN s \cup {x \o "a"} ELSE {x \o "b"}
        /\ c' = CHOOSE e \in s' : TRUE
Inv == Cardinality(s) < 2
====
