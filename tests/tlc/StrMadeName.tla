---- MODULE StrMadeName ----
\* A string made while exploring that is also the name of a definition was created when TLC
\* parsed that name: "zb" comes before "za", made earlier
EXTENDS Naturals, FiniteSets, Sequences
VARIABLES x, s
zb == 0
Init == x = "z" /\ s = {}
Next == /\ Cardinality(s) < 2
        /\ x' = x
        /\ s' = IF s = {} THEN {x \o "a"} ELSE s \cup {x \o "b"}
Inv == Cardinality(s) < 2
====
