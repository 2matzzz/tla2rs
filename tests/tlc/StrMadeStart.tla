---- MODULE StrMadeStart ----
\* When it starts, TLC evaluates every definition of constant level without arguments, used or
\* not: Words makes "ca" before "cb", so the set exploring builds prints as {"ca", "cb"}
EXTENDS Naturals, FiniteSets, Sequences
VARIABLES x, s
Words == {"c" \o w : w \in {"a", "b"}}
Init == x = "c" /\ s = {}
Next == /\ Cardinality(s) < 2
        /\ x' = x
        /\ s' = IF s = {} THEN {x \o "b"} ELSE s \cup {x \o "a"}
Inv == Cardinality(s) < 2
====
