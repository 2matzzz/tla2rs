---- MODULE StrMadeConst ----
\* A constant expression inside an action or invariant makes its string when TLC first evaluates
\* it there: "cb" one step before "ca", whether as a value (Next), as the set a quantifier ranges
\* over (NextBound), or as a set tested for membership on the initial state (InvIn)
EXTENDS Naturals, FiniteSets, Sequences
VARIABLES x, s
Init == x = "c" /\ s = {}
Next == /\ Cardinality(s) < 2
        /\ x' = x
        /\ s' = IF s # {} THEN s \cup {"c" \o "a"} ELSE {"c" \o "b"}
NextBound == /\ Cardinality(s) < 2
             /\ x' = x
             /\ IF s # {} THEN \E e \in {"c" \o "a"} : s' = s \cup {e}
                          ELSE \E e \in {"c" \o "b"} : s' = {e}
NextIn == /\ Cardinality(s) < 2
          /\ x' = x
          /\ s' = IF s = {} THEN {x \o "a"} ELSE s \cup {x \o "b"}
Inv == Cardinality(s) < 2
InvIn == x \notin {"c" \o "b"} /\ Cardinality(s) < 2
====
