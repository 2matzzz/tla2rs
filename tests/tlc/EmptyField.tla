---- MODULE EmptyField ----
\* A set that starts empty and later holds records: the field of one of its elements is typed
\* before any element is known
EXTENDS Naturals
VARIABLE seen
Init == seen = {}
Next == seen' = seen \cup (IF \A r \in seen : r.n # 1 THEN {[n |-> 1]} ELSE {[n |-> 2]})
Few == \A r \in seen : r.n < 3
====
