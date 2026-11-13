---- MODULE PairSource ----
\* A pair of a record or a model value and a record, checked against a set of pairs of records: the
\* pair with the model value is in no such set, as TLC compares a model value with a record
CONSTANT None
VARIABLES ord, src
Ids == {[p |-> 1], [p |-> 2]}
Init == ord = {} /\ src = None
Next == \/ \E a, b \in Ids : a # b /\ ord' = ord \cup {<<a, b>>} /\ UNCHANGED src
        \/ \E s \in Ids \cup {None} : src' = s /\ UNCHANGED ord
Ordered == \A b \in Ids : <<src, b>> \in ord => src # b
====
