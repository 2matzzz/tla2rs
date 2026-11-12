---- MODULE StrMadeSub ----
\* x grows from the end of w, and SubSeq of x makes "rs", then "qr", then "pq": TLC orders them so,
\* and CHOOSE picks "rs"
EXTENDS Naturals, Sequences, FiniteSets
VARIABLES x, s
w == "pqrs"
Init == x = "s" /\ s = {}
Next == /\ Len(x) < 4
        /\ x' = SubSeq(w, 4 - Len(x), 4)
        /\ s' = s \cup {SubSeq(x', 1, 2)}
Inv == Cardinality(s) < 3 \/ (CHOOSE e \in s : TRUE) # "rs"
====
