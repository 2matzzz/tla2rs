---- MODULE RecVarKey ----
\* A record updated or read at a key that is not a constant: a key that is a field updates or reads
\* it, a key that is not changes nothing in an EXCEPT (TLC warns), and reading it is an error
EXTENDS Naturals
VARIABLES r, n
Init == r = [a |-> 0, b |-> 1] /\ n = 0
Next == /\ n < 3
        /\ n' = n + 1
        /\ \E k \in {"a", "z"} : r' = [r EXCEPT ![k] = @ + n']
NextRead == /\ n < 4
            /\ \E k \in {"a", "b"} : n' = n + r[k] + 1
            /\ r' = [r EXCEPT !.a = n]
NextMiss == /\ n < 3
            /\ n' = n + 1
            /\ \E k \in {"b", "z"} : r[k] > 0
            /\ UNCHANGED r
Inv == r.a > 0 \/ n < 2
====
