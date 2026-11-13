---- MODULE Sources ----
\* A record field, only in records of one kind, that holds a record or a model value: checked
\* against a set of records whose field ranges over a set from the state and that model value
EXTENDS Naturals
CONSTANT None
VARIABLES q, n
Srcs == {[p |-> k] : k \in 1..n}
Ops == [op : {"wr"}, val : 1..2] \cup [op : {"rd"}, src : Srcs \cup {None}]
Init == q = [op |-> "rd", src |-> None] /\ n = 1
Next == /\ n' = IF n < 2 THEN n + 1 ELSE n
        /\ \/ q' = [op |-> "wr", val |-> n]
           \/ \E k \in 1..n : q' = [op |-> "rd", src |-> [p |-> k]]
           \/ q' = [op |-> "rd", src |-> None]
Valid == q \in Ops
====
