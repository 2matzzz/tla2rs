---- MODULE IntervalShow ----
\* TLC prints a set in the form it holds it: built as an interval, it prints as one (also inside
\* a function or a set, and after UNCHANGED or EXCEPT elsewhere), until an operation enumerates it.
\* tla2rs prints the set it denotes, and the comparison reads an interval so (see CLAUDE.md, "State
\* graphs")
EXTENDS Naturals
VARIABLES s, f, n
Init == s = 1..3 /\ f = [i \in 1..2 |-> 1..i] /\ n = 0
Next == \/ /\ n < 2
           /\ n' = n + 1
           /\ s' = IF n = 0 THEN {1, 2, 3} ELSE s \cup {4}
           /\ f' = [f EXCEPT ![1] = 2..3]
        \/ /\ n = 2
           /\ n' = 0
           /\ s' = 1..3
           /\ f' = [i \in 1..2 |-> {1}]
Small == n < 2
====
