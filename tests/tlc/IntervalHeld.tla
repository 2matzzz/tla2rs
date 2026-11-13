---- MODULE IntervalHeld ----
\* TLC keeps the form of each value inside a function, sequence or set held in the state: an
\* interval stays one there, through EXCEPT, Append, Tail, SubSeq, \o, \cup, \cap, \ and a filter
\* (a set keeps the first of equal elements, \cup and \cap those on the left), and when taken out
\* again (application, Head, CHOOSE, \E, \in). The invariant compares ToString with the text TLC
\* makes
EXTENDS Naturals, Sequences, TLC
CONSTANTS P
VARIABLES f, g, q, s, t, x, y, z, w, n
Init == /\ f = [i \in 1..2 |-> 1..i]
        /\ g = [p \in P |-> 1..2]
        /\ q = <<1..2>>
        /\ s = {1..2, {3}}
        /\ t = {{1, 2}, 2..3}
        /\ x = {} /\ y = {} /\ z = {}
        /\ w \in s
        /\ n = 0
Next == /\ n < 4 /\ n' = n + 1
        /\ f' = IF n = 0 THEN [f EXCEPT ![2] = {1, 2}] ELSE IF n = 1 THEN [f EXCEPT ![1] = 2..3] ELSE f
        /\ g' = [g EXCEPT ![CHOOSE p \in P : TRUE] = {5}]
        /\ q' = IF n < 2 THEN Append(q, 2..3)
                ELSE IF n = 2 THEN SubSeq(q, 2, 3) \o Tail(q)
                ELSE <<q[1]>> \o [q EXCEPT ![1] = {7}]
        /\ s' = IF n = 0 THEN s \cup {2..3}
                ELSE IF n = 1 THEN {e \in s : 2 \in e}
                ELSE IF n = 2 THEN s \cup {{1, 2}}
                ELSE (s \cap t) \ {{3}}
        /\ t' = IF n = 0 THEN t \cap s ELSE {1..2} \cup t
        /\ x' = f[2]
        /\ y' = CHOOSE e \in s : 1 \in e
        /\ \E e \in s : 3 \notin e /\ z' = e
        /\ w' \in t
        /\ PrintT(<<n, f, g, q, s, t, x, y, z, w, Head(q), {Head(q)}, [p \in P |-> s], <<CHOOSE e \in t : 2 \in e>>>>)
Inv == /\ ToString(x) \in {"{}", "1..2", "{1, 2}"}
       /\ ToString(y) \in {"{}", "1..2", "{1, 2}"}
       /\ ToString(w) \in {"1..2", "2..3", "{1, 2}", "{2, 3}", "{3}"}
====
