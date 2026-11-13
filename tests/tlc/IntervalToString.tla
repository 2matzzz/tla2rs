---- MODULE IntervalToString ----
\* ToString of a set TLC holds as an interval makes `a..b`, also inside a record and for DOMAIN of a
\* tuple or sequence, and `{}` when empty; `s \cup {3}` enumerates. An invariant comparing that text
\* holds in TLC, so a checker that made `{1, 2}` would report a violation TLC does not
EXTENDS Naturals, Sequences, TLC
CONSTANT N
VARIABLES s, r, q, n, u
Ivl == 1..N
ASSUME ToString(1..N) = "1..2" /\ ToString(DOMAIN <<5, 6>>) = "1..2"
Init == /\ s = 1..2 /\ r = [a |-> 2..3, b |-> 0] /\ q = <<5, 6>> /\ n = 0 /\ u = Ivl
Next == \/ /\ n < 3 /\ n' = n + 1
           /\ s' = IF n = 1 THEN s \cup {3} ELSE s
           /\ r' = [r EXCEPT !.b = 1 - r.b]
           /\ q' = Append(q, n)
           /\ u' = u
           /\ PrintT(<<n, ToString(s), ToString(r), ToString(DOMAIN q), ToString(DOMAIN <<n, n>>), ToString(u), ToString(n..1)>>)
        \/ n = 3 /\ UNCHANGED <<s, r, q, n, u>>
Inv == /\ ToString(s) = IF n < 2 THEN "1..2" ELSE "{1, 2, 3}"
       /\ ToString(r) = "[a |-> 2..3, b |-> " \o ToString(n % 2) \o "]"
       /\ ToString(DOMAIN q) = <<"1..2", "1..3", "1..4", "1..5">>[n + 1]
       /\ ToString(u) = "1..2"
====
