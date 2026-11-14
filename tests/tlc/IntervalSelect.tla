---- MODULE IntervalSelect ----
\* SelectSeq of a sequence from the state keeps the form of each element it keeps, and makes <<>>
\* when it keeps none; an IF whose condition prints, inside a tuple or record, gives the form of
\* the branch taken. The invariant compares ToString with the text TLC makes
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLES q, r, c, d, n
Small(s) == Cardinality(s) < 3
Init == /\ q = <<1..2, {3, 4, 5}, 6..7>>
        /\ r = <<>>
        /\ c = <<{}, 0>>
        /\ d = [a |-> {}, b |-> 0]
        /\ n = 0
Next == /\ n < 3 /\ n' = n + 1
        /\ r' = SelectSeq(q, LAMBDA s : n = 2 \/ Small(s))
        /\ q' = IF n = 1 THEN SelectSeq(q, LAMBDA s : FALSE) ELSE q
        /\ c' = <<IF PrintT(<<"c", n>>) /\ n % 2 = 0 THEN 1..2 ELSE {1, 2}, n>>
        /\ d' = [a |-> IF PrintT(<<"d", n>>) /\ n # 1 THEN 3..4 ELSE {3, 4}, b |-> n]
        /\ PrintT(<<n, q, r, c, d>>)
Inv == /\ \A i \in DOMAIN r : ToString(r[i]) \in {"1..2", "6..7", "{3, 4, 5}"}
       /\ ToString(c[1]) \in {"{}", "1..2", "{1, 2}"}
====
