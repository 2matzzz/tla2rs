---- MODULE IntervalMerge ----
\* An interval keeps its form in a record merged with @@ from records and functions over field
\* names, and in an IF whose condition prints inside Append and a set
EXTENDS Naturals, Sequences, TLC
VARIABLES r, g, q, s, n
Init == /\ r = [a |-> 1..2] @@ [b |-> {3}]
        /\ g = ("a" :> 1..2) @@ [b |-> 3..4]
        /\ q = <<>>
        /\ s = {}
        /\ n = 0
Next == /\ n < 3 /\ n' = n + 1
        /\ r' = [b |-> 2..n] @@ r
        /\ g' = [g EXCEPT !["a"] = {n}]
        /\ q' = Append(q, IF PrintT(<<"q", n>>) /\ n # 1 THEN 1..n ELSE {1, n})
        /\ s' = s \cup {IF PrintT(<<"s", n>>) /\ n # 2 THEN 0..n ELSE {0, n}}
        /\ PrintT(<<n, r, g, q, s>>)
====
