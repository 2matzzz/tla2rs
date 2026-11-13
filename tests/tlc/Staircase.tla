---- MODULE Staircase ----
\* Init draws from a constant filter, of more than 65535 records, of a set too large to compute
\* when compiling: a set held as an array of limited capacity cannot hold it
EXTENDS Naturals
Points == [x : 0..1100, y : 0..1100]
VARIABLE p
Init == p \in {q \in Points : q.x + q.y <= 400}
Next == IF p.x > 0 THEN p' = [p EXCEPT !.x = @ - 1] ELSE UNCHANGED p
Below == p.x + p.y <= 400
====
