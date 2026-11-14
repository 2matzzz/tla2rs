---- MODULE RecOptMerge ----
\* @@ on records whose fields differ from value to value: the left record's fields win
EXTENDS Naturals, TLC
VARIABLE r
Init == r \in {[a |-> 1], [a |-> 1, b |-> 2]}
Next == r' = (r @@ [b |-> 0, c |-> 3])
NextRight == r' = ([c |-> 3] @@ r)
\* A field that may be absent on both sides
NextBoth == \E s \in {[a |-> 2], [a |-> 2, b |-> 5]} : r' = (r @@ s)
Inv == r.a = 1
====
