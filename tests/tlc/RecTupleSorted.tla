---- MODULE RecTupleSorted ----
\* A record tested for membership in a sorted set of tuples (from a definition or the state): TLC
\* compares the record with the element it visits first and stops, as a record meets a non-record
EXTENDS Naturals
VARIABLES n, r, s
Trio == {<<1>>, <<2>>, <<3>>}
Quad == {<<1>>, <<2>>, <<3>>, <<4>>}
Init == n = 0 /\ r = [a |-> 1] /\ s = Trio
Next == n < 2 /\ n' = n + 1 /\ UNCHANGED <<r, s>>
InTrio == n = 1 => [a |-> n] \notin Trio
InQuad == n = 1 => [a |-> n] \notin Quad
InState == n = 1 => r \notin s
====
