---- MODULE ExceptRecMiss ----
\* An EXCEPT of a record at a field it does not have, written ["z"] or .z, changes nothing there,
\* and TLC warns; also under other steps, next to updates of fields it has, and on constant values
EXTENDS Naturals, TLC
VARIABLES r, g, q, n
R0 == [a |-> 0, b |-> 1]
G0 == [i \in 1..2 |-> [a |-> 0]]
Q0 == [a |-> [b |-> 0], c |-> 0]
Init == r = R0 /\ g = G0 /\ q = Q0 /\ n = 0
Next == /\ n < 3
        /\ n' = n + 1
        /\ r' = [r EXCEPT !["z"] = 1, !["a"] = @ + 1]
        /\ g' = [g EXCEPT ![1].z = 1, ![2].a = n]
        /\ q' = [q EXCEPT !.a["z"] = 1, !.c = @ + 1]
NextDot == /\ n < 2
           /\ n' = n + 1
           /\ r' = [r EXCEPT !.z = 1, !.b = n]
           /\ g' = [g EXCEPT ![n + 1].z = n]
           /\ q' = [q EXCEPT !.a.z = 1]
InitConst == /\ r = [R0 EXCEPT !["z"] = 1, !.a = 5]
             /\ g = [G0 EXCEPT ![1].z = 1, ![1].a = 2]
             /\ q = [Q0 EXCEPT !.a["z"] = 1, !.a.b = 3]
             /\ n = 0
Inv == r.a < 2
====
