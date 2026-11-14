---- MODULE PrintFold ----
\* Parts that tla2rs decides without evaluating them, which TLC evaluates, printing what they
\* print: the elements of a set written out where membership is tested (TLC builds the set first),
\* the tuple or function DOMAIN is taken of, the argument of Head when it starts. And a LET
\* definition it evaluates when it starts is evaluated once each time the LET is
EXTENDS Naturals, Sequences, TLC
VARIABLE x
Once == LET a == PrintT("once") IN a /\ a
First == Head(<<PrintT("head a"), PrintT("head b")>>)
ASSUME \A k \in {1, 2} : LET a == PrintT(<<"assume", k>>) IN a /\ a
Init == x = 0
Next == x < 2 /\ x' = x + 1 /\ DOMAIN [k \in 1..2 |-> PrintT(<<"next", k, x>>)] = 1..2
Member == TRUE \in {PrintT(<<"member a", x>>), PrintT(<<"member b", x>>)}
Picked == 1 \in {IF PrintT(<<"picked a", x>>) THEN 1 ELSE 2, IF PrintT(<<"picked b", x>>) THEN 1 ELSE 3}
Tuple == DOMAIN <<PrintT(<<"tuple", x>>)>> = {1}
====
