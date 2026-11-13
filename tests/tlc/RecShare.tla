---- MODULE RecShare ----
\* A recursive operator whose result goes to a definition that reads it several times, also per
\* element of a set: written out at each use, each level evaluated the level below several times
EXTENDS Naturals, TLC
Above(t) == CHOOSE k \in {t, t + 1, t + 2} : k > t /\ k < t + 2
RECURSIVE Climb(_)
Climb(n) == IF n = 0 THEN 0 ELSE Above(Climb(n - 1))
ASSUME PrintT(<<"climb", Climb(9)>>)
====
