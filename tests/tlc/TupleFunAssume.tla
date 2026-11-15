---- MODULE TupleFunAssume ----
\* An ASSUME where a tuple meets functions over keys that are not all integers, in a sorted set
\* (k = 1) and in a set written out (k = 2)
EXTENDS Naturals, TLC
CONSTANTS m, k
VARIABLE x
Deep == {(m :> 1), (2 :> 1), (3 :> 1)}
ASSUME IF k = 1 THEN <<1>> \notin Deep ELSE <<1>> \notin {(m :> 1)}
Init == x = 0
Next == x < 2 /\ x' = x + 1
====
