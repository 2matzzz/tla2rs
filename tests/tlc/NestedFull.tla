---- MODULE NestedFull ----
EXTENDS Naturals
VARIABLE m, k
TypeOK == /\ m \in [1..2 -> [1..2 -> 0..3]]
          /\ k \in 0..3
Init == m \in [1..2 -> [1..2 -> 0..1]] /\ k = 0
Next == /\ k < 3
        /\ k' = k + 1
        /\ \E a \in 1..2, b \in 1..2 :
             m' = [m EXCEPT ![a][b] = (@ + 1) % 4, ![b][a] = @ + 0]
Inv == TRUE
====
