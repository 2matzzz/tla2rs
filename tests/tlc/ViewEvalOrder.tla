---- MODULE ViewEvalOrder ----
(* The first successor of the initial state violates Inv, and the second has no VIEW value: f[3]
   is outside the domain of f. TLC takes the successors in order and reports Inv. *)
EXTENDS Naturals

VARIABLE x

f == [i \in 0..2 |-> i]

Init == x = 0

Next == \/ x = 0 /\ x' = 2
        \/ x = 0 /\ x' = 3

Inv == x # 2
View == f[x]
====
