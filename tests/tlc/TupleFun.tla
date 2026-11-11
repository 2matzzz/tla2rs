---- MODULE TupleFun ----
\* A tuple is the function over 1..n of its elements: tuples in sets of functions, and
\* functions over 1..n in products of sets
EXTENDS Naturals
VARIABLES t, f
TypeOK == t \in (0..2) \X (0..2) /\ f \in [1..2 -> 0..2]
Init == t = <<0, 0>> /\ f = [i \in 1..2 |-> 0]
Next == \/ \E k \in 1..2 : t' = [t EXCEPT ![k] = (@ + 1) % 3] /\ UNCHANGED f
        \/ f' = [i \in 1..2 |-> t[i]] /\ UNCHANGED t
Inv == /\ t \in [1..2 -> 0..2] /\ t \notin [1..3 -> 0..2] /\ t \notin [{0, 1} -> 0..2]
       /\ f \in (0..2) \X (0..2) /\ f \notin (0..2) \X (0..2) \X (0..2)
       /\ (t \in [1..2 -> {0}]) = (t = <<0, 0>>)
\* Violated
Same == f # t \/ t = <<0, 0>>
====
