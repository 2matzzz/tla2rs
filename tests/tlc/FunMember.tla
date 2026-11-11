---- MODULE FunMember ----
\* Membership in a set of functions [D -> R] for every kind of function value (sequences, records,
\* bags), FALSE for a model value, and TLC's error for a value that is not a function
EXTENDS Integers, Sequences, Bags
CONSTANT None
VARIABLES q, k
TypeOK == q \in Seq(0..1) /\ Len(q) <= 2 /\ k \in 0..2
ASSUME /\ [a |-> 1] \in [{"a"} -> {1}] /\ <<>> \in [{} -> {1}] /\ None \notin [{1} -> {1}]
       /\ (1 :> 2) \in [{1} -> {2}] /\ <<1, 2>> \notin [{1} -> {1, 2}]
Init == q = <<>> /\ k = 0
Next == \/ Len(q) < 2 /\ \E v \in 0..1 : q' = Append(q, v) /\ UNCHANGED k
        \/ k < 2 /\ k' = k + 1 /\ UNCHANGED q
        \/ UNCHANGED <<q, k>>
Inv == /\ (q \in [1..2 -> 0..1]) = (Len(q) = 2)
       /\ q \in [1..Len(q) -> 0..1]
       /\ [id |-> k] \in [{"id"} -> 0..2]
       /\ [id |-> k] \notin [{"id", "x"} -> 0..2]
       /\ (SetToBag({k}) \in [{0} -> {1}]) = (k = 0)
       /\ (<<k, k>> \in [1..2 -> {0}]) = (k = 0)
\* Fails once k is 1: an integer is not a function
NotFun == k = 0 \/ k \notin [{1} -> {1}]
====
