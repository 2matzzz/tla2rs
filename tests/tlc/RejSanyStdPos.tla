---- MODULE RejSanyStdPos ----
\* A name that clashes with an operator of a standard module: SANY names where the module defines it
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE x
Probe == \E Len \in {1} : \E Cardinality \in {2} : \E Print \in {3} : \E Nat \in {4} : TRUE
a :> b == a
Init == x = 0
Next == x' = (x + 1) % 3
====
