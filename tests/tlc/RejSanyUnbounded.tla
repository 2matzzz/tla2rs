---- MODULE RejSanyUnbounded ----
\* SANY checks the names in \E x : P, \A x : P and CHOOSE x : P without a set as in any other
\* expression, with x bound there
EXTENDS Naturals, Sequences
VARIABLE x
A(p) == p
D1 == \E y : y = Unknown
D2 == CHOOSE y : Len
D3 == \A y, z : y = z /\ A(Len)
D4 == \E y : \E y : y = 1
D5 == \E x : x = 1
Init == x = 0
Next == x' = 0
====
