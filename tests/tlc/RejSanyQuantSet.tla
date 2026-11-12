---- MODULE RejSanyQuantSet ----
\* The sets of one quantifier are read outside it: a later set cannot use an earlier bound variable
EXTENDS Naturals
VARIABLE x
Pairs == {<<i, j>> : i \in {1, 2}, j \in {i}}
Init == x = 0
Next == x' = (x + 1) % 3
====
