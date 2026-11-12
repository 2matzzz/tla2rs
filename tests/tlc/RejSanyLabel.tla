---- MODULE RejSanyLabel ----
\* A label must list the bound variables introduced between it and the enclosing definition
EXTENDS Naturals
VARIABLE x
Rel == \E i \in {1} : \E j \in {2} : here(i) :: i < j
Init == x = 0
Next == x' = (x + 1) % 3
====
