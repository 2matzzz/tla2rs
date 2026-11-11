---- MODULE RejSanyShadow ----
\* SANY refuses a bound variable named like a VARIABLE in scope
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Unused == \E x \in {1, 2} : x > 1
====
