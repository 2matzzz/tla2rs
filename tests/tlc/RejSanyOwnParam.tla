---- MODULE RejSanyOwnParam ----
\* A parameter may not be named like the operator it belongs to
EXTENDS Naturals
VARIABLE x
Id(Id) == Id
Init == x = 0
Next == x' = (x + 1) % 3
====
