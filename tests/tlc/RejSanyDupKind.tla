---- MODULE RejSanyDupKind ----
\* A CONSTANT and a VARIABLE of one name are refused
EXTENDS Naturals
CONSTANT x
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
====
