---- MODULE RejSanyDupDef ----
\* A definition may not be repeated
EXTENDS Naturals
VARIABLE x
Limit == 1
Limit == 2
Init == x = 0
Next == x' = (x + 1) % 3
====
