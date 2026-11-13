---- MODULE RejSanyRecUndef ----
\* A RECURSIVE declaration needs a definition, and may not reuse the name of a standard operator
EXTENDS Naturals
VARIABLE x
RECURSIVE Nat(_), Count(_)
Init == x = 0
Next == x' = (x + 1) % 3
====
