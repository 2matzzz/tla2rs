---- MODULE RejSanySubLet ----
\* A positional name whose operator is a LET definition that names nothing
EXTENDS Naturals
VARIABLE x
D == LET L(a) == a + 1 IN L(1)!3
Init == x = 0
Next == x' = 0
====
