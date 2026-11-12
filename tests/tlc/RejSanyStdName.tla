---- MODULE RejSanyStdName ----
\* A parameter may not be named like an operator of a standard module the spec extends
EXTENDS Naturals, Sequences
VARIABLE x
Pad(Len) == Len + 1
Init == x = 0
Next == x' = (x + 1) % 3
====
