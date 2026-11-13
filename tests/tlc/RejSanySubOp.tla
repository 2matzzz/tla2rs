---- MODULE RejSanySubOp ----
\* Subexpressions: only of a definition (not of a CONSTANT, VARIABLE, parameter or bound
\* variable), and only with the arguments its operator takes
EXTENDS Naturals
CONSTANT K
VARIABLE x
Op(a) == a + 1 /\ a > 0
Lab(a) == lab :: a + 1
Zero == 1 + 2
D1 == Op!1
D2 == x!1
D3 == K!1
D4 == \E y \in {1} : y!1
D5(p) == p!1
D6 == Lab!lab
D7 == LET L(a) == a + 1 IN L!1
D8 == Op!2!1
D9 == Zero!1
D10 == Op(1)!1
Init == x = 0
Next == x' = 0
====
