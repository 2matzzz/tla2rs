---- MODULE IdentPos ----
\* TLC gives the position of a variable it fails to evaluate where it is written: as the argument of
\* an operator, inside a LET, under a quantifier
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
Plus(a) == a + 1
NArg == x' = Plus(y') /\ y' = 0
NLet == LET z == y' IN x' = z /\ y' = 0
NBound == \E i \in {1, 2} : x' = y' + i /\ y' = 0
====
