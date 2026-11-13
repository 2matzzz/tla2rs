---- MODULE RejSanySubLetSet ----
\* A set {y \in S : P} has one operand to name
EXTENDS Naturals
VARIABLE x
D == LET Q == {y \in {1} : y > 0} IN Q!2
Init == x = 0
Next == x' = 0
====
