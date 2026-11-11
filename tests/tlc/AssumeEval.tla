---- MODULE AssumeEval ----
\* TLC stops before exploring when an ASSUME fails to evaluate, says which one, and exits with 10
EXTENDS Naturals
CONSTANT N
ASSUME N > 0
ASSUME 10 \div (N - 2) > 0
VARIABLE x
Init == x = 0
Next == x' = x
====
