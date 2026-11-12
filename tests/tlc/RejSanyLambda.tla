---- MODULE RejSanyLambda ----
\* LAMBDA is only an argument of an operator
EXTENDS Naturals
VARIABLE x
Fn == LAMBDA k : k + 1
Init == x = 0
Next == x' = (x + 1) % 3
====
