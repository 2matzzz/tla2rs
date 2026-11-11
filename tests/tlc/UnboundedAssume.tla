---- MODULE UnboundedAssume ----
\* An unbounded quantifier in an ASSUME: evaluating the assumption fails
EXTENDS Naturals
VARIABLE x
ASSUME \A y : y = 1
Init == x = 0
Next == x' = x
====
