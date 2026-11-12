---- MODULE RejSanyInfixStd ----
\* SANY refuses an infix operator of a standard module the spec does not extend
EXTENDS FiniteSets
VARIABLE x
Init == x = TRUE
Next == x' = x
Unused == Cardinality({1}) < 2
====
