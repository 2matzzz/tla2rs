---- MODULE MixedErr ----
\* Comparing a string with an integer stops TLC with an error
EXTENDS Naturals
VARIABLES x
Init == x = "idle"
Next == x' = IF x = "idle" THEN 1 ELSE "idle"
====
