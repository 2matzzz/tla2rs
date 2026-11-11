---- MODULE StrRankStd ----
\* The identifiers of the standard modules come before the string literals of the spec: a and b
\* are names in Naturals, so "a" and "b" come before "zz"
EXTENDS Naturals
VARIABLE x
Init == x = "start"
Next == x' \in {"zz", "b", "a"}
Inv == x # "a"
====
