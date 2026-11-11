---- MODULE StrRank ----
\* TLC orders strings by when it first creates them, and it creates the name zeta (an identifier)
\* before the string literals: {"alpha", "zeta"} is enumerated zeta first, so the violation comes
\* with the first successor
VARIABLE x
zeta == "unused"
Init == x = "start"
Next == x' \in {"alpha", "zeta"}
Inv == x # "zeta"
====
