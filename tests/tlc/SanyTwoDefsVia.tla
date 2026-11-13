---- MODULE SanyTwoDefsVia ----
\* The same through a module that extends both: SANY warns for that module and again for this one
EXTENDS Naturals, SanyTwoDefsMid
VARIABLE x
Init == x = F
Next == x' = G(x)
====
