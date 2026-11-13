---- MODULE SanyTwoDefs ----
\* Two definitions of one name in two extended modules: SANY warns "in global context" (before
\* the module's own warnings) and goes on; TLC uses the definition of the module extended first
EXTENDS Naturals, SanyTwoDefsA, SanyTwoDefsB
VARIABLE x, x
Init == x = F
Next == x' = G(x)
====
