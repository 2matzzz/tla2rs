---- MODULE Powered ----
\* Instantiated by InstOps.tla (no cfg of its own): an infix operator constant and an operator constant
EXTENDS Naturals
CONSTANT _ ** _, F(_)
VARIABLE v
Init == v = 1
Next == v < 5 /\ v' = (v ** 2) + F(0)
Big == v > 3
====
