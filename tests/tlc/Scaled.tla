---- MODULE Scaled ----
\* A module with an operator constant, instantiated by InstOp.tla (no cfg of its own)
EXTENDS Naturals
CONSTANT F(_)
VARIABLE v
Init == v = 0
Next == v < 3 /\ v' = v + 1
Big == F(v) > 4
====
