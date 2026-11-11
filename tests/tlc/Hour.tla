---- MODULE Hour ----
\* An abstract counter, instantiated by InstRef.tla (no cfg of its own)
EXTENDS Naturals
CONSTANT Max
VARIABLE h
vars == <<h>>
Init == h = 0
Next == h' = (h + 1) % Max
Spec == Init /\ [][Next]_vars
\* A bound variable named like a name of the instantiating module (no capture)
Exists(S) == \E lo \in S : h = lo
====
