---- MODULE SanyDupDecl ----
\* A CONSTANT or VARIABLE declared again as the same kind (also one of an extended module) is
\* only a warning for SANY; TLC goes on with one
EXTENDS Naturals, SanyDupDeclBase
CONSTANT N, N
VARIABLE x
VARIABLE y, x
VARIABLE z
Init == x = 0 /\ y = 0 /\ z = 0
Next == x' = (x + 1) % N /\ UNCHANGED <<y, z>>
====
