---- MODULE Unbounded ----
\* Quantifiers and CHOOSE without a set. TLC accepts them and stops only when it evaluates one
EXTENDS Naturals
VARIABLE x
UnusedE == \E y : y = x
UnusedA == \A y, z : y = z
UnusedC == CHOOSE y : y = 1
Init == x = 0
InitE == \E y : x = y
InitC == x = UnusedC
Next == x' = (x + 1) % 3
NextE == x' = (x + 1) % 3 /\ (x = 2 => \E y : y = x)
NextA == \E y : x' = y
NextC == x' = (x + 1) % 3 /\ (x = 2 => (CHOOSE y : y = x) = 2)
InvE == x < 2 \/ UnusedE
InvA == x < 1 \/ UnusedA
InvC == x = 0 \/ UnusedC = 0
Live == <>(\E y : y = x)
====
