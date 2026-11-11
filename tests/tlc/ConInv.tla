---- MODULE ConInv ----
\* TLC checks the invariants on states that violate the CONSTRAINT too, initial states included.
\* Such states count as generated but not as distinct, and are not explored
EXTENDS Naturals
VARIABLE x
TypeOK == x \in 0..5
Init == x = 0
InitAll == x \in 0..3
Next == x' = x + 1
NextMod == x' = (x + 1) % 4
\* From 0, x = 9 leaves the type and the CONSTRAINT: TLC reports it as a TypeOK violation
NextJump == x < 2 /\ (x' = x + 1 \/ x' = 9)
Inv == x # 2
InvInit == x # 1
Con == x < 2
ConInit == x # 1
====
