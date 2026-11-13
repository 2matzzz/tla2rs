---- MODULE TypeOrder ----
\* A state outside the types TypeOK declares, when TypeOK is an invariant: TLC checks the
\* invariants in the order the cfg lists them, so the first one it violates is reported, and an
\* initial state is reported as one
EXTENDS Naturals
VARIABLE x
TypeOK == x \in 0..2
InitBad == x = 3
InitOk == x = 1
Next == x' = x + 1
Inv == x # 3
====
