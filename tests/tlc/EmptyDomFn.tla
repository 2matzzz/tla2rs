---- MODULE EmptyDomFn ----
\* A function over a set that the constants make empty, assigned in Init and typed by TypeOK as a
\* function over that set: built from the empty set, it is the empty function
EXTENDS Naturals
CONSTANT Ids
VARIABLE f, n
Others == Ids \ {CHOOSE i \in Ids : TRUE}
Init == f = [i \in Others |-> 0] /\ n = 0
Next == n < 2 /\ n' = n + 1 /\ f' = [i \in Others |-> n]
TypeOK == f \in [Others -> 0..2] /\ n \in 0..2
====
