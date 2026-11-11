---- MODULE TempOps ----
\* \EE, \AA and -+-> parse; TLC refuses them in a property, and an unused definition with them is
\* fine. A [] over a definition that is [Next]_v
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 4
AlwaysNext == [][Next]_x
Spec == Init /\ AlwaysNext
SParen == Init /\ ([][Next]_x)
Hidden == \EE y : [](y = x)
Every == \AA y : [](y = x)
While == (x = 0) -+-> [](x \in 0..3)
Inv == x < 3
====
