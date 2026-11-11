---- MODULE PropInv ----
\* PROPERTY []P with P a state predicate is checked as an invariant while exploring (TLC names a
\* part of a larger property by its position in the source), and a state predicate on its own only
\* on the initial states ("Property ... is violated by the initial state", exit 13)
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Init == x = 0
InitAll == x \in 0..2
Next == x < 3 /\ x' = x + 1
Stay == x' = x
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Small == [](x < 2)
SmallAndBack == [](x < 2) /\ <>(x = 0)
SmallEval == [](x = 2 => 1 \div (x - x) = 0)
IsZero == x = 0
IsOne == x = 1
====
