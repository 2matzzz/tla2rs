---- MODULE ActionProp ----
\* A violated [][A]_v. TLC exits with 13 for it, as for any violated property
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
Up == [][x' > x]_x
Live == []<>(x = 0)
====
