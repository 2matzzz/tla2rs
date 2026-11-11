---- MODULE RejTempEquiv ----
\* TLC cannot handle <=> between temporal formulas (exit 255)
EXTENDS Naturals
VARIABLE x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x < 2 /\ x' = x + 1 /\ UNCHANGED y
Reset == x = 2 /\ x' = 0 /\ UNCHANGED y
Next == Inc \/ Reset
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
F == ([]<>(x = 0)) <=> ([]<>(x = 1))
====
