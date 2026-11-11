---- MODULE RejTempNest ----
\* <>[]<><<A>>_v is not of the forms TLC can check (exit 255)
EXTENDS Naturals
VARIABLE x, y
vars == <<x, y>>
Init == x = 0 /\ y = 0
Inc == x < 2 /\ x' = x + 1 /\ UNCHANGED y
Reset == x = 2 /\ x' = 0 /\ UNCHANGED y
Next == Inc \/ Reset
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
F == <>[]<><<Inc>>_vars
====
