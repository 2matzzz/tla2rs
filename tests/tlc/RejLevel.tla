---- MODULE RejLevel ----
\* SANY's level rules hold for every definition, used or not (TLC stops with exit 150)
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 4
Unused == Init /\ [][Next]_x /\ x' = 1
====
