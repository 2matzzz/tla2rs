---- MODULE LevelPosOr ----
\* SANY gives the position of the temporal formula it refuses: the innermost operator whose
\* arguments break the rules, with infix junctions read as binary and to the left
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_x
F == \/ Init
     \/ [](x < 3)
     \/ x' = 1
====
