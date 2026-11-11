---- MODULE Literals ----
\* Numbers in base 2, 8 and 16; named ASSUME and THEOREM; the infix operators ??, !! and \bigcirc
EXTENDS Naturals
VARIABLE x
ASSUME Small == \b101 = 5
THEOREM Thm == \o17 = 15
a ?? b == a + b
a !! b == a * b
a \bigcirc b == a - b
Init == x = \hF - 15
Next == x' = (x + \B11) % \O7
Inv == /\ Small /\ Thm
       /\ \hFF = 255 /\ \HaB = 171
       /\ (2 ?? 3) = 5 /\ (2 !! 3) = 6 /\ (5 \bigcirc 3) = 2
Bound == x < 6
====
