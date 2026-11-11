---- MODULE RejSanyChoose ----
\* A CHOOSE body extends as far as it can, so a second CHOOSE on the same line is inside the first one, and reusing its bound name is refused
EXTENDS Naturals
VARIABLE x, y
Init == x = 0 /\ y = 0
Next == /\ x' = CHOOSE k \in {1} : k = 1 /\ y' = CHOOSE k \in {2} : TRUE
====
