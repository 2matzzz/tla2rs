---- MODULE Junction ----
EXTENDS Naturals
VARIABLE x, y, z
TypeOK == /\ x \in 0..4
          /\ y \in 0..4
          /\ z \in BOOLEAN
Init == /\ x = 0
        /\ y \in 0..1
        /\ z = FALSE
A == /\ \/ /\ x < 4
           /\ x' = x + 1
        \/ /\ x = 4
           /\ x' = 0
     /\ IF y < 2
           THEN /\ y' = y + 1
                /\ z' = z
           ELSE \/ y' = 0 /\ z' = ~z
                \/ /\ y' = y
                   /\ z' = TRUE
B == /\ z
     /\ CASE x = 0 -> x' = 2
          [] x = 1 \/ x = 2 -> x' = x - 1
          [] OTHER -> x' = x
     /\ UNCHANGED <<y, z>>
C == LET d == x + y
         e(k) == k % 3
     IN /\ e(d) = 1
        /\ x' = e(d + 1)
        /\ y' = e(d) + 1
        /\ z' = z
Next == A \/ B \/ C
Inv == /\ x + y <= 8
       /\ \/ ~z
          \/ y # 4
             \/ x # 4
====
