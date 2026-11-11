---- MODULE FunDef ----
\* Function definitions f[x \in S] == e with one and two arguments, the constructor
\* [x \in S, y \in T |-> e], and EXCEPT ![a, b]
EXTENDS Naturals
CONSTANTS Nodes
VARIABLES load, link
First == CHOOSE m \in Nodes : TRUE
Weight[n \in Nodes] == IF n = First THEN 2 ELSE 1
Dist[a \in Nodes, b \in Nodes] == IF a = b THEN 0 ELSE 1
Zero[a, b \in Nodes] == 0
Pick == [a \in Nodes, k \in {1, 2} |-> IF k = 1 THEN a ELSE First]
TypeOK == load \in [Nodes -> 0..4] /\ link \in [Nodes \X Nodes -> 0..1]
Init == load = [n \in Nodes |-> 0] /\ link = Zero
Next == \E a, b \in Nodes :
          \/ /\ load[a] + Weight[a] <= 4
             /\ load' = [load EXCEPT ![a] = @ + Weight[a]]
             /\ UNCHANGED link
          \/ /\ link[a, b] < Dist[a, b]
             /\ link' = [link EXCEPT ![a, b] = 1]
             /\ load' = [n \in Nodes |-> IF n = a THEN 0 ELSE load[n]]
Inv == /\ \A a, b \in Nodes : link[a, b] <= Dist[a, b]
       /\ \A a \in Nodes : Pick[a, 1] = a /\ Pick[a, 2] = First
       /\ LET Sq[i \in 0..4] == i * i IN \A a \in Nodes : Sq[load[a]] <= 16
\* Violated: the counterexample prints a function over pairs
Light == \A n \in Nodes : load[n] < 4 \/ link[n, n] = 1
====
