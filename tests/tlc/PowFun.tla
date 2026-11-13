---- MODULE PowFun ----
\* An arithmetic error inside a function constructor: TLC computes its values inside the value it
\* keeps for it, and reports that it was unable to fingerprint, exiting with 75
EXTENDS Naturals
VARIABLES x, y
TypeOK == x \in 0..3 /\ y \in [1..2 -> 0..2]
Init == x = 0 /\ y = <<1, 1>>
Next == /\ x < 3
        /\ x' = x + 1
        /\ y' = LET t == [k \in 1..2 |-> (x - 1) ^ 0] IN IF t \in [1..2 -> 0..2] THEN t ELSE y
NextSet == /\ x < 3
           /\ x' = x + 1
           /\ y' = [k \in 1..2 |-> (x - 1) ^ 0]
NextPlain == /\ x < 3
             /\ x' = x + 1
             /\ y' = <<(x - 1) ^ 0, 1>>
====
