---- MODULE RejTupleEq ----
\* TLC stops with an error when it compares a tuple with an integer
EXTENDS Naturals
VARIABLE x, t
TypeOK == x \in 0..2 /\ t \in {1, 2} \X {3}
Init == x = 0 /\ t = <<1, 3>>
Next == /\ x' = (x + 1) % 3
        /\ t' = IF x = 1 /\ t[2] # x THEN <<2, 3>> ELSE t
        /\ x < 2 \/ t # x
====
