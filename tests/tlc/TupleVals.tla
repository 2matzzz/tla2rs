---- MODULE TupleVals ----
\* TLC shows both values when a tuple meets an integer: in `=` (worded by the value on the left) and
\* in membership of a product of sets written out (which is also unable to fingerprint)
EXTENDS Naturals
VARIABLES x, t
TypeOK == x \in 0..2 /\ t \in {1, 2} \X {3}
Init == x = 0 /\ t = <<1, 3>>
NextIntLeft ==
        /\ x' = (x + 1) % 3
        /\ UNCHANGED t
        /\ x = 0 \/ x # t
NextTupLeft ==
        /\ x' = (x + 1) % 3
        /\ UNCHANGED t
        /\ x = 0 \/ t # x
NextCross ==
        /\ x' = (x + 1) % 3
        /\ UNCHANGED t
        /\ x = 0 \/ ~(x \in {1, 2} \X {3})
====
