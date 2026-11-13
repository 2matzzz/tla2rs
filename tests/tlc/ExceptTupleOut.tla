---- MODULE ExceptTupleOut ----
\* EXCEPT on a tuple at a constant index outside it: TLC warns and leaves the tuple unchanged
EXTENDS Naturals
VARIABLE x
Init == x = <<FALSE, 1>>
Next == x' = [x EXCEPT ![0] = TRUE, ![3] = 2]
====
