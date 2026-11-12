---- MODULE StrIntSet ----
\* A set of strings compared with a set of integers. TLC compares sets of different sizes as
\* unequal; otherwise it compares their elements in order, and a string compared with an integer
\* stops it with an error worded by the value on the left. A model value is unequal to both
EXTENDS Naturals
CONSTANT m
VARIABLE x, n
Ints == {5, 6}
Init == x = "a" /\ n = 0
Next == n < 2 /\ n' = n + 1 /\ x' = IF n = 0 THEN m ELSE "b"
Sizes == /\ {x} # {5, 6}
         /\ ~({x, "c"} = {5})
         /\ ({} = {x}) = FALSE
StrLeft == {x} = {5}
IntLeft == {5} = {x}
Neq == {x, "c"} # Ints
Nested == <<{x}>> = <<{5}>>
Model == n = 1 => ({x} # {5} /\ ~({x} = {5}))
====
