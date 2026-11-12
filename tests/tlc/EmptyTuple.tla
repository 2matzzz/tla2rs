---- MODULE EmptyTuple ----
\* A variable that only ever holds the empty tuple, and a set of it
VARIABLE empty, pending, step
Init == empty = << >> /\ pending = {<< >>} /\ step = 0
Next == step = 0 /\ step' = 1 /\ pending' = {} /\ UNCHANGED empty
====
