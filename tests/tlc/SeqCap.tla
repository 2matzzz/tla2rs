---- MODULE SeqCap ----
\* A sequence whose bound the spec does not state: Init and Next settle it
EXTENDS Naturals, Sequences
VARIABLES q, i
Init == q = <<>> /\ i = 1
Next == /\ q' = IF Len(q) < 3 THEN Append(q, i) ELSE Tail(q)
        /\ i' = 3 - i
        \* a tuple indexed by a value from the state
        /\ <<10, 20, 30>>[Len(q') + 0 * i] \in {10, 20, 30} \/ q' = <<>>
Inv == Len(q) <= 3
====
