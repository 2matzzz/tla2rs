---- MODULE BatchViol ----
\* A violation found while expanding a later batch of a level (-batched with -memlimit 0 splits the
\* 20001 states of the second level into several batches). The batch that found it must still be
\* added, or the trace and the distinct count come out wrong
EXTENDS Naturals
VARIABLE x, y
TypeOK == x \in 0..2 /\ y \in 0..20000
Init == x = 0 /\ y = 0
Next == \/ x = 0 /\ x' = 1 /\ y' \in 0..20000
        \/ x = 1 /\ x' = 2 /\ y' = y
Inv == ~(x = 2 /\ y = 15000)
====
