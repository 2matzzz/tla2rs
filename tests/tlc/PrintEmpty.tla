---- MODULE PrintEmpty ----
EXTENDS Naturals, Sequences, TLC
VARIABLES x
\* TLC prints <<>> for the empty tuple written so and << >> for an empty function
Init == x = 0
Next == /\ x < 1
        /\ PrintT(<<1, <<>>>>)
        /\ PrintT(<<>>)
        /\ PrintT([i \in 1..0 |-> 1])
        /\ PrintT([i \in {} |-> 1])
        /\ PrintT(Tail(<<x>>))
        /\ PrintT(<<<<>>, [i \in {} |-> 1]>>)
        /\ PrintT(LET e == <<>> IN e)
        /\ PrintT({<<>>})
        /\ x' = x + 1
====
