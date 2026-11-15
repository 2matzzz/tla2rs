---- MODULE ExceptEmptyHeld ----
\* EXCEPT on an argument the empty value does not have, in a spec that builds both the empty
\* tuple and empty functions: TLC warns for both, and the value keeps its form, <<>> for one it
\* holds as a tuple (written so or from the state) and << >> for a function
EXTENDS Naturals, TLC
VARIABLES e, f, n
Init == /\ e = <<>>
        /\ f = [<<>> EXCEPT ![4] = 2]
        /\ n = 0
Next == /\ n < 2
        /\ n' = n + 1
        /\ e' = IF n = 0 THEN e ELSE [i \in {} |-> 1]
        /\ f' = [e' EXCEPT ![4] = 2]
        /\ PrintT(<<f', [[i \in {} |-> 1] EXCEPT ![4] = 2]>>)
Inv == ToString(f) = IF n < 2 THEN "<<>>" ELSE "<< >>"
InvViol == n < 2
====
