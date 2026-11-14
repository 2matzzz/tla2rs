---- MODULE TupleFunGet ----
\* The comparison of TupleFunFail in a spec that reads TLCGet, which handles each initial state as
\* Init computes it: TLC still generates the remaining initial states
EXTENDS Naturals, TLC
CONSTANT m
VARIABLE x
Init == x \in 1..3
Next == x < 3 /\ x' = x + 1
Inv == TLCGet("level") = 0 /\ <<1, x>> # (1 :> 1 @@ m :> x)
====
