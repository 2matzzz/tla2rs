---- MODULE TupleFunPrint ----
\* What Init prints for the initial states TLC still generates after the error of TupleFunFail
EXTENDS Naturals, TLC
CONSTANT m
VARIABLE x
Init == x \in 1..3 /\ PrintT(<<"init", x>>)
Next == x < 3 /\ x' = x + 1
Inv == PrintT(<<"inv", x>>) /\ <<1, x>> # (1 :> 1 @@ m :> x)
====
