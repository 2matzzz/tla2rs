---- MODULE TupleFunEq ----
\* A tuple and a function built with :> and @@ over 1..n are one value; over another domain they
\* differ, and TLC checks so with the tuple on either side
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in 1..2
Next == UNCHANGED x
Inv == /\ <<1, 2>> = (1 :> 1 @@ 2 :> 2)
       /\ <<1, x>> = (2 :> x @@ 1 :> 1)
       /\ (1 :> 1 @@ 2 :> x) = <<1, x>>
InvLeft == (1 :> 1 @@ 3 :> x) # <<1, x>>
InvRight == <<1, x>> # (1 :> 1 @@ 3 :> x)
====
