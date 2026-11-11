---- MODULE RealSet ----
\* Real of the Reals module is the string "Reals" in TLC: comparing with it works, using it as a
\* set fails when evaluated
EXTENDS Reals
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Inv == x \in Real
InvNot == x \notin Real
InvSub == {x} \subseteq Real
InvLater == x = 0 \/ x \in Real
NextIn == x' = 1 - x /\ x' \in Real
NextE == x' \in Real
Same == Real = "Reals"
====
