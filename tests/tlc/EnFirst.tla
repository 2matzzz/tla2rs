---- MODULE EnFirst ----
\* TLC stops computing ENABLED at the first successor it finds, so an error that only a later
\* successor would raise is not reached
EXTENDS Naturals
VARIABLE x
vars == <<x>>
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\ [][Next]_vars
\* The first disjunct gives a successor, the second fails
Or == \/ x' = x + 1
      \/ x' = 1 \div 0
\* TLC takes the elements in its order (0 first): 0 gives a successor, 2 would fail
In == x' \in {2, 1, 0} /\ 6 \div (2 - x') > 0
\* The first element fails
InBad == x' \in {1, 0} /\ 6 \div x' > 0
\* i = 1 gives a successor, i = 2 would fail
Ex == \E i \in 1..2 : x' = (x + 1) % 3 /\ 6 \div (2 - i) > 0
\* A recursive operator called with an argument from the state: the first disjunct gives a
\* successor, the recursion down to 0 would fail
RECURSIVE Rec(_)
Rec(n) == \/ x' = 6 \div n
          \/ n > 0 /\ Rec(n - 1)
\* A set from the state
St == \E i \in {x, x + 1, 3} : x' = 6 \div (3 - i)
InvOr == ENABLED Or
InvIn == ENABLED In
InvBad == ENABLED InBad
InvEx == ENABLED Ex
InvRec == ENABLED Rec(x + 2)
InvSt == ENABLED St
InitEn == x = 0 /\ ENABLED Or
FairSpec == Spec /\ WF_vars(Ex)
Live == []<>(x = 0)
LiveEn == []<>(ENABLED Ex)
====
