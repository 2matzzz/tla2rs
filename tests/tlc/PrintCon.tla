---- MODULE PrintCon ----
\* TLC evaluates the CONSTRAINT, then the ACTION_CONSTRAINT (when the CONSTRAINT holds), on each
\* successor as soon as an action yields it, so what they print comes after what the action printed
\* before that successor and before what the invariants print on it (also on a successor outside
\* the constraints), also in the search for liveness; rebuilding a behavior does not evaluate them
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0, 1} /\ PrintT(<<"init", x>>)
A == PrintT(<<"A", x>>) /\ x' = x + 1 /\ PrintT(<<"A2", x>>)
B == \E d \in {2, 3} : PrintT(<<"B", x, d>>) /\ x' = x + d
Next == A \/ B
Spec == Init /\ [][Next]_x
Cons == PrintT(<<"cons", x>>) /\ x < 5
ActCons == PrintT(<<"act", x, x'>>) /\ x' # 3 /\ x' < 6
Inv == PrintT(<<"inv", x>>) /\ x # 4
Live == <>(x = 100)
====
