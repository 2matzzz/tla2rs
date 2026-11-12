---- MODULE PrintOrder ----
\* The order of what Init, the actions and the invariants print with one worker: TLC checks each
\* state as soon as it computes it and stops at the state that stops the search; to show a
\* behavior it evaluates Init again (all of it) and, for each step, the actions in order up to the
\* one that yields the next state (that action as a whole)
EXTENDS Naturals, TLC
VARIABLE x
Init == x \in {0, 10} /\ PrintT(<<"init", x>>)
Two == \E k \in {x + 1, x + 2} : PrintT(<<"two", x, k>>) /\ x' = k
Jump == PrintT(<<"jump", x>>) /\ x < 20 /\ x' = x + 5
Next == Two \/ Jump
Each == \E d \in {1, 3} : PrintT(<<"each", x, d>>) /\ x < 20 /\ x' = x + d
Stuck == x < 2 /\ PrintT(<<"stuck", x>>) /\ x' = x + 1
Fail == PrintT(<<"fail", x>>) /\ x' = ((x + 1) % 5) + (1 \div (3 - x)) * 0
NotThree == x # 3
NotTwo == x # 2
Watched == PrintT(<<"inv", x>>) /\ x # 7
Unreached == <>(x = 100)
====
