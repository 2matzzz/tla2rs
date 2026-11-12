---- MODULE QueueLeft ----
\* When TLC stops at an error it reports the states left on its queue: those of the level not yet
\* expanded and those queued for the next, without the state that stopped it
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 300 /\ (x' = x + 1 \/ x' = x + 10 \/ x' = x + 100)
NextStuck == x # 2 /\ Next
NextFail == x < 300 /\ (x' = x + 1 \/ x' = 10 \div (x - 2) \/ x' = x + 100)
NotEleven == x # 11
NotTwo == x # 2
NeverEleven == [][x' # 11]_x
Unreached == <>(x = 1000)
====
