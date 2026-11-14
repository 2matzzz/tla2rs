---- MODULE ExceptWarnAt ----
\* EXCEPT applied to @ on an argument the value does not have: TLC's warning names the pair of the
\* EXCEPT @ belongs to
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 2 /\ x' = x + 1
In == [[i \in 1..2 |-> <<x>>] EXCEPT ![1] = [@ EXCEPT ![x + 2] = 0]]
Two == [[i \in 1..2 |-> <<x>>] EXCEPT ![1] = [@ EXCEPT ![x + 2] = 0], ![2] = [@ EXCEPT ![x + 3] = 0]]
Nest == [[i \in 1..2 |-> <<<<x>>>>] EXCEPT ![2] = [@ EXCEPT ![1] = [@ EXCEPT ![x + 4] = 0]]]
Inv == In # <<>> /\ Two # <<>> /\ Nest # <<>>
====
