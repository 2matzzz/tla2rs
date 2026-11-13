---- MODULE OptDump ----
\* TLC's -dump: the distinct states, or the state graph with the action of each edge
EXTENDS Naturals
VARIABLES x, y
TypeOK == x \in 0..2 /\ y \in 0..2
Init == x = 0 /\ y \in {0, 1}
IncX == x < 2 /\ x' = x + 1 /\ y' = y
IncY == y < 2 /\ y' = y + 1 /\ x' = x
Reset == x = 2 /\ x' = 0 /\ y' = 0
Next == IncX \/ IncY \/ Reset
Small == x + y < 4
====
