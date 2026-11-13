---- MODULE OptDumpInit ----
\* TLC writes nothing to its -dump file when it stops in the initial states
EXTENDS Naturals
VARIABLE x
Init == x \in 0..2
Next == x' = (x + 1) % 3
Pos == x > 0
====
