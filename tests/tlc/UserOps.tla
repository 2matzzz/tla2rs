---- MODULE UserOps ----
\* Postfix operators (^+, ^*, ^#) and the infix operators -- and |- defined by the spec
EXTENDS Integers
VARIABLE x
a ^+ == (a + 1) % 4
a ^* == a * a
S ^# == S \cup {0}
a -- b == (a - b) % 4
a |- b == a <= b
Init == x = 0
Next == x' = x ^+
Inv == /\ (x -- 1) \in 0..3 /\ x ^* >= x /\ {x} ^# = {0, x}
       /\ (0 |- x) /\ x ^+ ^+ = (x + 2) % 4
\* Violated
Small == x ^* < 9
====
