---- MODULE EvalInit ----
\* An evaluation error while computing the initial states. TLC checks each initial state as soon as
\* it is generated, so with Inv the violation at x = 1 comes first; otherwise it shows the counts so
\* far (no behavior) and exits with 75
EXTENDS Naturals
VARIABLE x
Init == x \in 0..3 /\ (x = 2 => 1 \div (x - x) = 0)
Next == x' = x
Inv == x # 1
====
