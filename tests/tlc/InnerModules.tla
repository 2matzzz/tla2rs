---- MODULE InnerModules ----
\* Modules written inside the spec, used through named and unnamed INSTANCEs
EXTENDS Integers

---- MODULE Counter ----
EXTENDS Integers
CONSTANT Limit
Step(n) == (n + 1) % Limit
====

---- MODULE Helpers ----
Twice(n) == 2 * n
====

C == INSTANCE Counter WITH Limit <- 4
INSTANCE Helpers
VARIABLE x
Init == x = 0
Next == x' = C!Step(x)
Inv == x \in 0..3 /\ Twice(x) \in 0..6
\* Violated
Low == x < 3
====
