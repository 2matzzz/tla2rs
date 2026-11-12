---- MODULE InstOpArg ----
\* An instantiated module passes one of its own definitions as an operator argument
EXTENDS Naturals
VARIABLE x
---- MODULE Adder ----
CONSTANT K
Twice(Op(_), v) == Op(Op(v))
AddK(v) == v + K
Step(v) == Twice(AddK, v)
====
A == INSTANCE Adder WITH K <- 2
Init == x = 0
Next == x < 10 /\ x' = A!Step(x)
Even == x % 4 = 0
====
