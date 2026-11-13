---- MODULE InstShadowParam ----
\* InstShadow through an instance with a parameter, named like a parameter of a definition
EXTENDS Integers, TLC
VARIABLE n
I(Base) == INSTANCE InstShadowDefs WITH Offset <- Base
Init == n = 0
Next == n' = (n + 1) % 3 /\ PrintT(<<I(5)!Shift(n), I(n)!Shift(7), I(n)!Double(n)>>)
====
