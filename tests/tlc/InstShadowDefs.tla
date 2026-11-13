---- MODULE InstShadowDefs ----
EXTENDS Integers
CONSTANT Offset
INSTANCE InstShadowBase
Bump(step) == step + 1
Small(S) == {step \in S : step < 2}
Double(k) == LET step == k * 2 IN step
RECURSIVE Sum(_)
Sum(step) == IF step = 0 THEN 0 ELSE step + Sum(step - 1)
Shift(Base) == Base + Offset
step == 100
twice == 7
====
