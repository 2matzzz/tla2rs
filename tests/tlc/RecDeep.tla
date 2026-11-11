---- MODULE RecDeep ----
\* A recursion 800 levels deep, which TLC still evaluates
EXTENDS Naturals
RECURSIVE Sum(_)
Sum(k) == IF k = 0 THEN 0 ELSE 1 + Sum(k - 1)
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 2 /\ Sum(800 + x) > 0
====
