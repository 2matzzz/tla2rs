---- MODULE RecDeep ----
\* A recursion 600 levels deep (more than the old limit of 500), which TLC still evaluates
EXTENDS Naturals
RECURSIVE Sum(_)
Sum(k) == IF k = 0 THEN 0 ELSE 1 + Sum(k - 1)
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 2 /\ Sum(600 + x) > 0
====
