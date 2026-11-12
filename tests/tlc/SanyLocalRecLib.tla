---- MODULE SanyLocalRecLib ----
\* A LOCAL recursive operator, used by an exported one
LOCAL INSTANCE Naturals
RECURSIVE Sum(_)
LOCAL Sum(n) == IF n = 0 THEN 0 ELSE n + Sum(n - 1)
Total(n) == Sum(n) % 4
====
