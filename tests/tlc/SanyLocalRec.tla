---- MODULE SanyLocalRec ----
\* An extended module whose exported operator uses a LOCAL recursive one
EXTENDS Naturals, SanyLocalRecLib
VARIABLE k
Init == k = 0
Next == k' = Total(k + 2)
====
