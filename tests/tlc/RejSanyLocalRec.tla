---- MODULE RejSanyLocalRec ----
\* A RECURSIVE declaration is exported even when its definition is LOCAL: the extending module may not define the name
EXTENDS Naturals, SanyLocalRecLib
VARIABLE k
Sum == 7
Init == k = 0
Next == k' = (k + 1) % 3
====
