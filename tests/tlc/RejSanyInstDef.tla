---- MODULE RejSanyInstDef ----
\* SANY refuses a definition named like one an earlier INSTANCE brought into scope
EXTENDS Naturals
VARIABLE x
INSTANCE SanyScopeBase
Shared == 1
Init == x = 0
Next == x' = (x + 1) % 3
====
