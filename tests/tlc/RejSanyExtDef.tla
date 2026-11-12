---- MODULE RejSanyExtDef ----
\* SANY refuses a definition named like one of a module the spec extends
EXTENDS Naturals, SanyScopeLeft
VARIABLE x
FromLeft == 1
Init == x = 0
Next == x' = (x + 1) % 3
====
