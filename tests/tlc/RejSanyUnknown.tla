---- MODULE RejSanyUnknown ----
\* SANY refuses a name that is not declared or defined, also in a definition nothing uses
EXTENDS Naturals
VARIABLE x
Unused == x + missing
Init == x = 0
Next == x' = (x + 1) % 3
====
