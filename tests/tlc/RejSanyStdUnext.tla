---- MODULE RejSanyStdUnext ----
\* SANY refuses an operator of a standard module the spec does not extend, also in a definition nothing uses
EXTENDS Naturals
VARIABLE x
Size(s) == Len(s)
Init == x = 0
Next == x' = (x + 1) % 3
====
