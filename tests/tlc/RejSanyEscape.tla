---- MODULE RejSanyEscape ----
\* SANY accepts only the escapes \\ \" \n \t \r and \f in a string
EXTENDS Naturals
VARIABLE x
Init == x = "a\qb"
Next == UNCHANGED x
====
