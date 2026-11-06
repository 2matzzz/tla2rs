---- MODULE AssumeFalse ----
\* TLC refuses to start when an ASSUME is false, and says where it is.
EXTENDS Naturals
CONSTANTS Lo, Hi
Gap == Hi - Lo
ASSUME Lo >= 0
ASSUME Gap > 2
VARIABLE x
Init == x = Lo
Next == x' = IF x < Hi THEN x + 1 ELSE Lo
====
