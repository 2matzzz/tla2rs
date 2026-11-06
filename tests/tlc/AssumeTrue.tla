---- MODULE AssumeTrue ----
\* True assumptions let the search run. TLC does not check THEOREM or AXIOM,
\* even when they are false.
EXTENDS Naturals
CONSTANTS Lo, Hi
Gap == Hi - Lo
ASSUME Gap > 2
ASSUMPTION Lo \in Nat
THEOREM Gap > 100
AXIOM Lo = 99
VARIABLE x
Init == x = Lo
Next == x' = IF x < Hi THEN x + 1 ELSE Lo
Inv == x <= Hi
====
