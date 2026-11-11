---- MODULE ArithNone ----
\* A model value reaching arithmetic is an evaluation error
EXTENDS Integers
CONSTANTS None
VARIABLES x
TypeOK == x \in (0..2) \cup {None}
Init == x = 0
Next == x' = IF x = 2 THEN None ELSE x + 1
====
