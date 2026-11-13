---- MODULE LetUnused ----
\* A LET definition of state level in a branch the compiler drops (the condition compares tuples of
\* different lengths, decided by their types): the checker computes such a definition on first use,
\* and must still compile when nothing uses it
EXTENDS Naturals
CONSTANTS Pa, Pb
VARIABLE x
Init == x = TRUE
Next == x' = ~x
Inv == Pb = (IF <<1>> # <<1, 0>> THEN Pa ELSE (LET l == {c \in {} : x} IN IF l = {} THEN Pa ELSE CHOOSE d \in l : TRUE))
====
