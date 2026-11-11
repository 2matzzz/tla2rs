---- MODULE StrHead ----
\* Head of the empty string stops TLC like Head of the empty sequence
EXTENDS Integers, Sequences
VARIABLES w
Init == w = "ab"
Next == w' = Tail(w) /\ Head(w) # "z"
====
