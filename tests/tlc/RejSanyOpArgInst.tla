---- MODULE RejSanyOpArgInst ----
\* The operators of a named INSTANCE: what they are passed, and their names without arguments
EXTENDS Naturals, Sequences
VARIABLE x
I == INSTANCE RejSanyOpArgInner
D1 == I!Op(Len)
D2 == I!Ap(5)
D3(p) == p
D4 == D3(I!Ap)
D5 == I!Ap
D6 == I!Ap(Len)
Init == x = 0
Next == x' = 0
====
