---- MODULE SpecInst ----
\* SPECIFICATION is a definition of an instance (TLC splits it after substitution)
EXTENDS Naturals
VARIABLE y
I == INSTANCE Ticker WITH N <- 3, c <- y
Spec == I!Spec
Ev2 == <>(y = 2)
Inv == y < 2
====
