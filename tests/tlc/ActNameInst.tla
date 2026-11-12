---- MODULE ActNameInst ----
\* The actions of an unnamed INSTANCE with substitutions keep the INSTANCE statement as their
\* position in a trace
EXTENDS Naturals
VARIABLE y
INSTANCE Counter WITH Limit <- 3, c <- y
Inv == y < 2
====
