---- MODULE InstRef ----
\* Two counters whose sum, modulo 4, refines Hour; the substitution is an expression
EXTENDS Naturals
VARIABLE lo, hi
Init == lo = 0 /\ hi = 0
Next == \/ lo < 1 /\ lo' = lo + 1 /\ hi' = hi
        \/ lo = 1 /\ lo' = 0 /\ hi' = (hi + 2) % 4
Abs == INSTANCE Hour WITH Max <- 4, h <- (lo + hi) % 4
Wrong == INSTANCE Hour WITH Max <- 4, h <- hi
Inv == Abs!Exists({lo + hi})
Refines == Abs!Spec
RefinesWrong == Wrong!Spec
====
