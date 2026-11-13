---- MODULE ConstLetVar ----
\* Whether TLC evaluates an invariant once when it starts depends on its bound on the level of
\* the definition: every LET definition and argument counts, used or not. These invariants read
\* x only in such a place, so TLC checks them on each state (and not as a constant FALSE)
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = 1 - x
Ignore(a) == 1 = 2
InvLet == LET l == x IN 1 = 2
InvArg == Ignore(x)
InvConst == LET l == 3 IN 1 = 2
====
