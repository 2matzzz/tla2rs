---- MODULE NoBehaviorVar ----
\* A variable but no initial predicate in the cfg: TLC refuses it, after checking the invariants of
\* constant level and before evaluating the ASSUMEs
EXTENDS Naturals, TLC
CONSTANT K
VARIABLE x
ASSUME PrintT(<<"assume", K>>)
ASSUME K > 0
Small == K < 5
====
