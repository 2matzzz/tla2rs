---- MODULE NoBehavior ----
\* A module without variables, checked with a cfg that has no SPECIFICATION, INIT or NEXT: TLC
\* evaluates the ASSUMEs and finishes with no states
EXTENDS Naturals, TLC
CONSTANT K
Square == K * K
ASSUME PrintT(<<"square", Square>>)
Small == Square < 100
====
