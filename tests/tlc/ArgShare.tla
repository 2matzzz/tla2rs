---- MODULE ArgShare ----
\* An argument that the definition uses twice, passed on through 24 calls: written out at each use,
\* the innermost argument would appear 2^24 times in the expansion
EXTENDS Naturals, TLC
Twice(n) == n + n
Deep == Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(Twice(1))))))))))))))))))))))))
ASSUME PrintT(<<"deep", Deep>>)
====
