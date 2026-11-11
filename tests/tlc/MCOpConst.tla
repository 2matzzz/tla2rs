---- MODULE MCOpConst ----
EXTENDS OpConst
CONSTANTS n1, n2, n3
MCNodes == {n1, n2, n3}
MCWeight(n) == IF n = n1 THEN 2 ELSE 1
MCCombine(a, b) == (a + b) % 7
MCCombineWide(a, b) == (a + b) % 10
====
