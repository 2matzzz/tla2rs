---- MODULE LetShare ----
\* LET definitions that the next one uses twice: written out at each use, the first would appear
\* 2^23 times in the expansion of the last
EXTENDS Naturals, TLC
Chain(k) ==
  LET a1 == k + 1
      a2 == a1 + a1
      a3 == a2 + a2
      a4 == a3 + a3
      a5 == a4 + a4
      a6 == a5 + a5
      a7 == a6 + a6
      a8 == a7 + a7
      a9 == a8 + a8
      a10 == a9 + a9
      a11 == a10 + a10
      a12 == a11 + a11
      a13 == a12 + a12
      a14 == a13 + a13
      a15 == a14 + a14
      a16 == a15 + a15
      a17 == a16 + a16
      a18 == a17 + a17
      a19 == a18 + a18
      a20 == a19 + a19
      a21 == a20 + a20
      a22 == a21 + a21
      a23 == a22 + a22
      a24 == a23 + a23
  IN a24
ASSUME PrintT(<<"chain", Chain(0)>>)
====
