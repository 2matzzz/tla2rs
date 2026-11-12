---- MODULE CmBits ----
\* Bitwise of the CommunityModules on numbers from the state
EXTENDS Naturals, Bitwise
VARIABLES a, b, r
Init == a = 0 /\ b = 0 /\ r = <<0, 0, 0, 0, 0>>
Next == \E x, y \in 0..6 : (x # a \/ y # b) /\ a' = x /\ b' = y
          /\ r' = <<x & y, x | y, x ^^ y, Not(x), shiftR(y, 1)>>
Agree == r[1] + r[2] = a + b /\ r[2] - r[1] = r[3] /\ (a | b) * 2 = (a | b) + (b | a)
====
