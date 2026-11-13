---- MODULE PowErr ----
\* The errors of ^ in TLC's words: 0^0, a negative exponent, and a result beyond 32 bits
EXTENDS Integers
VARIABLE x
Init == x = 2
Next == x > -1 /\ x' = x - 1
InvZero == x ^ 0 = 1
InvNeg == 2 ^ (x - 1) > 0
InvBig == (x * 30000) ^ 2 > -1
====
