---- MODULE AmpOp ----
\* An infix operator & defined by the spec (precedence 13, as * and &&)
EXTENDS Naturals
RECURSIVE Both(_, _, _)
Both(a, b, k) == IF a = 0 \/ b = 0 THEN 0
                 ELSE (IF a % 2 = 1 /\ b % 2 = 1 THEN k ELSE 0) + Both(a \div 2, b \div 2, 2 * k)
a & b == Both(a, b, 1)
VARIABLE m
Init == m = 1
Next == m < 12 /\ m' = m + 1
Even == m & 1 = 0 \/ m & 6 # 6 \/ m < 7
====
