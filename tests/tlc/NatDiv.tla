---- MODULE NatDiv ----
\* TLC's Naturals rounds \div toward zero and then down only when that is negative, so (0 - 1) \div 3
\* is 0 there; with Integers it is -1, the floor
EXTENDS Naturals, TLC
VARIABLE x
ASSUME PrintT(<<(0 - 1) \div 3, 10 \div (0 - 11), (0 - 7) \div 2, 7 \div (0 - 2), (0 - 6) \div 3>>)
Init == x \in 0..9
Next == x > 0 - 10 /\ x' = (x - 5) \div 3
====
