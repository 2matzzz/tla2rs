---- MODULE Capture ----
EXTENDS Naturals
VARIABLE x, y
TypeOK == x \in 0..6 /\ y \in 0..6
Max(S) == CHOOSE m \in S : \A k \in S : k <= m
Has(S, k) == \E i \in S : i = k
Shift(i, k) == LET j == i + k
                   g(i2) == i2 + j
               IN g(i) % 7
Sum(i, j) == \E k \in {i} : k + j < 7
Init == x \in 0..2 /\ y = 0
Next == \E i \in 0..2 :
          \E k \in {i + 1} :
            /\ Has({k, x}, i + 1)
            /\ Sum(k, i)
            /\ x' = Shift(i, k)
            /\ LET i3 == x' IN y' = IF \E j \in {i3} : j > i THEN (i3 + k) % 7 ELSE Max({2, 3})
Inv == ~(x = 1 /\ y = 4)
====
