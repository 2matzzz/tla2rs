---- MODULE IntervalWide ----
\* Intervals keep their form in values whose shapes take more bits than one 64-bit word holds:
\* a function over 1..70, and sequences of records whose shapes do not fit beside the other
\* variables. The invariant compares ToString with the text TLC makes
EXTENDS Naturals, Sequences, TLC
VARIABLES a, b, c, d, n
R(i) == [x |-> 1..i, y |-> {i}]
Init == /\ a = [i \in 1..70 |-> IF i % 3 = 0 THEN {i} ELSE 1..(i % 3)]
        /\ b = <<R(1), R(2), R(3)>>
        /\ c = <<R(2)>>
        /\ d = <<[x |-> {}, y |-> {}]>>
        /\ n = 0
Next == /\ n < 3 /\ n' = n + 1
        /\ a' = [a EXCEPT ![n + 1] = {1, 2}, ![70] = 2..3]
        /\ b' = Append(Tail(b), R(n + 1))
        /\ c' = c \o <<[x |-> {n}, y |-> 1..n]>>
        /\ d' = <<[x |-> 2..n, y |-> {}]>> \o d
        /\ PrintT(<<n, a[1], a[2], a[70], b, c, d>>)
Inv == ToString(a[2]) \in {"1..2", "{1, 2}"}
Short == n < 2
====
