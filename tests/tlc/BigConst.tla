---- MODULE BigConst ----
\* Sets of more than TLC's limit of a million elements in constant expressions: TLC goes through
\* [D -> R], \X, [f : S] and SUBSET S without building them in \E, \A and {x \in S : P}, and
\* CHOOSE over SUBSET S too, in the order of their values
EXTENDS Naturals, FiniteSets, TLC
VARIABLE x
\* True from the n-th time it is evaluated on (counted in register 1)
Nth(n) == TLCSet(1, TLCGet(1) + 1) /\ TLCGet(1) >= n
ASSUME TLCSet(1, 0)
ASSUME \E f \in [1..20 -> 1..3] : PrintT(<<"fun", f>>) /\ Nth(5)
ASSUME TLCSet(1, 0)
ASSUME \E f \in [{"p", "q"} \X {1, 2, 3} -> 1..12] : PrintT(<<"fun2", f>>) /\ Nth(3)
ASSUME TLCSet(1, 0)
ASSUME \E t \in (1..100) \X (1..100) \X (1..200) : PrintT(<<"prod", t>>) /\ Nth(5)
ASSUME TLCSet(1, 0)
ASSUME \E r \in [b : 1..200, a : 1..100, c : 1..100] : PrintT(<<"rec", r>>) /\ Nth(5)
ASSUME TLCSet(1, 0)
ASSUME \E s \in SUBSET (1..25) : PrintT(<<"subset", s>>) /\ Nth(5)
ASSUME TLCSet(1, 0)
ASSUME ~\A f \in [1..9 -> 1..5] : Nth(4) => PrintT(<<"all", f>>) /\ FALSE
ASSUME PrintT(<<"choose", CHOOSE s \in SUBSET (1..25) : Cardinality(s) = 2 /\ 1 \notin s>>)
ASSUME PrintT(<<"filter", Cardinality({f \in [1..10 -> 1..4] : \A i \in 1..9 : f[i] <= f[i + 1]})>>)
\* The condition of a filter of such a set, and what goes through it, element by element
ASSUME TLCSet(1, 0)
ASSUME \E f \in {g \in [1..20 -> 1..2] : PrintT(<<"cond", g[19], g[20]>>)} : PrintT(<<"elem", f[19], f[20]>>) /\ Nth(2)
\* In a constant definition the checker reads
Pick == CHOOSE s \in SUBSET (1..22) : Cardinality(s) = 3 /\ 2 \in s
Init == x = Cardinality(Pick) /\ \E f \in [1..21 -> 0..1] : f[21] = 1 /\ \A i \in 1..20 : f[i] = 0
Next == x' = x
====
