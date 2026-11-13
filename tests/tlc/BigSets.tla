---- MODULE BigSets ----
\* Constant sets of more than a thousand elements, which the checker enumerates from their parts
\* (sets of functions, products, sets of records, SUBSET) instead of writing them out. Each config
\* picks one in Init; the -Viol configs stop at an initial state that depends on the order of the
\* set's elements
EXTENDS Naturals, FiniteSets
VARIABLES v, n

Lamps == [1..11 -> BOOLEAN]
Odd == [{1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21} -> BOOLEAN]
Far == [{1, 70000} -> 1..40]
Nest == [{"p", "q"} -> [1..2 -> 1..6]]
Subs == SUBSET (1..11)
Pairs == (1..300) \X {1, 5, 9, 20}
Recs == [a : 1..100, b : BOOLEAN, c : {1, 4, 9}, d : {"x", "y"}]
Rows == [1..3 -> SUBSET {1, 2, 3, 4}]

InitLamps == v \in Lamps /\ n = 0
\* Written where it is used, over pairs
InitGrid == v \in [(1..3) \X (1..4) -> BOOLEAN] /\ n = 0
InitOdd == v \in Odd /\ n = 0
InitFar == v \in Far /\ n = 0
InitNest == v \in Nest /\ n = 0
InitSubs == v \in Subs /\ n = 0
InitPairs == v \in Pairs /\ n = 0
InitRecs == v \in Recs /\ n = 0
InitRows == v \in Rows /\ n = 0

Flip == n' = 1 - n /\ UNCHANGED v

\* Each holds in the first elements of its set, and fails at an element whose place depends on
\* the order
LampsOk == ~v[2] /\ ~v[5]
GridOk == ~v[<<1, 2>>] /\ ~v[<<3, 1>>]
NestOk == v["p"][1] + v["q"][2] < 9
SubsOk == Cardinality(v) < 2 \/ 7 \notin v
PairsOk == v[2] # 9 \/ v[1] < 5
RecsOk == v.a < 50 \/ v.d = "x"
====
