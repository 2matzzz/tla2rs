---------------------------- MODULE DieHard ----------------------------
(* Measure 4 gallons with 3- and 5-gallon jugs. The counterexample to NotSolved is the answer. *)
EXTENDS Naturals

VARIABLES small, big

TypeOK == /\ small \in 0..3
          /\ big \in 0..5

Init == /\ small = 0
        /\ big = 0

Min(m, n) == IF m < n THEN m ELSE n

FillSmall == small' = 3 /\ big' = big
FillBig == big' = 5 /\ small' = small
EmptySmall == small' = 0 /\ big' = big
EmptyBig == big' = 0 /\ small' = small

SmallToBig == /\ big' = Min(big + small, 5)
              /\ small' = small - (big' - big)

BigToSmall == /\ small' = Min(big + small, 3)
              /\ big' = big - (small' - small)

Next == \/ FillSmall \/ FillBig
        \/ EmptySmall \/ EmptyBig
        \/ SmallToBig \/ BigToSmall

NotSolved == big # 4
=============================================================================
