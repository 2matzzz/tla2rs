---------------------------- MODULE Features ----------------------------
(* A small spec that exercises the features tla2rs supports (it has no meaning) *)
EXTENDS Naturals, FiniteSets

CONSTANTS N, Keys

VARIABLES count, owner, seen, mode

Modes == {"off", "low", "high"}

TypeOK == /\ count \in 0..N
          /\ owner \in [Keys -> 0..N]
          /\ seen \in SUBSET (0..N)
          /\ mode \in Modes

Init == /\ count \in 0..1
        /\ owner = [k \in Keys |-> 0]
        /\ seen = {count}
        /\ mode \in {m \in Modes : m # "high"}

Bump ==
  LET c == count + 1 IN
  /\ c <= N
  /\ count' = c
  /\ seen' = seen \cup {c}
  /\ mode' = CASE c = N -> "high" [] c > 1 -> "low" [] OTHER -> mode
  /\ UNCHANGED owner

Take(k) ==
  /\ owner[k] < count
  /\ \A j \in Keys : owner[j] <= N
  /\ owner' = [owner EXCEPT ![k] = @ + 1]
  /\ UNCHANGED <<count, seen, mode>>

Reset ==
  /\ count = N
  /\ \E m \in Modes \ {"high"} :
       /\ mode' = m
       /\ count' = 0
       /\ seen' = {x \in seen : x % 2 = 0}
       /\ owner' = [k \in Keys |-> IF owner[k] > 1 THEN owner[k] - 1 ELSE 0]

Next == Bump \/ (\E k \in Keys : Take(k)) \/ Reset

SeenOK == /\ Cardinality(seen) <= N + 1
          /\ {x * 1 : x \in seen} = seen
          /\ count \in seen \/ mode # "high"
          /\ \E k \in Keys : owner[k] <= count \/ count = 0
=============================================================================
