---- MODULE Patterns ----
\* Tuple patterns after CHOOSE, in set filters and function constructors; EXCEPT into a tuple at
\* an index from the state; and a sequence bounded with UNION {[1..n -> S] : n \in 0..N}
EXTENDS Integers, Sequences
CONSTANTS Items
VARIABLES pair, i, log
TypeOK == /\ pair \in (0..2) \X (0..2) \X BOOLEAN
          /\ i \in 1..3
          /\ log \in UNION {[1..n -> Items] : n \in 0..2}
Init == pair = <<0, 0, FALSE>> /\ i = 1 /\ log = <<>>
Next == \/ /\ i < 3
           /\ pair' = [pair EXCEPT ![i] = IF i = 3 THEN ~@ ELSE (@ + 1) % 3]
           /\ i' = i + 1
           /\ UNCHANGED log
        \/ /\ i = 3
           /\ pair' = [pair EXCEPT ![i] = ~@]
           /\ i' = 1
           /\ log' = IF Len(log) < 2 THEN Append(log, (CHOOSE <<a, b>> \in Items \X Items : a # b /\ b = pair[1] + 1)[1]) ELSE <<>>
Pairs == {<<a, b>> \in (0..2) \X (0..2) : a < b}
Sums == [<<a, b>> \in Pairs |-> a + b]
Inv == /\ \A p \in Pairs : Sums[p] = p[1] + p[2]
       /\ (CHOOSE <<a, b>> \in Pairs : a + b = 3) = <<1, 2>>
       /\ pair[1] \in 0..2
\* Violated
NotThere == ~(pair = <<1, 1, TRUE>> /\ log # <<>>)
====
