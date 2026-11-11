---- MODULE ShowState ----
\* ToString of values from the state: sets, functions, records (fields in TLC's order),
\* functions over strings (printed as records) and sequences
EXTENDS Integers, Sequences, TLC
VARIABLES size, items, cfg, seen, q, log
Keys == {"beta", "alpha"}
TypeOK == /\ size \in 0..2 /\ items \subseteq 1..3 /\ seen \in [Keys -> BOOLEAN]
          /\ cfg \in [size : 0..2, items : SUBSET (1..3)] /\ q \in Seq(0..1) /\ Len(q) <= 2
Init == /\ size = 0 /\ items = {} /\ seen = [k \in Keys |-> FALSE] /\ q = <<>>
        /\ cfg = [size |-> 0, items |-> {}] /\ log = "start"
Next == \/ /\ size < 2 /\ size' = size + 1 /\ items' = items \cup {size + 1} /\ UNCHANGED <<seen, q>>
           /\ cfg' = [cfg EXCEPT !.size = size', !.items = items']
           /\ log' = ToString(cfg') \o ToString(items')
        \/ /\ \E k \in Keys : seen' = [seen EXCEPT ![k] = TRUE] /\ UNCHANGED <<size, items, cfg, q>>
           /\ log' = ToString(seen')
        \/ /\ Len(q) < 2 /\ \E b \in 0..1 : q' = Append(q, b) /\ UNCHANGED <<size, items, cfg, seen>>
           /\ log' = ToString(q') \o ToString(<<q', size>>)
Inv == /\ log # "[size |-> 2, items |-> {1, 2}]{1, 2, 3}"
       /\ log # "[beta |-> TRUE, alpha |-> TRUE]x"
       /\ log # "<<0, 1>><<<<0, 1>>, 0>>x"
       /\ ToString(items) \in {"{}", "{1}", "{1, 2}"}
\* Violated
NotBoth == log # "[beta |-> TRUE, alpha |-> TRUE]"
NotPair == log # "<<1, 0>><<<<1, 0>>, 0>>"
NotCfg == log # "[size |-> 2, items |-> {1, 2}]{1, 2}"
====
