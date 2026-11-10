---- MODULE SetUpdate ----
(* Updates that only add elements to a set or remove elements from it. `pad` widens the element
   type past 128 values, so q is stored as a sorted array. DropOther removes nothing: no element
   of q has the field `extra`. It is the only step that keeps q, so removing an element there
   would reach states with a q that no other step produces that early. *)
EXTENDS Naturals, FiniteSets

VARIABLES q, step

Elem == [k : 0..3, n : 0..2, pad : 0..15]

TypeOK == /\ q \subseteq Elem
          /\ step \in 0..5

Init == q = {} /\ step = 0

Put(k) == /\ Cardinality(q) < 3
          /\ q' = q \cup {[k |-> k, n |-> 0, pad |-> 0]}

Bump(m) == q' = (q \ {m}) \cup (IF m.n = 2 THEN {} ELSE {[m EXCEPT !.n = 2]})

Flip(m) == q' = (q \cup {[m EXCEPT !.pad = 15 - @]}) \ {m}

DropOld == /\ \E m \in q : m.n = 2
           /\ q' = q \ {m \in q : m.n = 2}

PutPair == /\ q = {}
           /\ q' = q \cup {[k |-> i, n |-> 1, pad |-> 15] : i \in 0..1}

DropOther == /\ [k |-> 0, n |-> 0, pad |-> 0] \in q
             /\ q' = q \ {[k |-> 0, n |-> 0, pad |-> 0, extra |-> TRUE]}

Next == /\ step < 5
        /\ step' = step + 1
        /\ \/ \E k \in 0..3 : Put(k)
           \/ \E m \in q : Bump(m) \/ Flip(m)
           \/ DropOld
           \/ PutPair
           \/ DropOther
====
