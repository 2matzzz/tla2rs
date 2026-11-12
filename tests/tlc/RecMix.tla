---- MODULE RecMix ----
\* Sets of records with different fields: TLC orders records by their number of fields first, so
\* [tag |-> "stop"] comes before [tag |-> "go", who |-> 1] in a set, in CHOOSE and in \E, for a
\* set held as a bitmask (box) and one held as an array (wide, whose element type is large)
EXTENDS Naturals, FiniteSets
VARIABLE box, wide, pick
Kinds == {[tag |-> "go", who |-> w] : w \in {1, 2}} \cup {[tag |-> "stop"]}
Wides == {[tag |-> "go", who |-> w] : w \in {4000, 4001}} \cup {[tag |-> "stop"]}
Init == box = {} /\ wide = {} /\ pick = "none"
Next == \/ \E m \in Kinds : /\ m \notin box
                            /\ box' = box \cup {m}
                            /\ wide' = wide
                            /\ pick' = (CHOOSE x \in box' : TRUE).tag
        \/ \E m \in Wides : /\ m \notin wide
                            /\ wide' = wide \cup {m}
                            /\ box' = box
                            /\ pick' = (CHOOSE x \in wide' : TRUE).tag
Small == Cardinality(box) + Cardinality(wide) < 5
TypeOK == wide \in SUBSET ([tag : {"go"}, who : 0..5000] \cup [tag : {"stop"}])
====
