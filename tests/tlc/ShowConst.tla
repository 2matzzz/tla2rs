---- MODULE ShowConst ----
EXTENDS Integers, TLC
\* ToString of constant records (fields in TLC's order), functions over strings (printed as
\* records), sets of records and functions
zeta == 1
ASSUME ToString([zeta |-> 2, mu |-> 1, alpha |-> 3]) = "[zeta |-> 2, mu |-> 1, alpha |-> 3]"
ASSUME ToString([x \in {"qq", "pp"} |-> 0]) = "[qq |-> 0, pp |-> 0]"
ASSUME ToString(("rr" :> 1) @@ ("aa" :> 2)) = "[rr |-> 1, aa |-> 2]"
ASSUME ToString({[mu |-> 1], [mu |-> 0]}) = "{[mu |-> 0], [mu |-> 1]}"
ASSUME ToString(<<[mu |-> <<>>]>>) = "<<[mu |-> <<>>]>>"
ASSUME ToString([i \in {2, 3} |-> i]) = "(2 :> 2 @@ 3 :> 3)"
ASSUME ToString([i \in 1..2 |-> [j \in {"k"} |-> i]]) = "<<[k |-> 1], [k |-> 2]>>"
ASSUME ToString(1 :> 2) = "<<2>>"
ASSUME ToString([s \in SUBSET {1} |-> 0]) = "({} :> 0 @@ {1} :> 0)"
ASSUME ToString({[zeta |-> 0, mu |-> 1], [zeta |-> 1, mu |-> 0]}) = "{[zeta |-> 0, mu |-> 1], [zeta |-> 1, mu |-> 0]}"
VARIABLE v
Init == v = 0
Next == v' = v
====
