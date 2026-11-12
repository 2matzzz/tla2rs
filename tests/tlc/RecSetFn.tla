---- MODULE RecSetFn ----
\* A recursive function whose value at a set is built from its values at smaller sets (the
\* orderings of a set as sequences), applied to a set from the state: its type is that of a set,
\* found while typing its body
EXTENDS Naturals, Sequences, FiniteSets
CONSTANT Items
VARIABLE pool, order
Orders(S) ==
  LET ords[ss \in SUBSET S] ==
        IF ss = {} THEN {<<>>}
        ELSE UNION {{Append(o, x) : o \in ords[ss \ {x}]} : x \in ss}
  IN ords[S]
Init == pool = Items /\ order = <<>>
Next == /\ pool /= {}
        /\ \E o \in Orders(pool) : /\ order' = o
                                   /\ pool' = pool \ {o[1]}
Short == Len(order) < 3
====
