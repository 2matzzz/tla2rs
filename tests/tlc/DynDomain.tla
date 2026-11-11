---- MODULE DynDomain ----
\* Membership in [D -> R] with D from the state, for functions, functions over part of a type,
\* bags and records
EXTENDS Integers, Bags
VARIABLES dom, f, g, b, r
TypeOK == dom \subseteq {"a", "b"} /\ f \in [{"a", "b"} -> 0..1]
Init == /\ dom = {} /\ f = [x \in {"a", "b"} |-> 0] /\ g = << >> /\ b = EmptyBag
        /\ r = [a |-> 0]
Next == \/ \E x \in {"a", "b"} \ dom : dom' = dom \cup {x} /\ g' = g @@ (x :> 1)
              /\ b' = b (+) SetToBag({x}) /\ UNCHANGED <<f, r>>
        \/ UNCHANGED <<dom, f, g, b, r>>
Inv == /\ (f \in [dom -> 0..1]) = (dom = {"a", "b"})
       /\ g \in [dom -> {1}]
       /\ (b \in [dom -> {1}]) = (\A x \in dom : CopiesIn(x, b) = 1)
       /\ (r \in [dom -> {0}]) = (dom = {"a"})
\* Violated
NotFull == g \notin [{"a", "b"} -> {1}]
====
