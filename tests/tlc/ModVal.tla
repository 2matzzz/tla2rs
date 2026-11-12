---- MODULE ModVal ----
\* `name = [Module] value` in the cfg replaces a definition of an instantiated module by a model
\* value (here one TLC cannot evaluate, an unbounded CHOOSE)
EXTENDS Naturals
CONSTANT Items
VARIABLE held
In == INSTANCE ModValInner
Init == held = In!Nothing
Next == \/ held = In!Nothing /\ \E i \in Items : held' = i
        \/ held \in Items /\ held' = In!Nothing
Some == held /= In!Nothing
====
