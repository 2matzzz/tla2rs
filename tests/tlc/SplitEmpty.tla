---- MODULE SplitEmpty ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
\* Sets that read the state but are empty without reading it: TLC makes no action of an \E over them
Next == \E e \in {s \in {} : x > s} : x' = e
NextMap == \E e \in {x + s : s \in {}} : x' = e
NextBoth ==
  \/ \E e \in {s \in {} : x > s} : x' = e
  \/ x < 2 /\ x' = x + 1
====
