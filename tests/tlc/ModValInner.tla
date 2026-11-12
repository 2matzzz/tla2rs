---- MODULE ModValInner ----
\* A definition that only the cfg of ModVal can give a value
CONSTANT Items
Nothing == CHOOSE x : x \notin Items
====
