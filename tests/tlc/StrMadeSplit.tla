---- MODULE StrMadeSplit ----
\* TLC evaluates the set of a \E it splits the next-state relation through once, when it reads the
\* spec, before the ASSUMEs: "cb" is made before the ASSUME makes "zz". Inside a conjunction the
\* set is evaluated where the action is, after the ASSUMEs
EXTENDS Naturals, FiniteSets, Sequences
VARIABLES s
ASSUME "z" \o "z" # "q"
Init == s = {}
Next == \E e \in {"c" \o "b"} : Cardinality(s) < 2 /\ s' = s \cup {e, "z" \o "z"}
NextIn == Cardinality(s) < 2 /\ \E e \in {"c" \o "b"} : s' = s \cup {e, "z" \o "z"}
Inv == Cardinality(s) < 2
====
