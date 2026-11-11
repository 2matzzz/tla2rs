---- MODULE AssumeCross ----
\* The cartesian product \X in constant positions: ASSUME, sets built from cfg constants, and
\* constant quantifier domains.
EXTENDS Naturals, FiniteSets
CONSTANTS Nodes, Root
Edges == {<<Root, s>> : s \in Nodes \ {Root}}
ASSUME Edges \subseteq Nodes \X Nodes
ASSUME \A p \in Edges : p[1] # p[2]
\* A \X B \X C is one set of triples, not pairs of pairs
ASSUME Cardinality(Nodes \X Nodes \X {1, 2}) = 18
ASSUME <<1, <<2, 3>>>> \in {1} \X ({2} \X {3})
ASSUME <<1, 2, 3>> \notin {1} \X ({2} \X {3})
ASSUME <<1, 2, 3>> \in {1} \X {2} \X {3}
ASSUME {1} \X {} = {}
ASSUME (0..1) \X {"a"} = {0, 1} \X {"a"} \cup {}
Pairs == {p \in Nodes \X Nodes : p \notin Edges}
VARIABLE n
Init == n = 0
Next == \E p \in Pairs : n' = (n + Cardinality({q \in Edges : q[2] = p[1]})) % 4
====
