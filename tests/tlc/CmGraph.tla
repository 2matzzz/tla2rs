---- MODULE CmGraph ----
\* UndirectedGraphs of the CommunityModules: the graph's edges grow from the state
EXTENDS Naturals, FiniteSets, UndirectedGraphs, TLC
Nodes == {1, 2, 3}
VARIABLES edge, r
G == [node |-> Nodes, edge |-> edge]
Init == edge = {} /\ r = <<TRUE, TRUE>>
Next == \E a, b \in Nodes : {a, b} \notin edge /\ edge' = edge \cup {{a, b}}
          /\ r' = <<IsUndirectedGraph([node |-> Nodes, edge |-> edge']), IsLoopFreeUndirectedGraph([node |-> Nodes, edge |-> edge'])>>
Graph == IsUndirectedGraph(G) /\ ~IsUndirectedGraph([node |-> {1}, edge |-> edge \cup {{1, 4}}])
ASSUME PrintT(<<UndirectedSubgraph([node |-> {1, 2}, edge |-> {{1, 2}}]), UndirectedGraphs({1, 2}),
                IsUndirectedGraph([node |-> {1}, edge |-> {}, extra |-> 0])>>)
====
