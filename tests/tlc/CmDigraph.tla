---- MODULE CmDigraph ----
\* Graphs (CommunityModules) on a directed graph from the state; the operators over paths are left
\* out, as TLC 2.19 cannot evaluate them without the module's Java override
EXTENDS Naturals, Graphs, TLC
N == {1, 2, 3}
VARIABLES e, r
Facts(E) ==
  LET G == [node |-> N, edge |-> E]
  IN <<IsDirectedGraph(G), Transpose(G), IsUndirectedGraph(G), ConnectionsIn(G),
       GraphUnion(G, [node |-> {4}, edge |-> {<<4, 1>>}]), IsBipartiteWithPartitions(G, {1}, {2, 3}), HasCycle(G),
       IsDag(G), Successors(G, 1), AllSuccessors(G, {1, 2}), Predecessors(G, 2), AllPredecessors(G, {2, 3}),
       Ancestors(G, 1), Descendants(G, 1), InDegree(G, 3), OutDegree(G, 2), Roots(G), Leaves(G)>>
Init == e = {} /\ r = Facts({})
Next == Cardinality(e) < 4 /\ \E p \in N \X N : p \notin e /\ e' = e \cup {p} /\ r' = Facts(e')
Consts == <<Cardinality(DirectedSubgraph([node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 2>>}])),
            UndirectedSubgraph([node |-> {1, 2}, edge |-> {<<1, 2>>, <<2, 1>>}]), EmptyGraph, Graphs({1}),
            IsDirectedGraph([node |-> {1}, edge |-> {<<1, 2>>}]), IsDag(EmptyGraph)>>
ASSUME PrintT(Consts)
====
