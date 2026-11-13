---- MODULE CmQuorum ----
\* Quorum (CommunityModules): the quorum systems of a set, and a variable ranging over them
EXTENDS Naturals, FiniteSets, Quorum, TLC
CONSTANT Nodes
VARIABLE q
Init == q \in QuorumSystem(Nodes)
Next == \E r \in QuorumSystem(Nodes) : Cardinality(r) > Cardinality(q) /\ q' = r
Small == \A a \in q : Cardinality(a) >= 1
ASSUME PrintT(<<QuorumSystem({}), QuorumSystem({1}), QuorumSystem({1, 2}), Cardinality(QuorumSystem(Nodes))>>)
====
