---- MODULE CmRel ----
\* Relation (CommunityModules): the properties and closures of a relation from the state, given as a
\* function from pairs to booleans and as an operator
EXTENDS Naturals, Relation, TLC
S == {1, 2, 3}
VARIABLES e, r
Facts(E) ==
  LET R == [p \in S \X S |-> p \in E]
      Op(a, b) == <<a, b>> \in E
  IN <<IsReflexive(R, S), IsIrreflexive(R, S), IsSymmetric(R, S), IsAntiSymmetric(R, S), IsAsymmetric(R, S),
       IsTransitive(R, S), IsStrictlyPartiallyOrdered(R, S), IsPartiallyOrdered(R, S),
       IsStrictlyTotallyOrdered(R, S), IsTotallyOrdered(R, S), TransitiveClosure(R, S),
       ReflexiveTransitiveClosure(R, S), IsConnected(R, S),
       <<IsReflexiveUnder(Op, S), IsIrreflexiveUnder(Op, S), IsSymmetricUnder(Op, S), IsAntiSymmetricUnder(Op, S),
         IsAsymmetricUnder(Op, S), IsTransitiveUnder(Op, S), IsStrictlyPartiallyOrderedUnder(Op, S),
         IsPartiallyOrderedUnder(Op, S), IsStrictlyTotallyOrderedUnder(Op, S), IsTotallyOrderedUnder(Op, S)>>>>
Init == e = {} /\ r = Facts({})
Next == Cardinality(e) < 4 /\ \E p \in S \X S : p \notin e /\ e' = e \cup {p} /\ r' = Facts(e')
Consts == <<IsTotallyOrderedUnder(LAMBDA a, b : a <= b, 1..4), IsStrictlyTotallyOrderedUnder(LAMBDA a, b : a < b, 1..4),
            IsConnected([p \in {} \X {} |-> TRUE], {})>>
ASSUME PrintT(Consts)
====
