---- MODULE CmSet ----
\* FiniteSetsExt of the CommunityModules, on a set from the state and on constants
EXTENDS Naturals, FiniteSetsExt, TLC
VARIABLES s, r
Facts(S) == <<SumSet(S), ProductSet(S), Max(S \cup {0}), Min(S \cup {9}), Quantify(S, LAMBDA x : x > 1),
              kSubset(2, S), FoldSet(LAMBDA a, b : 10 * b + a, 0, S), ReduceSet(LAMBDA a, b : 10 * a + b, S, 5),
              MapThenSumSet(LAMBDA x : x * x, S), SymDiff(S, {1, 2})>>
Init == s = {} /\ r = Facts({})
Next == \E x \in 1..3 : \/ x \notin s /\ s' = s \cup {x} /\ r' = Facts(s')
                        \/ x \in s /\ s' = s \ {x} /\ r' = Facts(s')
Consts == <<FlattenSet({{1}, {2, 3}, {}}), Choices({{1, 2}, {3}}), Choices({}),
            ChooseUnique({1, 2, 3}, LAMBDA x : x > 2), kSubset(0, {1}), kSubset(3, {1, 2})>>
ASSUME PrintT(Consts)
====
