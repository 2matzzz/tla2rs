---- MODULE CmJson ----
\* Json (CommunityModules): JSON text of tuples, records and functions with constant arguments
EXTENDS Naturals, Sequences, Json, TLC
VARIABLES n, out
TypeOK == n \in 0..3
Pair(k) == [left |-> k, right |-> <<k, "s">>]
Init == n = 0 /\ out = ToJsonObject(Pair(0))
Next == n < 3 /\ n' = n + 1 /\ out' = IF n' % 2 = 0 THEN ToJsonObject(Pair(2)) ELSE ToJsonArray(<<1, TRUE>>)
Short == out # ToJson(<<5>>) /\ PrintT(<<n, out>>)
Consts == <<ToJson(<<1, "a", TRUE>>), ToJson([b |-> 1, a |-> "x"]), ToJsonArray(<<>>), ToJson(<<>>), ToJsonObject(<<>>),
            ToJsonObject([b |-> <<1, 2>>, a |-> [c |-> 1], d |-> {1, 2}]), ToJsonObject(<<5, 6>>),
            ToJsonArray([b |-> 1, a |-> "x"]), ToJson([i \in {2, 3} |-> i * 2]), ToJsonObject([i \in {2, 3} |-> i * 2]),
            ToJson(<<"q\"x", <<>>, [a |-> "z"]>>), ToJsonObject([w \in {"zz", "aa"} |-> w]),
            JsonSerialize("f", 1), ndJsonSerialize("f", <<1>>)>>
ASSUME PrintT(Consts)
====
