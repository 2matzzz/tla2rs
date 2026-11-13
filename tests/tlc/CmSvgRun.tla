---- MODULE CmSvgRun ----
\* The SVG module of the CommunityModules in the initial states, the actions and the invariants:
\* the numbers it turns into strings come from the state
EXTENDS Integers, SVG, TLC
VARIABLES n, shape
TypeOK == n \in 0..3
Init == n = 0 /\ shape = Rect(0, 0, 10, 10, <<>>)
Next == n < 3 /\ n' = n + 1 /\ shape' = Rect(n', 2 * n', 10, 5, [fill |-> "red"])
Small == n < 3
Smaller == n < 2
InitMany == n = 0 /\ shape \in {Rect(1, 1, 2, 2, <<>>), Circle(4, 5, 6, [stroke |-> "blue"]), Line(0, 0, 7, 8, <<>>)}
Stay == UNCHANGED <<n, shape>>
Shown == n < 3 /\ n' = n + 1 /\ shape' = shape /\ PrintT(Text(n', -n', "t", <<>>).attrs)
Picked == CHOOSE k \in DOMAIN Line(n, n, n + 1, n + 1, <<>>).attrs : Line(n, n, n + 1, n + 1, <<>>).attrs[k] = ToString(n + 1)
Inv == Picked = "x2" /\ PointOnLine([x |-> n, y |-> 0], [x |-> 0, y |-> n], 2).x = n - n \div 2
Pic == n < 2 /\ n' = n + 1 /\ shape' = Image(n', n', 4, 4, "p.png", <<>>)
Doc == n < 2 /\ n' = n + 1 /\ shape' = SVGDoc(Group(<<>>, <<>>), 0, 0, n', n', <<>>)
====
