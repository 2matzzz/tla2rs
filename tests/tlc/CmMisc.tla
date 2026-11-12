---- MODULE CmMisc ----
\* Combinatorics, Statistics, GraphViz, DyadicRationals and VectorClocks (CommunityModules)
EXTENDS Naturals, Sequences, Combinatorics, Statistics, GraphViz, DyadicRationals, VectorClocks, TLC
VARIABLES x, r
Clock(n) == [a |-> n, b |-> 2 - n]
Facts(p) == <<IsDyadicRational(p), Add(p, Half(One)), Half(p), Add(Zero, p), Add(p, p) = One,
              factorial[p.den % 9], choose((p.den % 9) + 1, 2)>>
Init == x = One /\ r = Facts(One)
Next == x.den < 16 /\ x' = Half(x) /\ r' = Facts(x')
Log == <<[vc |-> [p |-> 1]], [vc |-> [p |-> 2, q |-> 1]], [vc |-> [p |-> 1, q |-> 2]], [vc |-> [q |-> 1]]>>
Consts == <<factorial[5], choose(5, 2), ChiSquare(<<1>>, <<2>>, 3), DotDiGraph(1, LAMBDA a : a, LAMBDA a : a),
            PrettyPrint(Zero), PrettyPrint(One), PrettyPrint(Half(Half(One))), Add(Zero, [num |-> 2, den |-> 4]), Add([num |-> 1, den |-> 2], Zero),
            IsDyadicRational([num |-> 1, den |-> 6]), IsCausalOrder(Log, LAMBDA l : l.vc),
            CausalOrder(Log, LAMBDA l : l.vc, LAMBDA l : 0, LAMBDA c : DOMAIN c),
            IsCausalOrder(<<Clock(0), Clock(1), Clock(2)>>, LAMBDA c : c)>>
ASSUME PrintT(Consts)
====
