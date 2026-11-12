---- MODULE CmFun ----
\* Functions and Folds of the CommunityModules, on a function from the state and on constants
EXTENDS Naturals, Sequences, Functions, TLC
VARIABLES f, r
\* A fold that is not commutative shows the order the elements are taken in
Digits(g) == FoldFunction(LAMBDA a, b : 10 * b + a, 0, g)
Facts(g) == <<Range(g), IsInjective(g), Digits(g), SumFunction(g),
              RestrictValues(g, LAMBDA v : v > 0), AntiFunction(g)>>
Init == f = <<0, 1, 2>> /\ r = Facts(<<0, 1, 2>>)
Next == \E i \in 1..3, v \in 0..2 : f[i] # v /\ f' = [f EXCEPT ![i] = v] /\ r' = Facts(f')
Consts == <<Restrict(<<5, 6, 7>>, {1, 3}), RestrictDomain(<<5, 6, 7>>, LAMBDA i : i > 1),
            IsRestriction(<<5>>, <<5, 6>>), IsRestriction(<<6>>, <<5, 6>>),
            Pointwise(<<1, 2>>, <<3, 4>>, LAMBDA a, b : a * b),
            Inverse(<<"a", "b">>, {1, 2}, {"b", "c"}),
            Injection({1, 2}, {3, 4}), Surjection({1, 2, 3}, {1, 2}), Bijection({1, 2}, {3, 4}),
            ExistsInjection({1, 2, 3}, {1, 2}), ExistsSurjection({1}, {1, 2}), ExistsBijection({1, 2}, {3, 4}),
            SumFunctionOnSet(<<4, 5, 6>>, {1, 2}),
            FoldFunctionOnSet(LAMBDA a, b : <<a>> \o b, <<>>, <<7, 8, 9>>, {1, 3}),
            MapThenFoldSet(LAMBDA a, b : a \o b, <<>>, LAMBDA x : <<x, x>>, LAMBDA T : CHOOSE x \in T : TRUE, {3, 1, 2})>>
ASSUME PrintT(Consts)
Small == r[4] < 6
====
