---- MODULE PrintFun ----
\* TLC keeps `[y \in S |-> e]` unevaluated: applied, it evaluates e at the argument only, at each
\* application; used as a value (compared, printed, DOMAIN, a variable's value), it evaluates e at
\* every element. Where TLC evaluates a LET definition or an argument once (an expression, or an
\* action once every variable is assigned), it keeps the function computed the first time it is
\* used as a value; before every variable is assigned, each use evaluates the definition again.
\* A definition of constant level is computed when TLC starts (all of it), but a recursive function
\* is not: it is evaluated where it is applied, the recursion too, and all of it where it is used
\* as a value
EXTENDS Naturals, TLC
VARIABLE x
Fixed == [k \in {1, 2} |-> PrintT(<<"fixed", k>>)]
R[k \in 0..2] == IF k = 0 THEN PrintT(<<"R", k>>) ELSE PrintT(<<"R", k>>) /\ R[k - 1]
Init == x = 0
Twice(f) == f[1] /\ f = f /\ f[2]
Act == x < 2 /\ LET h == [k \in {1, 2} |-> PrintT(<<"act", k, x>>)] IN h[1] /\ h[2] /\ h[1] /\ h = h /\ DOMAIN h = {1, 2} /\ x' = x + 1
After == x < 2 /\ x' = x + 1 /\ LET h == [k \in {1, 2} |-> PrintT(<<"after", k, x>>)] IN h[1] /\ h[1] /\ PrintT(h) /\ h[2] /\ h = h
Rec == x < 2 /\ x' = x + 1 /\ R[2] /\ Fixed[1]
Whole == x < 2 /\ x' = x + 1 /\ PrintT(<<"whole", R>>) /\ R[1]
Arg == x < 2 /\ x' = x + 1 /\ Twice([k \in {1, 2} |-> PrintT(<<"arg", k, x>>)])
Dom == x < 2 /\ x' = x + 1 /\ LET h == [k \in {1, 2} |-> PrintT(<<"dom", k, x>>)] IN DOMAIN h = {1, 2} /\ h[1]
Never == x < 2 /\ x' = x + 1 /\ LET h == [k \in {1, 2} |-> PrintT(<<"never", k>>)] IN TRUE
\* Once applied, DOMAIN computes nothing, and printing computes it without keeping it
F(t) == [k \in {1, 2} |-> PrintT(<<t, k, x>>)]
Str == x < 2 /\ x' = x + 1 /\ LET h == F("str") IN h[1] /\ PrintT("m1") /\ ToString(h) # "" /\ PrintT("m2") /\ h[2]
DomAfter == x < 2 /\ x' = x + 1 /\ LET h == F("dom") IN h[1] /\ PrintT("m1") /\ DOMAIN h = {1, 2} /\ PrintT("m2") /\ h[2] /\ PrintT("m3") /\ h = h /\ PrintT("m4") /\ h[1]
PrintFirst == x < 2 /\ x' = x + 1 /\ LET h == F("first") IN PrintT(h) /\ PrintT("m1") /\ h[1] /\ PrintT("m2") /\ PrintT(h)
PrintAfter == x < 2 /\ x' = x + 1 /\ LET h == F("after") IN h[1] /\ PrintT("m1") /\ PrintT(h) /\ PrintT("m2") /\ PrintT(h) /\ PrintT("m3") /\ h = h /\ PrintT("m4") /\ h[2]
Applied == LET h == F("applied") IN h[1] /\ PrintT(h) /\ h[2]
Inv == LET h == [k \in {1, 2} |-> PrintT(<<"inv", k, x>>)] IN h[2] /\ h[2] /\ h = h /\ h[1]
====
