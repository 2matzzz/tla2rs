---- MODULE PrintNext ----
\* Print and PrintT outside the definitions TLC evaluates when it starts: in the initial predicate,
\* in the actions and in an invariant, each time TLC evaluates them, up to a violation. With one
\* worker TLC prints them in a fixed order, which crosscheck.sh compares with the checker's
EXTENDS Naturals, TLC
VARIABLE x, y
Init == /\ x \in {0, 1}
        /\ PrintT(<<"init", x>>)
        /\ y = 0
Up == /\ x < 3
      /\ PrintT(<<"up", x, y>>)
      /\ x' = x + 1
      /\ y' = y
Flip == /\ y' = 1 - y
        /\ Print("flip", y') = y'
        /\ x' = x
Next == Up \/ Flip
Inv == PrintT(<<"inv", x, y>>) /\ x + y < 4
====
