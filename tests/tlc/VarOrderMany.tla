---- MODULE VarOrderMany ----
\* The order TLC prints variables in when SANY's table of names grows past 143 names after some
\* variables are in it: the table grows from 191 to 383 slots, which moves them. With the variables
\* of an extended module, which come first into the table
EXTENDS VarOrderBase, FiniteSets, Bags
VARIABLES count, pc
Inc(a) == a + 1
Dec(a) == a - 1
Sq(a) == a * a
Cube(a) == a * a * a
Last(q) == q[Len(q)]
First(q) == q[1]
Sum(q) == IF q = <<>> THEN 0 ELSE First(q) + Last(q)
Steps == {"start", "run", "done"}
Flip(b) == ~b
Other(t) == 3 - t
IsEven(a) == a % 2 = 0
IsOdd(a) == ~IsEven(a)
Pos(a) == a > 0
Small(a) == a < 3
Grow(q, a) == Append(q, a)
Size(q) == Len(q)
Mid(a, b) == (a + b) \div 2
Diff(a, b) == Max(a, b) - Min(a, b)
VARIABLES turn, flag
Init == /\ count = 0 /\ total = 0 /\ queue = <<>>
        /\ pc = "start" /\ turn = 1 /\ flag = FALSE
Next == /\ count < 3
        /\ count' = Inc(count)
        /\ total' = total + Double(count)
        /\ queue' = Grow(queue, count)
        /\ pc' = IF count = 2 THEN "done" ELSE "run"
        /\ turn' = Other(turn)
        /\ flag' = Flip(flag)
Bound == total < 6
====
