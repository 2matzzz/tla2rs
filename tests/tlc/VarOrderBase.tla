---- MODULE VarOrderBase ----
\* Variables and definitions that tests/tlc/VarOrderMany extends
EXTENDS Naturals, Sequences
VARIABLES total, queue
Max(a, b) == IF a > b THEN a ELSE b
Min(a, b) == IF a < b THEN a ELSE b
LOCAL Twice(a) == 2 * a
Double(a) == Twice(a)
====
