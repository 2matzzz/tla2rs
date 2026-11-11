---- MODULE InstU ----
\* An unnamed INSTANCE: the instantiated module's definitions become this module's, its constant
\* and variable stand for the same names here unless substituted. LOCAL INSTANCE of a standard
\* module works like EXTENDS
LOCAL INSTANCE Naturals
CONSTANT Limit
VARIABLE c
INSTANCE Counter
Inv == c < Limit
====
