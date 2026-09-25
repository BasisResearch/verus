---- MODULE Counter ----
\* counter.rs written by hand, to compare with its export.
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
Inc == x < 5 /\ x' = x + 1 /\ y' = y
Dbl == y < 4 /\ y' = y + 2 /\ x' = x
Next == Inc \/ Dbl
Spec == Init /\ [][Next]_<<x, y>>
Bounded == x < 4
SumSmall == x + y < 20
====
