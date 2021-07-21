---- MODULE counter ----

EXTENDS Naturals

VARIABLE x

TypeOK == x \in Nat

Init == x = 0

Next == x' = x + 1

Spec == Init /\ [][Next]_x

====