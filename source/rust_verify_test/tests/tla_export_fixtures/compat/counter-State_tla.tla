---- MODULE State_tla ----
\* Exported by verus -V tla-export from the Verus model in `test_crate`.
\* Mapping: structs are records; enum values are records with a `tag`;
\* Seq is a 1-based sequence (every index shifted once); Set is a set;
\* Map is a function (dom = DOMAIN, insert = :> @@); an ISet or IMap is a Set or
\* Map; Multiset is a function from the elements it holds to their counts (each
\* above 0, count = the value or 0); Option is a record tagged
\* None/Some with field v0; nat/int/uN are Int, and TypeOK keeps each variable
\* in its type's range (conjoined to Init, primed to Next); a spec fn is an operator, its
\* pre/post state parameters dropped and read as the unprimed/primed variables;
\* a quantifier is bounded from its guard, or from a CONSTANT Dom_<Type>.
\* What the export could not express is an Assert(FALSE, ...) that stops TLC
\* wherever it is evaluated.
EXTENDS Integers, Sequences, FiniteSets, TLC

VARIABLES x, y
vars == <<x, y>>

\* test_crate::init, @SOURCE@:20:1: 20:40 (#0)
init ==
    ((x = 0) /\ (y = 0))

\* test_crate::t_inc, @SOURCE@:24:1: 24:56 (#0)
t_inc ==
    (((x < 5) /\ (x' = (x + 1))) /\ (y' = y))

\* test_crate::t_dbl, @SOURCE@:30:1: 30:56 (#0)
t_dbl ==
    (((y < 4) /\ (y' = (y + 2))) /\ (x' = x))

\* test_crate::next_step, @SOURCE@:36:1: 36:72 (#0)
next_step(step) ==
    (LET m__ == step IN IF (m__.tag = "Inc") THEN t_inc ELSE IF (m__.tag = "Dbl") THEN t_dbl ELSE Assert(FALSE, "tla-export: no match arm applies"))

\* test_crate::next, @SOURCE@:43:1: 43:55 (#0)
next ==
    ((LET step == [tag |-> "Inc"] IN next_step(step)) \/ (LET step == [tag |-> "Dbl"] IN next_step(step)))

\* test_crate::bounded, @SOURCE@:48:1: 48:43 (#0)
bounded ==
    (x < 4)

\* test_crate::sum_small, @SOURCE@:52:1: 52:45 (#0)
sum_small ==
    ((x + y) < 20)

\* The state's integer fields stay within their types, as in Verus.
TypeOK ==
    /\ (x >= 0)
    /\ (y >= 0)
Init == init /\ TypeOK
Next == next /\ TypeOK'
Spec == Init /\ [][Next]_vars
Inv == (bounded) /\ (sum_small)
=============================
