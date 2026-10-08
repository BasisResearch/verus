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

VARIABLES holder, count
vars == <<holder, count>>

\* test_crate::init, @SOURCE@:39:1: 39:50 (#0)
init ==
    (holder = [tag |-> "None"] /\ count = 0)

\* test_crate::next, @SOURCE@:43:1: 43:57 (#0)
next ==
    ((\E thread \in 0..(2) - 1 : ((thread < 2) /\ ((LET t == thread IN ((holder = [tag |-> "None"]) /\ (count < 3))) /\ (LET t_2 == thread IN (holder' = [tag |-> "Some", v0 |-> t_2] /\ count' = (count + 1)))))) \/ ((holder.tag = "Some") /\ (holder' = [tag |-> "None"] /\ count' = [holder |-> holder, count |-> count].count)))

\* test_crate::count_bounded, @SOURCE@:49:1: 49:59 (#0)
count_bounded ==
    (count <= 3)

\* test_crate::held_after_acquire, @SOURCE@:53:1: 53:64 (#0)
held_after_acquire ==
    ((holder.tag = "Some") => (count > 0))

\* The state's integer fields stay within their types, as in Verus.
TypeOK ==
    /\ (holder.tag = "Some" => (holder.v0 >= 0))
    /\ (count >= 0)
Init == init /\ TypeOK
Next == next /\ TypeOK'
Spec == Init /\ [][Next]_vars
Inv == (count_bounded) /\ (held_after_acquire)
=============================
