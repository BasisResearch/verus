---- MODULE State_tla ----
\* Exported by verus -V tla-export from the Verus model in `test_crate::Adder`.
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

CONSTANTS Dom_Step_add_v0

VARIABLES x, y
vars == <<x, y>>

\* test_crate::Adder::State::initialize, @SOURCE@:11:1: 44:3 (#11)
initialize ==
    (LET update_tmp_x == 0
         update_tmp_y == 0 IN ((y = update_tmp_y) /\ (x = update_tmp_x)))

\* test_crate::Adder::State::init_by, @SOURCE@:11:1: 44:3 (#11)
init_by(step) ==
    (LET m__ == step IN IF (m__.tag = "initialize") THEN initialize ELSE IF (m__.tag = "dummy_to_use_type_params") THEN FALSE ELSE Assert(FALSE, "tla-export: no match arm applies"))

\* test_crate::Adder::State::init, @SOURCE@:11:1: 44:3 (#11)
init ==
    ((LET step == [tag |-> "initialize"] IN init_by(step)))

\* test_crate::Adder::State::add, @SOURCE@:11:1: 44:3 (#11)
add(v) ==
    ((v >= 0) /\ (LET update_tmp_x == (x + v)
         update_tmp_y == (y + v) IN ((y' = update_tmp_y) /\ (x' = update_tmp_x))))

\* test_crate::Adder::State::next_by, @SOURCE@:11:1: 44:3 (#11)
next_by(step) ==
    (LET m__ == step IN IF (m__.tag = "add") THEN (LET v == m__.v0 IN add(v)) ELSE IF (m__.tag = "dummy_to_use_type_params") THEN FALSE ELSE Assert(FALSE, "tla-export: no match arm applies"))

\* test_crate::Adder::State::next, @SOURCE@:11:1: 44:3 (#11)
next ==
    ((\E v0__ \in Dom_Step_add_v0 : (LET step == [tag |-> "add", v0 |-> v0__] IN next_by(step))))

\* test_crate::Adder::State::x_eq_y, @SOURCE@:18:5: 18:33 (#0)
x_eq_y ==
    (x = y)

Init == init
Next == next
Spec == Init /\ [][Next]_vars
Inv == (x_eq_y)
=============================
