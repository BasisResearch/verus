---- MODULE State_tla ----
\* Exported by verus -V tla-export from the Verus model in `test_crate::Toggle`.
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

VARIABLES on, n
vars == <<on, n>>

\* test_crate::Toggle::State::initialize, @SOURCE@:11:1: 55:3 (#11)
initialize ==
    (LET update_tmp_on == FALSE
         update_tmp_n == 0 IN ((n = update_tmp_n) /\ (on = update_tmp_on)))

\* test_crate::Toggle::State::init_by, @SOURCE@:11:1: 55:3 (#11)
init_by(step) ==
    (LET m__ == step IN IF (m__.tag = "initialize") THEN initialize ELSE IF (m__.tag = "dummy_to_use_type_params") THEN FALSE ELSE Assert(FALSE, "tla-export: no match arm applies"))

\* test_crate::Toggle::State::init, @SOURCE@:11:1: 55:3 (#11)
init ==
    ((LET step == [tag |-> "initialize"] IN init_by(step)))

\* test_crate::Toggle::State::flip, @SOURCE@:11:1: 55:3 (#11)
flip ==
    ((on = FALSE) /\ (LET update_tmp_on == TRUE
         update_tmp_n == (n + 1) IN ((n' = update_tmp_n) /\ (on' = update_tmp_on))))

\* test_crate::Toggle::State::reset, @SOURCE@:11:1: 55:3 (#11)
reset ==
    (LET update_tmp_n == n IN ((on = TRUE) /\ (LET update_tmp_on == FALSE IN ((on' = update_tmp_on) /\ (n' = update_tmp_n)))))

\* test_crate::Toggle::State::next_by, @SOURCE@:11:1: 55:3 (#11)
next_by(step) ==
    (LET m__ == step IN IF (m__.tag = "flip") THEN flip ELSE IF (m__.tag = "reset") THEN reset ELSE IF (m__.tag = "dummy_to_use_type_params") THEN FALSE ELSE Assert(FALSE, "tla-export: no match arm applies"))

\* test_crate::Toggle::State::next, @SOURCE@:11:1: 55:3 (#11)
next ==
    ((LET step == [tag |-> "flip"] IN next_by(step)) \/ (LET step == [tag |-> "reset"] IN next_by(step)))

\* test_crate::Toggle::State::n_nonneg, @SOURCE@:18:5: 18:35 (#0)
n_nonneg ==
    (n >= 0)

Init == init
Next == next
Spec == Init /\ [][Next]_vars
Inv == (n_nonneg)
=============================
