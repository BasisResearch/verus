---- MODULE State_tla ----
\* Exported by verus -V tla-export from the Verus model in `test_crate::Guarded`.
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

VARIABLES n, s
vars == <<n, s>>

\* test_crate::Guarded::State::initialize, @SOURCE@:11:1: 45:3 (#11)
initialize ==
    (LET update_tmp_n == 0
         update_tmp_s == {} IN ((s = update_tmp_s) /\ (n = update_tmp_n)))

\* test_crate::Guarded::State::init_by, @SOURCE@:11:1: 45:3 (#11)
init_by(step) ==
    (LET m__ == step IN IF (m__.tag = "initialize") THEN initialize ELSE IF (m__.tag = "dummy_to_use_type_params") THEN FALSE ELSE Assert(FALSE, "tla-export: no match arm applies"))

\* test_crate::Guarded::State::init, @SOURCE@:11:1: 45:3 (#11)
init ==
    ((LET step == [tag |-> "initialize"] IN init_by(step)))

\* test_crate::Guarded::State::bump, @SOURCE@:11:1: 45:3 (#11)
bump ==
    (LET tmp_assert == TRUE IN ((n < 3) /\ (LET tmp_assert_2 == (tmp_assert /\ (n <= 3))
         update_tmp_n == (n + 1)
         update_tmp_s == (s \cup {n}) IN ((IF tmp_assert_2 THEN (s' = update_tmp_s) ELSE Assert(FALSE, "tla-export: VerusSync assert in test_crate::Guarded::State::bump fails at @SOURCE@:32:20: 32:30")) /\ (IF tmp_assert_2 THEN (n' = update_tmp_n) ELSE Assert(FALSE, "tla-export: VerusSync assert in test_crate::Guarded::State::bump fails at @SOURCE@:32:20: 32:30"))))))

\* test_crate::Guarded::State::next_by, @SOURCE@:11:1: 45:3 (#11)
next_by(step) ==
    (LET m__ == step IN IF (m__.tag = "bump") THEN bump ELSE IF (m__.tag = "dummy_to_use_type_params") THEN FALSE ELSE Assert(FALSE, "tla-export: no match arm applies"))

\* test_crate::Guarded::State::next, @SOURCE@:11:1: 45:3 (#11)
next ==
    ((LET step == [tag |-> "bump"] IN next_by(step)))

\* test_crate::Guarded::State::n_small, @SOURCE@:18:5: 18:34 (#0)
n_small ==
    (n <= 3)

\* The state's integer fields stay within their types, as in Verus.
TypeOK ==
    /\ (n >= 0)
Init == init /\ TypeOK
Next == next /\ TypeOK'
Spec == Init /\ [][Next]_vars
Inv == (n_small)
=============================
