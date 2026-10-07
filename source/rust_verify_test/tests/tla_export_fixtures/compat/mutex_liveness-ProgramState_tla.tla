---- MODULE ProgramState_tla ----
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
\* Temporal (verus-tla): always is [], eventually <>, leads_to ~>, lift_state(p)
\* the state formula p, always(lift_action(a)) [][A]_vars, weak_fairness WF_vars(A)
\* of the action's forward step, tla_forall/tla_exists bounded quantifiers. Shared
\* WF_vars fairness is in Spec; other spec assumptions are a property's premises.
EXTENDS Integers, Sequences, FiniteSets, TLC

VARIABLES lock, threads
vars == <<lock, threads>>

\* test_crate::init, @SOURCE@:164:6: 164:42 (#0)
init ==
    (((((lock = FALSE) /\ ([tag |-> "A"] \in DOMAIN threads)) /\ (threads[[tag |-> "A"]] = [tag |-> "Waiting"])) /\ ([tag |-> "B"] \in DOMAIN threads)) /\ (threads[[tag |-> "B"]] = [tag |-> "Waiting"]))

\* test_crate::thread_acquires_lock().forward(input), @SOURCE@:184:6: 184:64 (#0)
thread_acquires_lock(input) ==
    ((LET tid == input IN ((lock = FALSE) /\ (threads[tid] = [tag |-> "Waiting"]))) /\ (LET s__ == (LET tid_2 == input IN <<[lock |-> TRUE, threads |-> ((tid_2 :> [tag |-> "Holding"]) @@ threads)], <<>>>>)[1] IN lock' = s__.lock /\ threads' = s__.threads))

\* test_crate::thread_releases_lock().forward(input), @SOURCE@:198:6: 198:64 (#0)
thread_releases_lock(input) ==
    ((LET tid == input IN (threads[tid] = [tag |-> "Holding"])) /\ (LET s__ == (LET tid_2 == input IN <<[lock |-> FALSE, threads |-> ((tid_2 :> [tag |-> "Terminated"]) @@ threads)], <<>>>>)[1] IN lock' = s__.lock /\ threads' = s__.threads))

\* test_crate::stutter().forward(()), @SOURCE@:212:6: 212:50 (#0)
stutter ==
    LET input == <<>> IN ((LET input_2 == input IN TRUE) /\ (LET s__ == (LET input_3 == input IN <<[lock |-> lock, threads |-> threads], <<>>>>)[1] IN lock' = s__.lock /\ threads' = s__.threads))

\* test_crate::next, @SOURCE@:174:6: 174:43 (#0)
next ==
    ((((thread_acquires_lock([tag |-> "A"]) \/ thread_releases_lock([tag |-> "A"])) \/ thread_acquires_lock([tag |-> "B"])) \/ thread_releases_lock([tag |-> "B"])) \/ stutter)

\* test_crate::both_threads_are_terminated, @SOURCE@:219:6: 219:65 (#0)
both_threads_are_terminated ==
    ((threads[[tag |-> "A"]] = [tag |-> "Terminated"]) /\ (threads[[tag |-> "B"]] = [tag |-> "Terminated"]))

Init == (threads \in UNION {[d__ -> ({[tag |-> "Waiting"]} \cup {[tag |-> "Holding"]} \cup {[tag |-> "Terminated"]})] : d__ \in SUBSET ({[tag |-> "A"]} \cup {[tag |-> "B"]})}) /\ init
Next == next
\* The fairness of the properties' spec (the requires of test_crate::both_threads_eventually_terminate (model.entails(...))).
Fairness ==
    /\ (\A tid \in ({[tag |-> "A"]} \cup {[tag |-> "B"]}) : WF_vars(thread_acquires_lock(tid)))
    /\ (\A tid \in ({[tag |-> "A"]} \cup {[tag |-> "B"]}) : WF_vars(thread_releases_lock(tid)))
Spec == Init /\ [][Next]_vars /\ Fairness
\* test_crate::both_threads_eventually_terminate, @SOURCE@:223:7: 223:74 (#0); spec: the requires of test_crate::both_threads_eventually_terminate (model.entails(...))
both_threads_eventually_terminate ==
    <>(both_threads_are_terminated)
====================================
