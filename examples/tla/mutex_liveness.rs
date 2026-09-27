// verus-tla's two-thread mutex liveness example (anvil-verifier/verus-tla,
// src/mutex_example.rs, MIT), with the parts of verus-tla it uses copied in
// (`defs`: `TempPred`, `lift_state`, `always`, `eventually`, ...; `action`:
// `Action` and its `forward`/`weak_fairness`) so it builds alone. The proof
// is verus-tla's `wf1` chain; here its body is admitted, since the export
// reads only its `requires` (the spec: init, always next, and weak fairness
// of acquire and release for every thread) and its `ensures` (the property:
// eventually both threads terminate).
// `-V tla-export=mutex_liveness` writes `Spec` with the two fairness
// conjuncts and the property as a `PROPERTY`; TLC proves it, and with the
// release fairness removed finds the lasso where a holder never releases.
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

pub mod defs {
    use vstd::prelude::*;

    pub struct Execution<T> {
        pub nat_to_state: spec_fn(nat) -> T,
    }

    impl<T> Execution<T> {
        pub open spec fn head(self) -> T {
            (self.nat_to_state)(0)
        }

        pub open spec fn head_next(self) -> T {
            (self.nat_to_state)(1)
        }

        pub open spec fn suffix(self, pos: nat) -> Self {
            Execution { nat_to_state: |i: nat| (self.nat_to_state)(i + pos) }
        }
    }

    pub type StatePred<T> = spec_fn(T) -> bool;

    pub type ActionPred<T> = spec_fn(T, T) -> bool;

    #[verifier(reject_recursive_types(T))]
    pub struct TempPred<T> {
        pub pred: spec_fn(Execution<T>) -> bool,
    }

    impl<T> TempPred<T> {
        pub open spec fn new(pred: spec_fn(Execution<T>) -> bool) -> Self {
            TempPred { pred: pred }
        }

        pub open spec fn satisfied_by(self, execution: Execution<T>) -> bool {
            (self.pred)(execution)
        }

        pub open spec fn and(self, other: Self) -> Self {
            TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) && other.satisfied_by(ex))
        }

        pub open spec fn or(self, other: Self) -> Self {
            TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) || other.satisfied_by(ex))
        }

        pub open spec fn implies(self, other: Self) -> Self {
            TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) ==> other.satisfied_by(ex))
        }

        pub open spec fn leads_to(self, other: Self) -> Self {
            always(self.implies(eventually(other)))
        }

        pub open spec fn entails(self, other: Self) -> bool {
            valid(self.implies(other))
        }
    }

    pub open spec fn lift_state<T>(state_pred: StatePred<T>) -> TempPred<T> {
        TempPred::new(|ex: Execution<T>| state_pred(ex.head()))
    }

    pub open spec fn lift_action<T>(action_pred: ActionPred<T>) -> TempPred<T> {
        TempPred::new(|ex: Execution<T>| action_pred(ex.head(), ex.head_next()))
    }

    pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
        TempPred::new(|ex: Execution<T>| forall|i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
    }

    pub open spec fn eventually<T>(temp_pred: TempPred<T>) -> TempPred<T> {
        TempPred::new(|ex: Execution<T>| exists|i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
    }

    pub open spec fn not<T>(temp_pred: TempPred<T>) -> TempPred<T> {
        TempPred::new(|ex: Execution<T>| !temp_pred.satisfied_by(ex))
    }

    pub open spec fn tla_forall<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>) -> TempPred<T> {
        TempPred::new(|ex: Execution<T>| forall|a: A| #[trigger] a_to_temp_pred(a).satisfied_by(ex))
    }

    pub open spec fn tla_exists<T, A>(a_to_temp_pred: spec_fn(A) -> TempPred<T>) -> TempPred<T> {
        TempPred::new(|ex: Execution<T>| exists|a: A| #[trigger] a_to_temp_pred(a).satisfied_by(ex))
    }

    pub open spec fn enabled<T>(action_pred: ActionPred<T>) -> StatePred<T> {
        |s: T| exists|s_prime: T| #[trigger] action_pred(s, s_prime)
    }

    pub open spec fn weak_fairness<T>(action_pred: ActionPred<T>) -> TempPred<T> {
        always(lift_state(enabled(action_pred))).leads_to(lift_action(action_pred))
    }

    pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
        forall|ex: Execution<T>| temp_pred.satisfied_by(ex)
    }

    pub open spec fn true_pred<T>() -> TempPred<T> {
        lift_state(|s: T| true)
    }
}

pub mod action {
    use super::defs::*;
    use vstd::prelude::*;

    #[verifier(reject_recursive_types(State))]
    #[verifier(reject_recursive_types(Input))]
    #[verifier(reject_recursive_types(Output))]
    pub struct Action<State, Input, Output> {
        pub precondition: spec_fn(Input, State) -> bool,
        pub transition: spec_fn(Input, State) -> (State, Output),
    }

    impl<State, Input, Output> Action<State, Input, Output> {
        pub open spec fn pre(self, input: Input) -> StatePred<State> {
            |s: State| (self.precondition)(input, s)
        }

        pub open spec fn forward(self, input: Input) -> ActionPred<State> {
            |s: State, s_prime: State| {
                &&& (self.precondition)(input, s)
                &&& s_prime == (self.transition)(input, s).0
            }
        }

        pub open spec fn weak_fairness(self, input: Input) -> TempPred<State> {
            always(lift_state(self.pre(input))).leads_to(lift_action(self.forward(input)))
        }
    }
}

use action::*;
use defs::*;

enum Tid { A, B }

enum ThreadState { Waiting, Holding, Terminated }

struct ProgramState {
    lock: bool,
    threads: Map<Tid, ThreadState>,
}

spec fn init() -> StatePred<ProgramState> {
    |s: ProgramState| {
        &&& !s.lock
        &&& s.threads.contains_key(Tid::A)
        &&& s.threads[Tid::A] is Waiting
        &&& s.threads.contains_key(Tid::B)
        &&& s.threads[Tid::B] is Waiting
    }
}

spec fn next() -> ActionPred<ProgramState> {
    |s, s_prime: ProgramState| {
        ||| thread_acquires_lock().forward(Tid::A)(s, s_prime)
        ||| thread_releases_lock().forward(Tid::A)(s, s_prime)
        ||| thread_acquires_lock().forward(Tid::B)(s, s_prime)
        ||| thread_releases_lock().forward(Tid::B)(s, s_prime)
        ||| stutter().forward(())(s, s_prime)
    }
}

spec fn thread_acquires_lock() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState| {
            !s.lock && s.threads[tid] is Waiting
        },
        transition: |tid: Tid, s: ProgramState| {
            (ProgramState {
                lock: true,
                threads: s.threads.insert(tid, ThreadState::Holding)
            }, ())
        },
    }
}

spec fn thread_releases_lock() -> Action<ProgramState, Tid, ()> {
    Action {
        precondition: |tid: Tid, s: ProgramState| {
            s.threads[tid] is Holding
        },
        transition: |tid: Tid, s: ProgramState| {
            (ProgramState {
                lock: false,
                threads: s.threads.insert(tid, ThreadState::Terminated)
            }, ())
        },
    }
}

spec fn stutter() -> Action<ProgramState, (), ()> {
    Action {
        precondition: |input: (), s: ProgramState| { true },
        transition: |input: (), s: ProgramState| { (s, ()) },
    }
}

spec fn both_threads_are_terminated() -> StatePred<ProgramState> {
    |s: ProgramState| s.threads[Tid::A] is Terminated && s.threads[Tid::B] is Terminated
}

proof fn both_threads_eventually_terminate(model: TempPred<ProgramState>)
    requires
        model.entails(lift_state(init())),
        model.entails(always(lift_action(next()))),
        model.entails(tla_forall(|tid| thread_acquires_lock().weak_fairness(tid))),
        model.entails(tla_forall(|tid| thread_releases_lock().weak_fairness(tid))),
    ensures
        model.entails(eventually(lift_state(both_threads_are_terminated()))),
{
    admit();
}

fn main() {
}

} // verus!
