// The verus-tla shape: `init()` and `next()` return closures over the state,
// and each action is an `Action { precondition, transition }` record built
// by a spec fn. The exporter reduces the applications symbolically.
// `-V tla-export=mutex_tla`.
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(S)]
pub struct Action<S> {
    pub precondition: spec_fn(S) -> bool,
    pub transition: spec_fn(S, S) -> bool,
}

pub open spec fn step<S>(a: Action<S>) -> spec_fn(S, S) -> bool {
    |pre: S, post: S| (a.precondition)(pre) && (a.transition)(pre, post)
}

pub struct State {
    pub holder: Option<nat>,
    pub count: nat,
}

pub open spec fn acquire(t: nat) -> Action<State> {
    Action {
        precondition: |s: State| s.holder is None && s.count < 3,
        transition: |pre: State, post: State|
            post == State { holder: Some(t), count: pre.count + 1 },
    }
}

pub open spec fn release() -> Action<State> {
    Action {
        precondition: |s: State| s.holder is Some,
        transition: |pre: State, post: State| post == State { holder: None, ..pre },
    }
}

pub open spec fn init() -> spec_fn(State) -> bool {
    |s: State| s == State { holder: None, count: 0 }
}

pub open spec fn next() -> spec_fn(State, State) -> bool {
    |pre: State, post: State|
        (exists|thread: nat| thread < 2 && #[trigger] step(acquire(thread))(pre, post))
            || step(release())(pre, post)
}

pub open spec fn count_bounded() -> spec_fn(State) -> bool {
    |s: State| s.count <= 3
}

pub open spec fn held_after_acquire() -> spec_fn(State) -> bool {
    |s: State| s.holder is Some ==> s.count > 0
}

fn main() {
}

} // verus!
