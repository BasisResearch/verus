// A VerusSync `state_machine!` whose transitions take no parameters, so the
// macro generates a `<transition>_enabled(pre)` predicate for each: a
// `(State) -> bool` spec fn like an invariant, but not one. The invariants are
// the conjuncts of the generated `State::invariant`, here only `n_nonneg`.
// `-V tla-export=toggle_sync::Toggle`.
use vstd::prelude::*;
use verus_state_machines_macros::state_machine;

verus! {

state_machine!{ Toggle {
    fields {
        pub on: bool,
        pub n: int,
    }

    #[invariant]
    pub fn n_nonneg(&self) -> bool {
        self.n >= 0
    }

    init!{
        initialize() {
            init on = false;
            init n = 0;
        }
    }

    transition!{
        flip() {
            require !pre.on;
            update on = true;
            update n = pre.n + 1;
        }
    }

    transition!{
        reset() {
            require pre.on;
            update on = false;
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
    }

    #[inductive(flip)]
    fn flip_inductive(pre: Self, post: Self) {
    }

    #[inductive(reset)]
    fn reset_inductive(pre: Self, post: Self) {
    }
}}

fn main() {
}

} // verus!
