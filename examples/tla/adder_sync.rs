// A VerusSync `state_machine!`: the macro generates `State::init(post)`,
// `State::next(pre, post)`, the `Step` enum and `init_by`/`next_by`, and the
// `#[invariant]` methods are the invariants. `-V tla-export=adder_sync::Adder`.
// The step's `v: int` parameter has no finite domain, so it is a hole: the
// .cfg asks for `Dom_Step_add_v0`.
use vstd::prelude::*;
use verus_state_machines_macros::state_machine;

verus! {

state_machine!{ Adder {
    fields {
        pub x: int,
        pub y: int,
    }

    #[invariant]
    pub fn x_eq_y(&self) -> bool {
        self.x == self.y
    }

    init!{
        initialize() {
            init x = 0;
            init y = 0;
        }
    }

    transition!{
        add(v: int) {
            require v >= 0;
            update x = pre.x + v;
            update y = pre.y + v;
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
    }

    #[inductive(add)]
    fn add_inductive(pre: Self, post: Self, v: int) {
    }
}}

fn main() {
}

} // verus!
