// A hand-rolled transition system: `init(s)`, `next(pre, post)` as an
// `exists` over a step enum, one relational spec fn per step, and the
// invariants as `(State) -> bool` spec fns. Counter.tla is the same system
// written by hand; `-V tla-export=counter` reproduces its model-checking
// numbers (see README.md).
use vstd::prelude::*;

verus! {

pub struct State {
    pub x: nat,
    pub y: nat,
}

pub enum Step {
    Inc,
    Dbl,
}

pub open spec fn init(s: State) -> bool {
    s.x == 0 && s.y == 0
}

pub open spec fn t_inc(pre: State, post: State) -> bool {
    &&& pre.x < 5
    &&& post.x == pre.x + 1
    &&& post.y == pre.y
}

pub open spec fn t_dbl(pre: State, post: State) -> bool {
    &&& pre.y < 4
    &&& post.y == pre.y + 2
    &&& post.x == pre.x
}

pub open spec fn next_step(pre: State, post: State, step: Step) -> bool {
    match step {
        Step::Inc => t_inc(pre, post),
        Step::Dbl => t_dbl(pre, post),
    }
}

pub open spec fn next(pre: State, post: State) -> bool {
    exists|step: Step| next_step(pre, post, step)
}

// Violated: Inc runs x up to 5.
pub open spec fn bounded(s: State) -> bool {
    s.x < 4
}

pub open spec fn sum_small(s: State) -> bool {
    s.x + s.y < 20
}

fn main() {
}

} // verus!
