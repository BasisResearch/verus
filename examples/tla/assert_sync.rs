// VerusSync with an `assert` in a transition. The macro lowers it to
// `tmp_assert => (update ...)`, so every update sits under the assertion;
// Verus proves the assertion wherever the transition is taken, and the
// export counts the updates as assigning (TLC assigns them whenever the
// assertion holds). `-V tla-export=assert_sync::Guarded`.
use vstd::prelude::*;
use verus_state_machines_macros::state_machine;

verus! {

state_machine!{ Guarded {
    fields {
        pub n: nat,
        pub s: Set<int>,
    }

    #[invariant]
    pub fn n_small(&self) -> bool {
        self.n <= 3
    }

    init!{
        initialize() {
            init n = 0;
            init s = Set::empty();
        }
    }

    transition!{
        bump() {
            require(pre.n < 3);
            assert(pre.n <= 3);
            update n = pre.n + 1;
            update s = pre.s.insert(pre.n as int);
        }
    }

    #[inductive(initialize)]
    fn initialize_inductive(post: Self) {
    }

    #[inductive(bump)]
    fn bump_inductive(pre: Self, post: Self) {
    }
}}

fn main() {
}

} // verus!
