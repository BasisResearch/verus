#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// After a failed check under cvc5, Verus prints what the solver said about it
// between two delimiter lines. The test harness reads diagnostics as JSON, so
// here each block arrives as one note.

const BEGIN: &str = "=== verus-diagnostics begin ===";
const END: &str = "=== verus-diagnostics end ===";

/// The blocks among a run's notes.
fn blocks(err: &TestErr) -> Vec<String> {
    err.notes.iter().filter(|n| n.message.starts_with(BEGIN)).map(|n| n.message.clone()).collect()
}

const LOOPING: &str = verus_code_str! {
    uninterp spec fn f(x: int) -> bool;

    proof fn looping()
        requires
            forall|x: int| #[trigger] f(x) ==> f(x + 1),
            f(0),
    {
        assert(f(-1)); // FAILS
    }
};

test_verify_one_file_with_options! {
    #[test] matching_loop_is_named_with_its_trigger ["-V cvc5", "--rlimit 2"] => LOOPING.to_string() => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        let blocks = blocks(&err);
        assert_eq!(blocks.len(), 1, "{:?}", err.notes);
        let block = &blocks[0];
        assert!(block.ends_with(END), "{}", block);
        assert!(block.contains("function: looping"), "{}", block);
        assert!(block.contains("outcome: the solver ran out of its resource budget"), "{}", block);
        assert!(block.contains("matching loops"), "{}", block);
        assert!(block.contains("trigger: f(x)"), "{}", block);
        assert!(block.contains("f(_0)  ->  f((_0 + 1))"), "{}", block);
        assert!(block.contains("next: give the looping quantifier a trigger"), "{}", block);
    }
}

test_verify_one_file_with_options! {
    #[test] nonlinear_term_is_shown_with_its_factors ["-V cvc5"] => verus_code! {
        proof fn nonlinear(x: int, y: int)
            requires
                0 < x < 10,
                0 < y < 10,
        {
            assert(x * y < 50); // FAILS
        }
    } => Err(err) => {
        assert_one_fails(err.clone());
        let blocks = blocks(&err);
        assert_eq!(blocks.len(), 1, "{:?}", err.notes);
        let block = &blocks[0];
        assert!(block.contains("function: nonlinear"), "{}", block);
        assert!(block.contains("nonlinear terms the solver could not settle"), "{}", block);
        assert!(block.contains("x * y: the model gives it"), "{}", block);
        assert!(block.contains("by (nonlinear_arith)"), "{}", block);
    }
}

test_verify_one_file_with_options! {
    #[test] failed_assertion_shows_the_solver_equalities ["-V cvc5"] => verus_code! {
        proof fn plain(x: int)
            requires
                x > 0,
        {
            assert(x > 1); // FAILS
        }
    } => Err(err) => {
        assert_one_fails(err.clone());
        let blocks = blocks(&err);
        assert_eq!(blocks.len(), 1, "{:?}", err.notes);
        let block = &blocks[0];
        assert!(block.contains("function: plain"), "{}", block);
        assert!(block.contains("outcome: "), "{}", block);
        assert!(block.contains("equalities the solver held between the goal's terms:\n  x == 1"), "{}", block);
    }
}

test_verify_one_file_with_options! {
    #[test] no_block_when_everything_verifies ["-V cvc5"] => verus_code! {
        proof fn fine(x: int)
            requires
                x > 1,
        {
            assert(x > 0);
        }
    } => Ok(ok) => {
        assert!(blocks(&ok).is_empty());
    }
}

test_verify_one_file_with_options! {
    #[test] no_block_under_z3 ["--rlimit 2"] => LOOPING.to_string() => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(blocks(&err).is_empty(), "{:?}", err.notes);
    }
}

test_verify_one_file_with_options! {
    #[test] no_block_when_turned_off ["-V cvc5", "-V no-failure-diagnostics", "--rlimit 2"] => LOOPING.to_string() => Err(err) => {
        assert_eq!(err.errors.len(), 1);
        assert!(blocks(&err).is_empty(), "{:?}", err.notes);
    }
}
