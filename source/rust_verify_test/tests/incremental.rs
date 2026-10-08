//! The per-query verdict cache (`VERUS_INCREMENTAL_CACHE`, rust_verify/src/incremental.rs): a
//! second run over unchanged source solves nothing, an edit re-solves only the queries it changed,
//! and a cached failure is reported again, at its moved lines, with the same exit status.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

/// A cache directory of this test's own, under the test target directory.
fn cache_dir(test: &str) -> String {
    let exe = std::env::current_exe().unwrap();
    let dir =
        exe.parent().unwrap().parent().unwrap().join("test_inputs").join(format!("cache-{test}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir.to_str().unwrap().to_owned()
}

/// What the last run against `dir` looked up, replayed and solved, as `runs.jsonl` records it.
fn last_run(dir: &str) -> (u64, u64, u64) {
    let text = std::fs::read_to_string(format!("{dir}/runs.jsonl")).unwrap();
    let run: serde_json::Value = serde_json::from_str(text.lines().last().unwrap()).unwrap();
    (
        run["queries"].as_u64().unwrap(),
        run["replayed"].as_u64().unwrap(),
        run["solved"].as_u64().unwrap(),
    )
}

fn run(name: &str, dir: &str, code: String) -> Result<TestErr, TestErr> {
    let option = format!("--incremental-cache={dir}");
    verify_one_file(name, code, &[option.as_str()])
}

const TWO_LEMMAS: &str = verus_code_str! {
    spec fn double(x: int) -> int { 2 * x }

    proof fn lemma_a(x: int)
        requires x > 0,
        ensures double(x) > x,
    {
    }

    proof fn lemma_b(x: int)
        requires x >= 0,
        ensures double(x) >= x,
    {
        assert(double(x) == x + x);
    }
};

#[test]
fn second_run_replays_every_query() {
    let dir = cache_dir("second_run_replays_every_query");
    run("second_run_replays_every_query_1", &dir, TWO_LEMMAS.to_string()).unwrap();
    let (queries, replayed, solved) = last_run(&dir);
    assert!(
        queries > 0 && replayed == 0 && solved == queries,
        "first run: {queries} {replayed} {solved}"
    );
    run("second_run_replays_every_query_2", &dir, TWO_LEMMAS.to_string()).unwrap();
    assert_eq!(last_run(&dir), (queries, queries, 0));
}

#[test]
fn an_edit_re_solves_only_its_function() {
    let dir = cache_dir("an_edit_re_solves_only_its_function");
    run("an_edit_re_solves_only_its_function_1", &dir, TWO_LEMMAS.to_string()).unwrap();
    let (queries, _, _) = last_run(&dir);
    // lemma_b's body changes, and a blank line above lemma_a moves it: only lemma_b is solved again
    let edited = TWO_LEMMAS.replace("assert(double(x) == x + x);", "assert(double(x) == 2 * x);");
    let edited = format!("\n\n{edited}");
    run("an_edit_re_solves_only_its_function_2", &dir, edited).unwrap();
    assert_eq!(last_run(&dir), (queries, queries - 1, 1));
}

#[test]
fn a_new_lemma_leaves_the_others_cached() {
    let dir = cache_dir("a_new_lemma_leaves_the_others_cached");
    run("a_new_lemma_leaves_the_others_cached_1", &dir, TWO_LEMMAS.to_string()).unwrap();
    let (queries, _, _) = last_run(&dir);
    // a lemma neither of the others calls joins the module: its declaration and contract axioms
    // are below their queries now, but neither reaches them
    let added = format!(
        "{TWO_LEMMAS}\n{}",
        verus_code_str! {
            proof fn lemma_c(x: int)
                ensures double(x) == x + x,
            {
            }
        }
    );
    run("a_new_lemma_leaves_the_others_cached_2", &dir, added).unwrap();
    assert_eq!(last_run(&dir), (queries + 1, queries, 1));
}

#[test]
fn a_cached_failure_is_reported_again_at_its_new_line() {
    let dir = cache_dir("a_cached_failure_is_reported_again_at_its_new_line");
    let failing = verus_code_str! {
        proof fn lemma_ok(x: int)
            requires x > 0,
            ensures x + 1 > 1,
        {
        }

        proof fn lemma_bad(x: int)
            requires x > 0,
        {
            assert(x > 1); // FAILS
        }
    };
    let err =
        run("a_cached_failure_is_reported_again_at_its_new_line_1", &dir, failing.to_string())
            .unwrap_err();
    assert_eq!(err.errors.len(), 1);
    let line = relevant_error_span(&err.errors[0].spans).line_start;
    let (queries, _, solved) = last_run(&dir);
    assert_eq!(solved, queries);

    // the same file three lines lower: the failure is replayed, not solved, at the moved line,
    // and the run still fails
    let moved = format!("\n\n\n{failing}");
    let err = run("a_cached_failure_is_reported_again_at_its_new_line_2", &dir, moved).unwrap_err();
    assert_eq!(err.errors.len(), 1);
    assert_eq!(err.errors[0].message, "assertion failed");
    assert_eq!(relevant_error_span(&err.errors[0].spans).line_start, line + 3);
    assert_eq!(last_run(&dir), (queries, queries, 0));
}
