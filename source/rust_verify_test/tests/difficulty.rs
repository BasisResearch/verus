#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

/// `-V difficulty` needs cvc5, which a test gets by leaving internal test
/// mode; `--output-json` is where the records land.
const DIFFICULTY: [&str; 2] = ["--disable-internal-test-mode", "-V difficulty"];

/// The `func-details.<fun>.difficulty` records of a `--output-json` run.
fn difficulty_records(err: &TestErr, fun: &str) -> Vec<serde_json::Value> {
    let json = err.json_output.as_ref().expect("--output-json output");
    json["func-details"][fun]["difficulty"]
        .as_array()
        .unwrap_or_else(|| panic!("no difficulty records for {} in {}", fun, json))
        .clone()
}

/// The kinds of a row's tags, as `Symbols` joined them.
fn row_kinds(row: &serde_json::Value) -> Vec<String> {
    row["tags"]
        .as_array()
        .expect("tags")
        .iter()
        .map(|tag| tag["kind"].as_str().expect("kind").to_owned())
        .collect()
}

test_verify_one_file_with_options! {
    #[test] difficulty_lists_the_goal_and_the_hypotheses_of_a_verified_query
    [&DIFFICULTY[..], &["--output-json"]].concat() => verus_code! {
        uninterp spec fn enc(k: int) -> int;
        uninterp spec fn dec(v: int) -> int;

        #[verifier::external_body]
        broadcast proof fn roundtrip(k: int)
            ensures #[trigger] dec(enc(k)) == k,
        {
        }

        proof fn decode_ok(k: int, v: int, bound: int)
            requires
                v == enc(k),
                bound < 100,
            ensures
                dec(v) == k,
        {
            broadcast use roundtrip;
        }
    } => Ok(err) => {
        let records = difficulty_records(&err, "test_crate::decode_ok");
        assert_eq!(records.len(), 1, "one check, one record: {:?}", records);
        let record = &records[0];
        // the pinned cvc5 answers the key, so the reply parses
        assert_eq!(record.get("unparsed"), None, "unparsed reply: {}", record);
        assert_eq!(record["kind"], "body");
        assert_eq!(record["round"], 0);
        assert_eq!(record["result"], "valid");
        assert_eq!(record["solver_result"], "unsat");
        assert_eq!(record["difficulty"], true);
        assert_eq!(record["core"], true);
        assert_eq!(record.get("focus"), None, "only an expanded recheck is focused");

        let rows = record["rows"].as_array().expect("rows");
        // the goal is in every refutation's core
        let goal = rows
            .iter()
            .find(|row| row_kinds(row).contains(&"query".to_owned()))
            .expect("the goal is listed");
        assert_eq!(goal["in_core"], true);
        // both requires clauses are listed, whatever work they did
        let requires =
            rows.iter().filter(|row| row_kinds(row).contains(&"requires".to_owned())).count();
        assert_eq!(requires, 2, "both requires clauses are listed: {:?}", rows);
        // the axioms that did nothing are counted, not listed: most of the scope
        assert!(
            record["idle_axioms"].as_u64().expect("idle_axioms") > 0,
            "the prelude leaves idle axioms: {}",
            record
        );
    }
}

test_verify_one_file_with_options! {
    #[test] difficulty_leaves_the_verdicts_alone
    DIFFICULTY => verus_code! {
        proof fn two_errors(x: int) {
            assert(x > 0); // FAILS
            assert(x < 0); // FAILS
        }
    } => Err(err) => {
        assert_eq!(err.errors.len(), 2, "both errors are still reported: {:?}", err.errors);
    }
}

/// The refusals are argument errors, so the verifier reports them before it
/// runs anything; the test reads them off a direct run.
fn refusal(options: &[&str]) -> String {
    let dir = tempfile::tempdir().expect("temp dir");
    let file = dir.path().join("test.rs");
    std::fs::write(&file, "").expect("write");
    let current = std::env::current_exe().expect("test binary");
    let binary = current.parent().unwrap().parent().unwrap().join("rust_verify");
    let out = std::process::Command::new(binary)
        .arg(&file)
        .args(["--mcp", "--crate-type=lib"])
        .args(options)
        .output()
        .expect("run the verifier");
    String::from_utf8_lossy(&out.stderr).into_owned()
}

#[test]
fn difficulty_refuses_what_it_cannot_serve() {
    assert!(
        refusal(&["-V", "difficulty", "-V", "no-assert-ids"])
            .contains("-V difficulty and -V no-assert-ids exclude each other")
    );
    assert!(
        refusal(&["-V", "difficulty", "--resident"])
            .contains("-V difficulty is not available in resident mode")
    );
}
