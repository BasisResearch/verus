//! `-V observers=coverage` and `-V observers=proof-state`, read back from
//! `--report-json`. These run cvc5 (no internal test mode), which is what
//! `proof-state`'s live model evaluation has to work against.

#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

use tempfile::TempDir;

/// Verify `code` with the given observers and return the per-function
/// details of the report.
fn functions_for(code: &str, extra: &[&str]) -> serde_json::Value {
    let tempdir = TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("test.rs");
    let source = format!("{}\n{}\n{}\n", FEATURE_PRELUDE, USE_PRELUDE, code);
    std::fs::write(&entry_file, source).expect("write source file");
    let report_path = tempdir.path().join("report.json");
    let mut args = vec!["--crate-type=lib", "--report-json", report_path.to_str().unwrap()];
    args.extend_from_slice(extra);
    args.push(entry_file.to_str().unwrap());
    let output = run_verus_raw(&args, tempdir.path());
    let text = std::fs::read_to_string(&report_path).unwrap_or_else(|err| {
        panic!(
            "no report at {}: {err}\nstderr:\n{}",
            report_path.display(),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    let report: serde_json::Value = serde_json::from_str(&text).expect("valid json");
    report["functions"].clone()
}

/// Each obligation of `f`'s queries as (message, status), in query order.
fn statuses(functions: &serde_json::Value, f: &str) -> Vec<(String, String)> {
    functions[f]["obligations"]
        .as_array()
        .unwrap_or_else(|| panic!("no obligations for {}: {:#}", f, functions))
        .iter()
        .flat_map(|q| q["obligations"].as_array().unwrap().iter())
        .map(|o| {
            (o["message"].as_str().unwrap().to_string(), o["status"].as_str().unwrap().to_string())
        })
        .collect()
}

const CODE: &str = r#"
verus!{
fn bump(x: u32, y: u32) -> (r: u32)
    requires x < 100, y < 100,
    ensures r == x + y + 1,
{
    x + y
}

fn fine(a: u32) -> (r: u32)
    requires a < 10,
    ensures r < 20,
{
    let b = a + 1;
    assert(b <= 10);
    b + 1
}

fn loops(n: u32)
    requires n < 50,
{
    let mut i = 0;
    while i < n
        invariant i <= n, i < 40,
        decreases n - i,
    {
        i = i + 1;
    }
}

fn two_bad(a: u32) {
    assert(a < 5);
    assert(a > 7);
}
}
"#;

#[test]
fn coverage_says_what_became_of_each_obligation() {
    let functions = functions_for(CODE, &["-V", "observers=coverage"]);
    let s = |m: &str, st: &str| (m.to_string(), st.to_string());
    assert_eq!(
        statuses(&functions, "test::fine"),
        vec![
            s("possible arithmetic underflow/overflow", "proved"),
            s("assertion failed", "proved"),
            s("possible arithmetic underflow/overflow", "proved"),
            s("postcondition not satisfied", "proved"),
        ]
    );
    assert!(
        statuses(&functions, "test::bump").contains(&s("postcondition not satisfied", "failed"))
    );
    // coverage alone does not collect counterexamples
    assert!(functions["test::bump"].get("failing_asserts").is_none());
}

/// Loop invariants carry no assertion id: the failure is placed by its span,
/// not on the first id-less invariant.
#[test]
fn an_id_less_failure_lands_on_the_invariant_that_failed() {
    let functions = functions_for(CODE, &["-V", "observers=coverage"]);
    let loop_query = functions["test::loops"]["obligations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|q| q["desc"] == "while loop")
        .expect("the loop's query")
        .clone();
    let ends: Vec<(String, String)> = loop_query["obligations"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|o| o["message"] == "invariant not satisfied at end of loop body")
        .map(|o| {
            (o["span"].as_str().unwrap().to_string(), o["status"].as_str().unwrap().to_string())
        })
        .collect();
    assert_eq!(ends.len(), 2, "{ends:?}");
    assert_eq!(ends[0].1, "proved", "i <= n holds: {ends:?}");
    assert_eq!(ends[1].1, "failed", "i < 40 fails: {ends:?}");
}

/// With `--multiple-errors 0` the query ends at the first failure, so the
/// later assertion is unchecked, not proved.
#[test]
fn a_query_that_stops_early_leaves_obligations_unchecked() {
    let functions = functions_for(CODE, &["-V", "observers=coverage", "--multiple-errors", "0"]);
    let s = |m: &str, st: &str| (m.to_string(), st.to_string());
    assert_eq!(
        statuses(&functions, "test::two_bad"),
        vec![s("assertion failed", "failed"), s("assertion failed", "unchecked")]
    );
}

/// The counterexample is read while it is live: the false conjunct, in
/// source spelling, and the value the loop counter has there.
#[test]
fn proof_state_reports_the_false_conjunct_and_its_values() {
    let functions = functions_for(CODE, &["-V", "observers=proof-state"]);
    let failing = functions["test::loops"]["failing_asserts"].as_array().expect("failing_asserts");
    assert_eq!(failing.len(), 1, "{failing:#?}");
    let f = &failing[0];
    assert_eq!(f["message"], "invariant not satisfied at end of loop body");
    assert_eq!(f["conjuncts"][0], serde_json::json!({ "term": "(i < 40)", "value": false }));
    let i = f["values"]
        .as_array()
        .unwrap()
        .iter()
        .find(|v| v["name"] == "i")
        .unwrap_or_else(|| panic!("no value for i: {:#}", f));
    assert_eq!(i["value"], "40");
    // proof-state alone does not collect coverage
    assert!(functions["test::loops"].get("obligations").is_none());

    let bump = &functions["test::bump"]["failing_asserts"][0];
    assert_eq!(bump["conjuncts"][0]["term"], "(r == ((x + y) + 1))");
    assert_eq!(bump["conjuncts"][0]["value"], false);
}
