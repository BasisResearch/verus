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

const MORE: &str = r#"
use vstd::prelude::*;
verus!{
fn conj(a: u32, b: u32)
    requires a > 2,
{
    assert(a > 3 && b < 2);
}

fn bits(x: u32) {
    assert(x & 1 == 0) by (bit_vector);
}

fn callee(y: u32, z: u32)
    requires y > 5 && y < z, z < 100,
{
}

fn caller(y: u32) {
    callee(y, 7);
}

fn all_big(v: &Vec<u64>) -> (r: u64)
    requires v.len() > 0,
    ensures forall|i: int| 0 <= i < v.len() ==> v[i] <= r,
{
    v[0]
}

fn fine(a: u32) -> (r: u32)
    requires a < 10,
    ensures r == a,
{
    a
}
}
"#;

/// The failing assertion of `f`, as (term, value) per conjunct, and the
/// symbols it reports values for.
fn failing(
    functions: &serde_json::Value,
    f: &str,
) -> (Vec<(String, serde_json::Value)>, Vec<String>) {
    let failing = functions[f]["failing_asserts"]
        .as_array()
        .unwrap_or_else(|| panic!("no failing_asserts for {}: {:#}", f, functions[f]));
    assert_eq!(failing.len(), 1, "{failing:#?}");
    let conjuncts = failing[0]["conjuncts"]
        .as_array()
        .unwrap()
        .iter()
        .map(|c| (c["term"].as_str().unwrap().to_string(), c["value"].clone()))
        .collect();
    let symbols = failing[0]["values"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v["symbol"].as_str().unwrap().to_string())
        .collect();
    (conjuncts, symbols)
}

/// `assert(a && b)` asserts a Verus temporary; proof-state splits it into
/// the conjuncts of its definition and reports the variables they read.
#[test]
fn proof_state_splits_an_asserted_conjunction() {
    let functions = functions_for(MORE, &["-V", "observers=proof-state"]);
    let (conjuncts, symbols) = failing(&functions, "test::conj");
    assert_eq!(
        conjuncts,
        vec![
            ("(a > 3)".to_string(), serde_json::json!(false)),
            ("(b < 2)".to_string(), serde_json::json!(true)),
        ]
    );
    assert_eq!(symbols, vec!["a!", "b!"]);
}

/// A failing call's precondition splits into the callee's requires
/// clauses at the call's arguments.
#[test]
fn proof_state_splits_a_callee_precondition() {
    let functions = functions_for(MORE, &["-V", "observers=proof-state"]);
    let (conjuncts, symbols) = failing(&functions, "test::caller");
    let terms: Vec<&str> = conjuncts.iter().map(|(t, _)| t.as_str()).collect();
    assert_eq!(terms, vec!["(y > 5)", "(y < 7)", "(7 < 100)"]);
    assert_eq!(conjuncts[0].1, serde_json::json!(false));
    assert_eq!(symbols, vec!["y!"]);
}

/// Values are the program's: the encoding's type ids and decorations
/// (`INT`, `$`, `TYPE%...`) are left out.
#[test]
fn proof_state_values_leave_out_encoding_constants() {
    let functions = functions_for(MORE, &["-V", "observers=proof-state"]);
    let (_, symbols) = failing(&functions, "test::all_big");
    assert_eq!(symbols, vec!["r!", "v!"]);
}

/// A bit-vector assert fails without a model and without an assertion id;
/// coverage still says it failed.
#[test]
fn coverage_marks_a_failing_bit_vector_assert_failed() {
    let functions = functions_for(MORE, &["-V", "observers=coverage"]);
    let s = |m: &str, st: &str| (m.to_string(), st.to_string());
    assert!(
        statuses(&functions, "test::bits")
            .contains(&s("bitvector assertion not satisfied", "failed")),
        "{:#}",
        functions["test::bits"]
    );
}

/// Under `-V axiom-usage-info` a proved query lists its unsat core; cvc5
/// prints the core over several lines.
#[test]
fn coverage_lists_used_axioms_under_cvc5() {
    let functions = functions_for(MORE, &["-V", "observers=coverage", "-V", "axiom-usage-info"]);
    let queries = functions["test::fine"]["obligations"].as_array().expect("obligations");
    let body = queries.iter().find(|q| q["kind"] == "body").expect("the body query");
    assert!(body["used_axioms"].is_array(), "{:#}", body);
    let with_axioms = functions
        .as_object()
        .unwrap()
        .values()
        .flat_map(|f| f["obligations"].as_array().into_iter().flatten())
        .filter(|q| q["used_axioms"].as_array().is_some_and(|a| !a.is_empty()))
        .count();
    assert!(with_axioms > 0, "no proved query named an axiom: {:#}", functions);
}

/// An observer name Verus does not know is an error, not a run without it.
#[test]
fn unknown_observer_names_are_rejected() {
    for (names, expected) in [
        ("covrage", "unknown observer `covrage`"),
        ("coverage,", "unknown observer ``"),
        ("test,coverage", "cannot be combined"),
    ] {
        let tempdir = TempDir::new().expect("temp dir");
        let entry_file = tempdir.path().join("test.rs");
        std::fs::write(&entry_file, format!("{}\n{}\n", FEATURE_PRELUDE, USE_PRELUDE)).unwrap();
        let observers = format!("observers={names}");
        let output = run_verus_raw(
            &["--crate-type=lib", "-V", &observers, entry_file.to_str().unwrap()],
            tempdir.path(),
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(!output.status.success(), "{}: {}", names, stderr);
        assert!(stderr.contains(expected), "{}: {}", names, stderr);
    }
}
