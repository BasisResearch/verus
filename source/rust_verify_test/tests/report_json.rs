#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

use tempfile::TempDir;

/// Verify `code` with `--report-json` and return the report it wrote.
///
/// The crate is named after the source file, so every test here reports on a
/// crate called `test`.
fn report_for(code: &str) -> (serde_json::Value, std::process::Output) {
    let tempdir = TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("test.rs");
    let source = format!("{}\n{}\n{}\n", FEATURE_PRELUDE, USE_PRELUDE, code);
    std::fs::write(&entry_file, source).expect("write source file");
    let report_path = tempdir.path().join("report.json");

    let output = run_verus_raw(
        &[
            "--crate-type=lib",
            "--report-json",
            report_path.to_str().unwrap(),
            entry_file.to_str().unwrap(),
        ],
        tempdir.path(),
    );

    let text = std::fs::read_to_string(&report_path).unwrap_or_else(|err| {
        panic!(
            "no report at {}: {err}\nstderr:\n{}",
            report_path.display(),
            String::from_utf8_lossy(&output.stderr)
        )
    });
    let report = serde_json::from_str(&text).expect("the report is valid json");
    (report, output)
}

const FAILING_PRECONDITION: &str = r#"
verus!{
spec fn small(x: u64) -> bool { x < 10 }

fn requires_small(x: u64)
    requires small(x),
{
}

fn ok() {
    requires_small(3);
}

fn bad() {
    requires_small(99);
}
}
"#;

/// A consumer reads the schema and the crate off the artifact itself. Neither
/// may have to be inferred from the path it was found at or from a
/// neighbouring message in some stream.
#[test]
fn the_report_names_its_schema_and_its_crate() {
    let (report, _) = report_for(FAILING_PRECONDITION);
    assert_eq!(report["schema_version"], serde_json::json!(1));
    assert_eq!(report["crate_name"], serde_json::json!("test"));
}

/// The point of the whole artifact: Verus says which function's obligation
/// failed, so a consumer never has to work it back out by matching spans
/// against its own index of the source.
#[test]
fn a_failing_obligation_names_its_function() {
    let (report, _) = report_for(FAILING_PRECONDITION);

    let diagnostics = report["diagnostics"].as_array().expect("diagnostics array");
    assert_eq!(diagnostics.len(), 1, "one failure, one diagnostic: {:#?}", diagnostics);

    let failure = &diagnostics[0];
    assert_eq!(failure["level"], serde_json::json!("error"));
    assert_eq!(failure["message"], serde_json::json!("precondition not satisfied"));
    assert_eq!(failure["function"], serde_json::json!("test::bad"));
    assert!(
        !failure["assert_ids"].as_array().expect("assert_ids").is_empty(),
        "the failing query named an assertion: {:#?}",
        failure
    );
}

/// Spans are resolved, one-based, and carry the source they cover — the same
/// coordinates the rendered diagnostic points at.
#[test]
fn spans_are_resolved_to_source_coordinates() {
    let (report, _) = report_for(FAILING_PRECONDITION);
    let failure = &report["diagnostics"][0];

    let span = &failure["spans"][0];
    assert!(span["file"].as_str().expect("file").ends_with("test.rs"));
    assert_eq!(span["text"], serde_json::json!("requires_small(99)"));
    assert!(span["line"].as_u64().expect("line") >= 1, "lines count from one");
    assert!(span["col"].as_u64().expect("col") >= 1, "columns count from one");

    // The label is the other half of the rendered diagnostic: the clause that
    // failed, at its own span, not merged into the primary one.
    let label = &failure["labels"][0];
    assert_eq!(label["note"], serde_json::json!("failed precondition"));
    assert_eq!(label["span"]["text"], serde_json::json!("small(x)"));
}

#[test]
fn a_failing_postcondition_names_its_function_too() {
    let (report, _) = report_for(
        r#"
verus!{
fn bad_post(x: u64) -> (r: u64)
    ensures r == x + 1,
{
    x
}
}
"#,
    );

    let failure = &report["diagnostics"][0];
    assert_eq!(failure["message"], serde_json::json!("postcondition not satisfied"));
    assert_eq!(failure["function"], serde_json::json!("test::bad_post"));
}

#[test]
fn a_failing_assert_names_its_function_too() {
    let (report, _) = report_for(
        r#"
verus!{
fn has_a_bad_assert(x: u64) {
    assert(x < 10);
}
}
"#,
    );

    let failure = &report["diagnostics"][0];
    assert_eq!(failure["message"], serde_json::json!("assertion failed"));
    assert_eq!(failure["function"], serde_json::json!("test::has_a_bad_assert"));
}

/// A crate that verified reports no diagnostics and says so positively —
/// rather than leaving a consumer to read an empty list as "nothing ran".
#[test]
fn a_clean_run_reports_success_and_no_diagnostics() {
    let (report, output) = report_for(
        r#"
verus!{
spec fn small(x: u64) -> bool { x < 10 }
fn requires_small(x: u64) requires small(x), {}
fn ok() { requires_small(3); }
}
"#,
    );

    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(report["diagnostics"].as_array().expect("diagnostics").len(), 0);
    assert_eq!(report["results"]["success"], serde_json::json!(true));
    assert_eq!(report["results"]["errors"], serde_json::json!(0));
    assert_eq!(report["results"]["encountered_error"], serde_json::json!(false));
}

#[test]
fn a_failing_run_reports_the_counts_it_observed() {
    let (report, output) = report_for(FAILING_PRECONDITION);

    assert!(!output.status.success());
    assert_eq!(report["results"]["success"], serde_json::json!(false));
    assert_eq!(report["results"]["errors"], serde_json::json!(1));
    assert_eq!(report["results"]["encountered_error"], serde_json::json!(true));
    assert_eq!(report["results"]["is_verifying_entire_crate"], serde_json::json!(true));
    // `ok` verified even though `bad` did not.
    assert!(report["results"]["verified"].as_u64().expect("verified") >= 1);
}

/// Per-function detail is the same map `--output-json` prints, so a consumer
/// that already reads `func-details` needs no second parser for it.
#[test]
fn the_report_carries_per_function_detail() {
    let (report, _) = report_for(FAILING_PRECONDITION);
    let functions = report["functions"].as_object().expect("functions map");
    assert!(
        functions.contains_key("test::bad"),
        "functions are keyed by friendly rust name: {:?}",
        functions.keys().collect::<Vec<_>>()
    );
}

/// The writer creates the directory it was pointed at, and leaves nothing
/// beside the report.
///
/// It writes to a temporary and renames, so a consumer polling the path sees
/// either no file or a complete one — never a half-written object it would
/// have to tell apart from a malformed one. The leftover check is what keeps
/// that from silently becoming a plain write.
#[test]
fn the_report_is_written_whole_into_a_directory_it_creates() {
    let tempdir = TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("test.rs");
    let source = format!("{}\n{}\n{}\n", FEATURE_PRELUDE, USE_PRELUDE, FAILING_PRECONDITION);
    std::fs::write(&entry_file, source).expect("write source file");

    let nested = tempdir.path().join("does").join("not").join("exist");
    let report_path = nested.join("report.json");
    let args = [
        "--crate-type=lib",
        "--report-json",
        report_path.to_str().unwrap(),
        entry_file.to_str().unwrap(),
    ];

    // Twice: the second run must replace the first cleanly.
    for _ in 0..2 {
        run_verus_raw(&args, tempdir.path());
    }

    let text = std::fs::read_to_string(&report_path).expect("report is readable");
    let report: serde_json::Value = serde_json::from_str(&text).expect("report is complete json");
    assert_eq!(report["crate_name"], serde_json::json!("test"));

    let beside: Vec<_> = std::fs::read_dir(&nested)
        .expect("report directory")
        .filter_map(|e| e.ok())
        .map(|e| e.file_name())
        .filter(|name| name != "report.json")
        .collect();
    assert!(beside.is_empty(), "the writer left a temporary behind: {:?}", beside);
}

/// A directory takes the crate's name inside it.
///
/// Cargo invokes Verus once per target. With a fixed filename each
/// invocation would clobber the last one's report and the caller would be
/// left with whichever finished last, silently.
#[test]
fn a_directory_destination_is_named_after_the_crate() {
    let tempdir = TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("test.rs");
    let source = format!("{}\n{}\n{}\n", FEATURE_PRELUDE, USE_PRELUDE, FAILING_PRECONDITION);
    std::fs::write(&entry_file, source).expect("write source file");

    // A trailing separator names a directory that does not exist yet.
    let reports = tempdir.path().join("reports");
    let asked_for = format!("{}{}", reports.display(), std::path::MAIN_SEPARATOR);

    run_verus_raw(
        &["--crate-type=lib", "--report-json", &asked_for, entry_file.to_str().unwrap()],
        tempdir.path(),
    );

    let written = reports.join("test.json");
    let text = std::fs::read_to_string(&written).unwrap_or_else(|err| {
        let listing: Vec<_> = std::fs::read_dir(&reports)
            .map(|d| d.filter_map(|e| e.ok()).map(|e| e.file_name()).collect())
            .unwrap_or_default();
        panic!("no report at {}: {err} (found {listing:?})", written.display())
    });
    let report: serde_json::Value = serde_json::from_str(&text).expect("valid json");
    assert_eq!(report["crate_name"], serde_json::json!("test"));
}

/// `--report-json` is additive. Everything that reads `--output-json` today —
/// `tools/verita`, `verus/src/record.rs`, the metrics scripts in verified
/// projects — must see exactly what it saw before.
#[test]
fn asking_for_a_report_does_not_change_output_json() {
    let tempdir = TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("test.rs");
    let source = format!("{}\n{}\n{}\n", FEATURE_PRELUDE, USE_PRELUDE, FAILING_PRECONDITION);
    std::fs::write(&entry_file, source).expect("write source file");
    let file = entry_file.to_str().unwrap();

    let without = run_verus_raw(&["--crate-type=lib", "--output-json", file], tempdir.path());
    let with = run_verus_raw(
        &[
            "--crate-type=lib",
            "--output-json",
            "--report-json",
            tempdir.path().join("report.json").to_str().unwrap(),
            file,
        ],
        tempdir.path(),
    );

    // Compared as JSON, not as bytes: `--output-json` builds `func-details`
    // from a `HashMap`, so its key order differs between two runs of the same
    // input. (The report `--report-json` writes keys its own map in sorted
    // order, so it does not have that problem.)
    let parse = |out: &std::process::Output| -> serde_json::Value {
        serde_json::from_slice(&out.stdout).expect("--output-json emits valid json")
    };
    assert_eq!(parse(&without), parse(&with), "--report-json must not disturb the stdout report");
}
