#![feature(rustc_private)]

use std::fs;
use std::process::{Command, Output};

const CODE: &str = r#"
use vstd::prelude::*;
verus! {
proof fn alpha() { assert(1int + 1 == 2); }
proof fn alpha_two() { assert(2int + 2 == 4); }
proof fn beta() { assert(3int + 3 == 6); }
proof fn gamma() { assert(false); }
}
"#;

// `gamma` fails, so a run that verifies it reports an error.
fn run(functions: &[&str]) -> (Output, String, String) {
    let dir = tempfile::tempdir().unwrap();
    let input = dir.path().join("fixture.rs");
    fs::write(&input, CODE).unwrap();
    let current = std::env::current_exe().unwrap();
    let binary = current.parent().unwrap().parent().unwrap().join("rust_verify");
    let mut command = Command::new(binary);
    command.args(["--mcp", "--crate-type=lib", "--verify-root", "-V", "no-solver-version-check"]);
    for f in functions {
        command.args(["--verify-function", f]);
    }
    let output = command.arg(&input).output().unwrap();
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    (output, stdout, stderr)
}

fn results(n: usize) -> String {
    format!(
        "verification results:: {n} verified, 0 errors (partial verification with `--verify-*`)\n"
    )
}

#[test]
fn verify_function_once() {
    let (output, stdout, stderr) = run(&["beta"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(1));
    assert_eq!(stderr.matches("note: verifying root module (selected functions)").count(), 1);
}

#[test]
fn verify_function_two_exact_names() {
    let (output, stdout, stderr) = run(&["alpha", "beta"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(2));
}

#[test]
fn verify_function_exact_name_and_prefix() {
    let (output, stdout, stderr) = run(&["beta", "alpha*"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(3));
}

#[test]
fn verify_function_overlapping_patterns_check_each_function_once() {
    let (output, stdout, stderr) = run(&["alpha*", "alpha_two", "*two"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(2));
}

#[test]
fn verify_function_includes_a_failing_function() {
    let (output, stdout, stderr) = run(&["beta", "gamma"]);
    assert!(!output.status.success());
    assert_eq!(stderr.matches("error: assertion failed").count(), 1, "{}", stderr);
    assert!(
        stdout.contains("1 verified, 1 errors (partial verification with `--verify-*`)"),
        "{}",
        stdout
    );
}

#[test]
fn verify_function_pattern_without_match_reports_the_same_error() {
    let (single, _, single_stderr) = run(&["delta"]);
    let (output, _, stderr) = run(&["alpha", "delta"]);
    assert!(!single.status.success() && !output.status.success());
    let message = "could not find function delta specified by --verify-function";
    assert!(single_stderr.contains(message), "{}", single_stderr);
    assert_eq!(stderr, single_stderr);
}
