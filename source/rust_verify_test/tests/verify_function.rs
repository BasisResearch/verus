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
mod first {
    use vstd::prelude::*;
    verus! {
    proof fn shared() { assert(4int + 4 == 8); }
    proof fn only_first() { assert(5int + 5 == 10); }
    }
}
mod second {
    use vstd::prelude::*;
    verus! {
    proof fn shared() { assert(6int + 6 == 12); }
    proof fn only_second() { assert(7int + 7 == 14); }
    }
}
"#;

// `gamma` fails, so a run that verifies it reports an error.
fn run(functions: &[&str]) -> (Output, String, String) {
    run_in(&["--verify-root"], functions)
}

// `modules` holds `--verify-root` or names for `--verify-only-module`.
fn run_in(modules: &[&str], functions: &[&str]) -> (Output, String, String) {
    let dir = tempfile::tempdir().unwrap();
    let input = dir.path().join("fixture.rs");
    fs::write(&input, CODE).unwrap();
    let current = std::env::current_exe().unwrap();
    let binary = current.parent().unwrap().parent().unwrap().join("rust_verify");
    let mut command = Command::new(binary);
    command.args(["--mcp", "--crate-type=lib", "-V", "no-solver-version-check"]);
    for m in modules {
        if *m == "--verify-root" {
            command.arg(m);
        } else {
            command.args(["--verify-only-module", m]);
        }
    }
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

#[test]
fn verify_function_bad_pattern_first_reports_the_same_error() {
    let (single, _, single_stderr) = run(&["delta"]);
    let (output, stdout, stderr) = run(&["delta", "alpha"]);
    assert!(!single.status.success() && !output.status.success());
    assert_eq!(stderr, single_stderr);
    assert!(!stdout.contains("verified"), "{}", stdout);
}

#[test]
fn verify_function_reports_every_bad_pattern() {
    let (_, _, delta_stderr) = run(&["delta"]);
    let (_, _, zeta_stderr) = run(&["zeta"]);
    let (output, stdout, stderr) = run(&["delta", "alpha", "zeta"]);
    assert!(!output.status.success());
    assert!(!stdout.contains("verified"), "{}", stdout);
    // One error, holding each pattern's message as a single flag words it
    let message = |s: &str| {
        let start = s.find("error: ").unwrap() + "error: ".len();
        let end = s.find("\nerror: aborting").unwrap();
        s[start..end].trim_end().to_string()
    };
    assert_eq!(
        message(&stderr),
        format!("{}\n       \n       {}", message(&delta_stderr), message(&zeta_stderr))
    );
    assert!(stderr.contains("error: aborting due to 1 previous error"), "{}", stderr);
}

#[test]
fn verify_function_ambiguous_pattern_among_good_ones() {
    let (single, _, single_stderr) = run(&["alph"]);
    let (output, stdout, stderr) = run(&["alpha_two", "alph", "beta"]);
    assert!(!single.status.success() && !output.status.success());
    assert!(stderr.contains("more than one match found for --verify-function alph,"), "{}", stderr);
    assert_eq!(stderr, single_stderr);
    assert!(!stdout.contains("verified"), "{}", stdout);
}

#[test]
fn verify_function_in_two_modules() {
    let (output, stdout, stderr) = run_in(&["first", "second"], &["only_first", "only_second"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(2));
    assert_eq!(stderr.matches("note: verifying module first (selected functions)").count(), 1);
    assert_eq!(stderr.matches("note: verifying module second (selected functions)").count(), 1);
}

#[test]
fn verify_function_in_two_modules_requires_qualifying_a_shared_name() {
    let (output, stdout, stderr) = run_in(&["first", "second"], &["shared"]);
    assert!(!output.status.success());
    assert!(!stdout.contains("verified"), "{}", stdout);
    assert!(
        stderr.contains(
            "error: --verify-function shared matches functions in more than one module, qualify it with the module (e.g. first::shared),\n       matched results are:\n         - first::shared\n         - second::shared\n"
        ),
        "{}",
        stderr
    );
}

#[test]
fn verify_function_in_two_modules_with_qualified_names() {
    let (output, stdout, stderr) = run_in(&["first", "second"], &["first::shared"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(1));
    assert_eq!(stderr.matches("note: verifying module second").count(), 0, "{}", stderr);

    let (output, stdout, stderr) =
        run_in(&["first", "second"], &["first::shared", "second::shared", "only_first"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(3));
}

#[test]
fn verify_function_in_root_and_a_module() {
    let (output, stdout, stderr) =
        run_in(&["--verify-root", "first"], &["crate::beta", "first::shared", "alpha_two"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(3));
}
