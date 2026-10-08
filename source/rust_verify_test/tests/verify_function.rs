#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

use std::fs;
use std::process::Output;

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
    impl crate::second::Item { proof fn moved() { assert(10int == 10); } }
    }
}
mod second {
    use vstd::prelude::*;
    verus! {
    pub struct Item {}
    proof fn shared() { assert(6int + 6 == 12); }
    proof fn only_second() { assert(7int + 7 == 14); }
    }
}
mod point {
    use vstd::prelude::*;
    verus! {
    proof fn origin() { assert(0int == 0); }
    }
}
mod third {
    use vstd::prelude::*;
    verus! {
    #[allow(non_camel_case_types)]
    pub struct point {}
    impl point { proof fn f() { assert(8int == 8); } }
    }
}
mod a {
    use vstd::prelude::*;
    verus! {
    proof fn f() { assert(9int == 9); }
    pub struct Data {}
    impl Data { proof fn f() { assert(false); } }
    }
}
mod cell {
    use vstd::prelude::*;
    verus! {
    proof fn f() { assert(11int == 11); }
    }
}
mod fifth {
    use vstd::prelude::*;
    verus! {
    #[allow(non_camel_case_types)]
    pub struct cell {}
    impl cell { proof fn f() { assert(12int == 12); } }
    }
}
mod sixth {
    use vstd::prelude::*;
    verus! {
    #[allow(non_camel_case_types)]
    pub struct cell {}
    impl cell { proof fn f() { assert(13int == 13); } }
    }
}
mod line {
    use vstd::prelude::*;
    verus! {
    proof fn f() { assert(14int == 14); }
    #[allow(non_camel_case_types)]
    pub struct line {}
    impl line { proof fn f() { assert(15int == 15); } }
    }
}
mod eighth {
    use vstd::prelude::*;
    verus! {
    #[allow(non_camel_case_types)]
    pub struct first {}
    impl first { proof fn shared() { assert(16int == 16); } }
    }
}
mod ninth {
    use vstd::prelude::*;
    verus! {
    pub struct G<T> { t: T }
    impl G<u8> { proof fn g() { assert(17int == 17); } }
    impl G<u16> { proof fn g() { assert(18int == 18); } }
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
    let mut args = vec!["--crate-type=lib", "-V", "no-solver-version-check"];
    for m in modules {
        if *m != "--verify-root" {
            args.push("--verify-only-module");
        }
        args.push(*m);
    }
    for f in functions {
        args.extend(["--verify-function", *f]);
    }
    args.push(input.to_str().unwrap());
    let output = run_verus_raw(&args, dir.path());
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    (output, stdout, stderr)
}

// The lines of the error message, without rustc's indentation
fn error_lines(stderr: &str) -> Vec<String> {
    let start = stderr.find("error: ").unwrap() + "error: ".len();
    let end = stderr.find("\nerror: aborting").unwrap();
    stderr[start..end].trim_end().lines().map(|line| line.trim().to_string()).collect()
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
    // One error, holding each pattern's message as a single flag words it,
    // separated by a blank line
    let mut expected = error_lines(&delta_stderr);
    expected.push(String::new());
    expected.extend(error_lines(&zeta_stderr));
    assert_eq!(error_lines(&stderr), expected);
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
    assert_eq!(
        error_lines(&stderr),
        [
            "--verify-function shared matches more than one function, use a name that matches only one (e.g. first::shared),",
            "matched results are:",
            "- first::shared",
            "- second::shared",
        ]
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

#[test]
fn verify_function_wildcard_across_modules() {
    let (output, stdout, stderr) = run_in(&["first", "second"], &["*shared"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(2));
}

#[test]
fn verify_function_ambiguity_across_modules_suggests_a_wildcard_that_works() {
    let (output, _, stderr) = run_in(&["first", "second"], &["shar"]);
    assert!(!output.status.success());
    assert!(
        stderr.contains(
            "more than one match found for --verify-function shar, consider using wildcard *shar* to verify all matched results,"
        ),
        "{}",
        stderr
    );
    let (output, stdout, stderr) = run_in(&["first", "second"], &["*shar*"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(2));
}

// On main, a module-qualified pattern with a single module is "could not find function".
#[test]
fn verify_function_qualified_with_one_module() {
    let (output, stdout, stderr) = run_in(&["first"], &["first::shared"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(1));

    let (output, stdout, stderr) = run_in(&["first"], &["first::only_*"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(1));

    let (output, stdout, stderr) = run(&["crate::beta"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(1));

    // The hint's wildcard matches the same names, so it selects the functions listed
    let (output, _, stderr) = run(&["crate::alph"]);
    assert!(!output.status.success());
    assert!(stderr.contains("consider using wildcard *crate::alph* "), "{}", stderr);
    let (output, stdout, stderr) = run(&["*crate::alph*"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(2));
}

#[test]
fn verify_function_qualified_by_the_path_from_crate() {
    let (output, stdout, stderr) = run_in(&["first"], &["crate::first::shared"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(1));

    let (output, stdout, stderr) =
        run_in(&["--verify-root", "first"], &["crate::first::shared", "crate::beta"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(2));
}

// `point::f` names the method `f` of struct `third::point`; it is not `f` in module `point`.
#[test]
fn verify_function_name_that_starts_with_a_module_name() {
    let (output, stdout, stderr) = run_in(&["point", "third"], &["point::f"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(1));
    assert_eq!(stderr.matches("note: verifying module third (selected functions)").count(), 1);
    assert_eq!(stderr.matches("note: verifying module point").count(), 0, "{}", stderr);
}

// The qualified reading `f` in module `a` is an exact match,
// so it wins over `Data::f`, whose name merely contains `a::f`.
#[test]
fn verify_function_qualified_name_is_not_read_as_a_substring() {
    let (output, stdout, stderr) = run_in(&["a", "first"], &["a::f"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(1));
}

// With one module, a pattern that works on main selects what it selects on main:
// `a::f` is the unique substring match `Data::f`, which fails.
// The path from `crate` names `f` in module `a`.
#[test]
fn verify_function_qualified_with_one_module_as_on_main() {
    let (output, stdout, stderr) = run_in(&["a"], &["a::f"]);
    assert!(!output.status.success());
    assert_eq!(stderr.matches("error: assertion failed").count(), 1, "{}", stderr);
    assert!(stdout.contains("0 verified, 1 errors"), "{}", stdout);

    let (output, stdout, stderr) = run_in(&["a"], &["crate::a::f"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(1));
}

// `cell::f` names `f` in module `cell` and the methods `cell::f` in `fifth` and `sixth`.
#[test]
fn verify_function_qualified_and_unqualified_readings_are_ambiguous() {
    let (output, stdout, stderr) = run_in(&["cell", "fifth", "sixth"], &["cell::f"]);
    assert!(!output.status.success());
    assert!(!stdout.contains("verified"), "{}", stdout);
    assert_eq!(
        error_lines(&stderr),
        [
            "--verify-function cell::f matches more than one function, use a name that matches only one (e.g. crate::cell::f),",
            "matched results are:",
            "- cell::f",
            "- fifth::cell::f",
            "- sixth::cell::f",
        ]
    );

    let (output, stdout, stderr) =
        run_in(&["cell", "fifth", "sixth"], &["crate::cell::f", "fifth::cell::f"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(2));
    assert_eq!(stderr.matches("note: verifying module sixth").count(), 0, "{}", stderr);
}

// `moved` is owned by `first` but named by the path of `second::Item`,
// so it is listed by that path from the crate root, and matched by it with or without `crate::`
// (or by its full name, as on main).
#[test]
fn verify_function_names_a_function_by_its_path_from_the_crate_root() {
    let (output, _, stderr) = run_in(&["first", "second"], &["zzz"]);
    assert!(!output.status.success());
    let lines = error_lines(&stderr);
    assert!(lines.contains(&"- second::Item::moved".to_string()), "{}", stderr);
    assert!(!stderr.contains("first::fixture"), "{}", stderr);

    for pattern in
        ["crate::second::Item::moved", "second::Item::moved", "fixture::second::Item::moved"]
    {
        for modules in [&["first", "second"][..], &["first"][..]] {
            let (output, stdout, stderr) = run_in(modules, &[pattern]);
            assert!(output.status.success(), "{pattern}: {}", stderr);
            assert_eq!(stdout, results(1), "{pattern}");
        }
    }
}

// Two functions of one module that match the same name are ambiguous too,
// unless a single module is selected and the pattern works on main.
#[test]
fn verify_function_ambiguity_within_one_module() {
    // `line::f` is the path of `f` in module `line`, and the name of the method `f` of `line::line`
    let (output, stdout, stderr) = run_in(&["line", "first"], &["line::f"]);
    assert!(!output.status.success());
    assert!(!stdout.contains("verified"), "{}", stdout);
    assert_eq!(
        error_lines(&stderr),
        [
            "--verify-function line::f matches more than one function, use a name that matches only one (e.g. crate::line::f),",
            "matched results are:",
            "- line::f",
            "- line::line::f",
        ]
    );
    for pattern in ["crate::line::f", "line::line::f"] {
        let (output, stdout, stderr) = run_in(&["line", "first"], &[pattern]);
        assert!(output.status.success(), "{pattern}: {}", stderr);
        assert_eq!(stdout, results(1), "{pattern}");
    }

    // As on main: with `line` alone, `line::f` is the method's name relative to the module
    let (output, stdout, stderr) = run_in(&["line"], &["line::f"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(1));
}

// The example in the hint is a name that the same rule resolves to one function:
// `first::shared` is also the method `shared` of `eighth::first`, so the hint is `crate::first::shared`.
#[test]
fn verify_function_hint_names_just_one_function() {
    let modules = ["first", "second", "eighth"];
    let (output, _, stderr) = run_in(&modules, &["shared"]);
    assert!(!output.status.success());
    assert_eq!(
        error_lines(&stderr),
        [
            "--verify-function shared matches more than one function, use a name that matches only one (e.g. crate::first::shared),",
            "matched results are:",
            "- first::shared",
            "- second::shared",
        ]
    );
    let (output, stdout, stderr) = run_in(&modules, &["crate::first::shared"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(1));
    assert_eq!(stderr.matches("note: verifying module eighth").count(), 0, "{}", stderr);
}

// `G<u8>::g` and `G<u16>::g` are both named `G::g`: main verifies both with one module,
// and with several modules no name selects just one, so the hint is a wildcard.
#[test]
fn verify_function_functions_with_the_same_name() {
    let (output, stdout, stderr) = run_in(&["ninth"], &["G::g"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(2));

    let (output, _, stderr) = run_in(&["ninth", "first"], &["G::g"]);
    assert!(!output.status.success());
    assert_eq!(
        error_lines(&stderr),
        [
            "--verify-function G::g matches more than one function and no name matches only one of them, consider using wildcard G::g* to verify them all,",
            "matched results are:",
            "- ninth::G::g",
            "- ninth::G::g",
        ]
    );
    let (output, stdout, stderr) = run_in(&["ninth", "first"], &["G::g*"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(2));
}

#[test]
fn verify_function_repeated_bad_pattern_reports_once() {
    let (_, _, single_stderr) = run(&["delta"]);
    let (output, _, stderr) = run(&["delta", "alpha", "delta"]);
    assert!(!output.status.success());
    assert_eq!(stderr, single_stderr);
}
