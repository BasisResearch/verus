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
pub struct S<T> { t: T }
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
mod ta {
    use vstd::prelude::*;
    verus! {
    impl crate::S<u8> { proof fn f() { assert(19int == 19); } }
    }
}
mod tb {
    use vstd::prelude::*;
    verus! {
    impl crate::S<u16> { proof fn f() { assert(20int == 20); } }
    }
}
mod eleventh {
    use vstd::prelude::*;
    verus! {
    impl crate::ninth::G<u32> { proof fn g() { assert(21int == 21); } }
    impl crate::ninth::G<u64> { proof fn g() { assert(22int == 22); } }
    }
}
mod twelfth {
    use vstd::prelude::*;
    verus! {
    pub trait Tw { proof fn tw(); }
    impl Tw for Seq<int> { proof fn tw() { assert(23int == 23); } }
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

// The lines of the error message, without rustc's indentation,
// and with `(at DIR/fixture.rs:...)` shortened to `(at fixture.rs:...)`
fn error_lines(stderr: &str) -> Vec<String> {
    let start = stderr.find("error: ").unwrap() + "error: ".len();
    let end = stderr.find("\nerror: aborting").unwrap();
    let shorten = |line: &str| match (line.find("(at "), line.find("fixture.rs:")) {
        (Some(at), Some(file)) => format!("{}{}", &line[..at + "(at ".len()], &line[file..]),
        _ => line.to_string(),
    };
    stderr[start..end].trim_end().lines().map(|line| shorten(line.trim())).collect()
}

// Where `text` starts in the fixture, as `fixture.rs:line:column`
fn location(text: &str) -> String {
    let (line, col) =
        CODE.lines().enumerate().find_map(|(i, l)| l.find(text).map(|c| (i + 1, c + 1))).unwrap();
    format!("fixture.rs:{line}:{col}")
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

// A pattern with `::` is matched against the paths from the crate root with one module, too.
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

// With one module too, `a::f` is the path of `f` in module `a`, an exact match,
// so it is not read as a substring of `Data::f` (which fails).
#[test]
fn verify_function_qualified_name_is_not_read_as_a_substring_with_one_module() {
    for pattern in ["a::f", "crate::a::f"] {
        let (output, stdout, stderr) = run_in(&["a"], &[pattern]);
        assert!(output.status.success(), "{pattern}: {}", stderr);
        assert_eq!(stdout, results(1), "{pattern}");
    }

    let (output, stdout, stderr) = run_in(&["a"], &["a::Data::f"]);
    assert!(!output.status.success());
    assert_eq!(stderr.matches("error: assertion failed").count(), 1, "{}", stderr);
    assert!(stdout.contains("0 verified, 1 errors"), "{}", stdout);
}

// `cell::f` is the relative name of the methods `f` of `cell` in `fifth` and `sixth`,
// which wins over the path of `f` in module `cell`, and is ambiguous.
#[test]
fn verify_function_relative_names_win_over_paths_and_are_ambiguous() {
    let (output, stdout, stderr) = run_in(&["cell", "fifth", "sixth"], &["cell::f"]);
    assert!(!output.status.success());
    assert!(!stdout.contains("verified"), "{}", stdout);
    assert_eq!(
        error_lines(&stderr),
        [
            "--verify-function cell::f matches more than one function, use a name that matches only one (e.g. fifth::cell::f),",
            "matched results are:",
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
// so it is listed by that path from the crate root, and matched by it with or without `crate::`,
// by its full name (its name relative to `first`), and by `first::` followed by that path.
#[test]
fn verify_function_names_a_function_by_its_path_from_the_crate_root() {
    let (output, _, stderr) = run_in(&["first", "second"], &["zzz"]);
    assert!(!output.status.success());
    let lines = error_lines(&stderr);
    assert!(lines.contains(&"- second::Item::moved".to_string()), "{}", stderr);
    assert!(!stderr.contains("first::fixture"), "{}", stderr);

    for pattern in [
        "crate::second::Item::moved",
        "second::Item::moved",
        "fixture::second::Item::moved",
        "first::second::Item::moved",
    ] {
        for modules in [&["first", "second"][..], &["first"][..]] {
            let (output, stdout, stderr) = run_in(modules, &[pattern]);
            assert!(output.status.success(), "{pattern}: {}", stderr);
            assert_eq!(stdout, results(1), "{pattern}");
        }
    }
}

// `line::f` is the name of the method `f` of `line::line` relative to module `line`,
// and the path of `f` in module `line`: the relative name wins, with one module or several.
#[test]
fn verify_function_relative_name_wins_over_a_path() {
    for modules in [&["line", "first"][..], &["line"][..]] {
        // The method is the one function selected by both patterns
        let (output, stdout, stderr) = run_in(modules, &["line::f", "line::line::f"]);
        assert!(output.status.success(), "{}", stderr);
        assert_eq!(stdout, results(1));
        let (output, stdout, stderr) = run_in(modules, &["line::f", "crate::line::f"]);
        assert!(output.status.success(), "{}", stderr);
        assert_eq!(stdout, results(2));
        for pattern in ["crate::line::f", "line::line::f"] {
            let (output, stdout, stderr) = run_in(modules, &[pattern]);
            assert!(output.status.success(), "{pattern}: {}", stderr);
            assert_eq!(stdout, results(1), "{pattern}");
        }
    }
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

// `G<u8>::g` and `G<u16>::g` are both named `G::g` in `ninth`, and both selected by it,
// however the module is written and whichever other modules are selected.
#[test]
fn verify_function_functions_with_the_same_name() {
    for modules in [&["ninth"][..], &["ninth", "first"][..]] {
        for pattern in ["G::g", "ninth::G::g", "crate::ninth::G::g"] {
            let (output, stdout, stderr) = run_in(modules, &[pattern]);
            assert!(output.status.success(), "{pattern}: {}", stderr);
            assert_eq!(stdout, results(2), "{pattern}");
        }
    }
}

// `ta` and `tb` each have a method `f` of `crate::S`, so `S::f` is ambiguous with both,
// and they are told apart by their modules. The listing shows where each is defined.
#[test]
fn verify_function_impls_of_one_type_in_two_modules() {
    let (output, stdout, stderr) = run_in(&["ta", "tb"], &["S::f"]);
    assert!(!output.status.success());
    assert!(!stdout.contains("verified"), "{}", stdout);
    assert_eq!(
        error_lines(&stderr),
        [
            "--verify-function S::f matches more than one function, use a name that matches only one (e.g. ta::S::f),".to_string(),
            "matched results are:".to_string(),
            format!("- S::f (at {})", location("fn f() { assert(19int")),
            format!("- S::f (at {})", location("fn f() { assert(20int")),
        ]
    );
    for pattern in ["ta::S::f", "crate::ta::S::f"] {
        let (output, stdout, stderr) = run_in(&["ta", "tb"], &[pattern]);
        assert!(output.status.success(), "{pattern}: {}", stderr);
        assert_eq!(stdout, results(1), "{pattern}");
        assert_eq!(stderr.matches("note: verifying module tb").count(), 0, "{}", stderr);
    }
}

// `eleventh` has two methods `g` of `crate::ninth::G` too, so no name selects one function of
// `ninth::G::g`, and the hint names the functions of one module, which the same rule selects.
#[test]
fn verify_function_same_names_in_two_modules() {
    let modules = ["ninth", "eleventh"];
    let (output, _, stderr) = run_in(&modules, &["ninth::G::g"]);
    assert!(!output.status.success());
    let listed = ["17int", "18int", "21int", "22int"]
        .map(|n| format!("- ninth::G::g (at {})", location(&format!("fn g() {{ assert({n}"))));
    let mut expected = vec![
        "--verify-function ninth::G::g matches functions in more than one module, use a name that matches the functions of only one module (e.g. eleventh::ninth::G::g),".to_string(),
        "matched results are:".to_string(),
    ];
    expected.extend(listed);
    assert_eq!(error_lines(&stderr), expected);

    let (output, stdout, stderr) = run_in(&modules, &["eleventh::ninth::G::g"]);
    assert!(output.status.success(), "{}", stderr);
    assert_eq!(stdout, results(2));
    assert_eq!(stderr.matches("note: verifying module ninth").count(), 0, "{}", stderr);
}

// A method of an impl for a type of another crate has no path from the crate root,
// but its module's path followed by its full name names it.
#[test]
fn verify_function_method_of_a_type_of_another_crate() {
    let (output, _, stderr) = run_in(&["twelfth", "first"], &["zzz"]);
    assert!(!output.status.success());
    let lines = error_lines(&stderr);
    assert!(lines.contains(&"- twelfth::vstd::seq::Seq::tw".to_string()), "{}", stderr);

    for modules in [&["twelfth", "first"][..], &["twelfth"][..]] {
        for pattern in ["twelfth::vstd::seq::Seq::tw", "crate::twelfth::vstd::seq::Seq::tw"] {
            let (output, stdout, stderr) = run_in(modules, &[pattern]);
            assert!(output.status.success(), "{pattern}: {}", stderr);
            assert_eq!(stdout, results(1), "{pattern}");
        }
    }
}

#[test]
fn verify_function_repeated_bad_pattern_reports_once() {
    let (_, _, single_stderr) = run(&["delta"]);
    let (output, _, stderr) = run(&["delta", "alpha", "delta"]);
    assert!(!output.status.success());
    assert_eq!(stderr, single_stderr);
}
