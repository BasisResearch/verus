#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;
use verus_reach::{Graph, Node, Report, Roots};

/// Runs verus with `--reach` and returns the crate's report.
fn reach(name: &str, code: String) -> (Result<TestErr, TestErr>, Report) {
    let dir = std::env::temp_dir().join(format!("verus-reach-{name}"));
    let _ = std::fs::remove_dir_all(&dir);
    let reach_opt = format!("--reach {}", dir.display());
    let result = verify_one_file(name, code, &[&reach_opt]);
    let mut reports = verus_reach::load(&[dir]).unwrap();
    assert_eq!(reports.len(), 1);
    (result, reports.remove(0))
}

fn node<'a>(report: &'a Report, def_path: &str) -> &'a Node {
    report
        .nodes
        .iter()
        .find(|n| n.def_path == def_path)
        .unwrap_or_else(|| panic!("no function {} in {:#?}", def_path, report))
}

fn has_edge(report: &Report, from: &str, to: &str) -> bool {
    report.edges.iter().any(|(f, t)| f == from && t == to)
}

fn graph(report: &Report, exclude: &[&str]) -> Graph {
    let roots = Roots {
        add: vec![],
        exclude: exclude.iter().map(|g| glob::Pattern::new(g).unwrap()).collect(),
    };
    Graph::new(std::slice::from_ref(report), &roots)
}

fn twin_code() -> String {
    verus_code! {
    mod verified {
        use verus_builtin::*;

        pub fn inc(x: u64) -> (r: u64)
            requires x < 100,
            ensures r == x + 1,
        {
            x + 1
        }
    }

    #[verifier::external]
    fn inc(x: u64) -> u64 {
        x + 1
    }

    #[verifier::external]
    fn main() {
        let _ = inc(1);
    }
    }
}

#[test]
fn twin() {
    let (result, report) = reach("twin", twin_code());
    result.unwrap();
    assert_eq!(report.krate, "test_crate");
    assert_eq!(report.main.as_deref(), Some("test_crate::main"));
    let twin = node(&report, "test_crate::verified::inc");
    assert!(twin.verified);
    assert_eq!(twin.mode, "exec");
    assert!(!node(&report, "test_crate::inc").verified);
    assert!(has_edge(&report, "test_crate::main", "test_crate::inc"));

    let graph = graph(&report, &[]);
    assert_eq!(graph.roots, vec!["test_crate::main"]);
    assert!(!graph.is_reachable(twin));
    assert!(graph.is_reachable(node(&report, "test_crate::inc")));
}

#[test]
fn wired() {
    let code = verus_code! {
        mod verified {
            use verus_builtin::*;

            pub fn inc(x: u64) -> (r: u64)
                requires x < 100,
                ensures r == x + 1,
            {
                x + 1
            }
        }

        fn main() {
            let _ = verified::inc(1);
        }
    };
    let (result, report) = reach("wired", code);
    result.unwrap();
    assert!(graph(&report, &[]).is_reachable(node(&report, "test_crate::verified::inc")));
}

#[test]
fn trait_dispatch() {
    let code = verus_code! {
        trait Step {
            fn step(&self) -> u64;
        }

        struct S;

        impl Step for S {
            fn step(&self) -> u64 {
                1
            }
        }

        fn run<T: Step>(t: &T) -> u64 {
            t.step()
        }

        fn main() {
            let _ = run(&S);
        }
    };
    let (result, report) = reach("trait_dispatch", code);
    result.unwrap();
    // The call names the trait method; the impl is reached through the dispatch edge
    assert!(has_edge(&report, "test_crate::run", "test_crate::Step::step"));
    assert!(has_edge(&report, "test_crate::Step::step", "test_crate::impl&%0::step"));
    assert!(graph(&report, &[]).is_reachable(node(&report, "test_crate::S::step")));
}

#[test]
fn trait_impl_called_by_upstream() {
    let code = verus_code! {
        struct S;

        fn helper() -> u64 {
            1
        }

        #[verifier::external]
        impl core::fmt::Display for S {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                let _ = helper();
                write!(f, "S")
            }
        }

        #[verifier::external]
        fn main() {
            let _ = S.to_string();
        }
    };
    let (result, report) = reach("trait_impl_called_by_upstream", code);
    result.unwrap();
    // Using the type reaches its trait impls, which upstream code may call
    assert!(has_edge(&report, "test_crate::main", "test_crate::S"));
    assert!(has_edge(&report, "test_crate::S", "test_crate::impl&%0::fmt"));
    assert!(graph(&report, &[]).is_reachable(node(&report, "test_crate::helper")));
}

#[test]
fn closures_belong_to_the_enclosing_function() {
    let code = verus_code! {
        fn helper() -> u64 {
            1
        }

        #[verifier::external]
        fn main() {
            let f = || helper();
            let _ = f();
        }
    };
    let (result, report) = reach("closures", code);
    result.unwrap();
    assert!(has_edge(&report, "test_crate::main", "test_crate::helper"));
}

/// A library without `main`: exported functions are the roots.
#[test]
fn exported_roots() {
    let code = verus_code! {
        pub mod verified {
            use verus_builtin::*;

            pub fn inc(x: u64) -> (r: u64)
                requires x < 100,
                ensures r == x + 1,
            {
                x + 1
            }
        }

        #[verifier::external]
        pub fn inc(x: u64) -> u64 {
            x + 1
        }
    };
    let (result, report) = reach("exported_roots", code);
    result.unwrap();
    assert_eq!(report.main, None);
    assert!(node(&report, "test_crate::verified::inc").exported);

    let all = graph(&report, &[]);
    assert_eq!(all.roots, vec!["test_crate::inc", "test_crate::verified::inc"]);
    assert!(all.is_reachable(node(&report, "test_crate::verified::inc")));

    let excluded = graph(&report, &["test_crate::verified::*"]);
    assert_eq!(excluded.roots, vec!["test_crate::inc"]);
    assert!(!excluded.is_reachable(node(&report, "test_crate::verified::inc")));
}

#[test]
fn proxies() {
    let code = verus_code! {
        #[verifier::external]
        fn ext(x: u64) -> u64 {
            x
        }

        assume_specification [ext](x: u64) -> (r: u64)
            ensures r == x;

        fn main() {
            let _ = ext(1);
        }
    };
    let (result, report) = reach("proxies", code);
    result.unwrap();
    let proxies: Vec<&Node> = report.nodes.iter().filter(|n| n.proxy).collect();
    assert_eq!(proxies.len(), 1, "{:#?}", report);
    assert!(proxies[0].verified);
    assert!(!proxies[0].is_verified_exec());
    let ext = node(&report, "test_crate::ext");
    assert!(ext.verified);
    assert!(ext.external_body);
    assert!(!ext.is_verified_exec());
}

/// A library crate and a binary crate: the binary's `main` is the root, and
/// only the library functions it calls are reachable.
#[test]
fn lib_and_bin() {
    let current_exe = std::env::current_exe().unwrap();
    let fixture = current_exe
        .ancestors()
        .nth(4)
        .unwrap()
        .join("rust_verify_test/tests/cargo-tests/verified/reach_lib_bin");
    let target_dir = tempfile::tempdir().unwrap();
    let reach_dir = tempfile::tempdir().unwrap();
    let reach_arg = reach_dir.path().to_str().unwrap();
    let args = ["verify", "--fwd-verus-args-to", "roots", "--", "--reach", reach_arg];
    let run = run_cargo_verus_with_target(&args, &fixture, target_dir.path());
    assert!(run.status.success());

    let reports = verus_reach::load(&[reach_dir.path().to_path_buf()]).unwrap();
    let mut names: Vec<String> = reports.iter().map(|r| r.file_name()).collect();
    names.sort();
    assert_eq!(names, vec!["reach_lib_bin.bin.json", "reach_lib_bin.lib.json"]);

    let graph = Graph::new(&reports, &Roots::default());
    assert_eq!(graph.roots, vec!["reach_lib_bin::main"]);
    let lib = |name: &str| graph.nodes.values().find(|n| n.def_path == name).unwrap();
    assert!(graph.is_reachable(lib("reach_lib_bin::double")));
    assert!(graph.is_reachable(lib("reach_lib_bin::Counter::bump")));
    assert!(!graph.is_reachable(lib("reach_lib_bin::twin::double")));
}
