#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;
use verus_reach::{EdgeKind, Graph, Node, Report, Roots};

/// Runs verus with `--reach` and returns the crate's report.
fn reach(name: &str, code: String) -> (Result<TestErr, TestErr>, Report) {
    let dir = tempfile::tempdir().unwrap();
    let reach_opt = format!("--reach {}", dir.path().display());
    let result = verify_one_file(name, code, &[&reach_opt]);
    let mut reports = verus_reach::load(&[dir.path().to_path_buf()]).unwrap();
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
    report.edges.iter().any(|e| e.from == from && e.to == to)
}

fn edge_kinds(report: &Report, from: &str, to: &str) -> Vec<EdgeKind> {
    let mut kinds: Vec<EdgeKind> =
        report.edges.iter().filter(|e| e.from == from && e.to == to).map(|e| e.kind).collect();
    kinds.sort();
    kinds
}

/// The test crate is a library, so `main` is not an entry point; make it the root.
fn graph_from_main(report: &Report) -> Graph {
    let roots = Roots { add: vec!["test_crate::main".into()], exclude: vec![] };
    Graph::new(std::slice::from_ref(report), &roots).unwrap()
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
    assert_eq!(report.crate_type, "lib");
    assert_eq!(report.main, None);
    let twin = node(&report, "test_crate::verified::inc");
    assert!(twin.verified);
    assert_eq!(twin.mode, "exec");
    assert_eq!(twin.module, "test_crate::verified");
    assert!(twin.span.end_line >= twin.span.start_line + 5, "{:?}", twin.span);
    assert!(!node(&report, "test_crate::inc").verified);
    assert!(has_edge(&report, "test_crate::main", "test_crate::inc"));

    let graph = graph_from_main(&report);
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
    assert!(graph_from_main(&report).is_reachable(node(&report, "test_crate::verified::inc")));
}

/// A `when_used_as_spec` function mentioned only in ghost code is not
/// called, but the spec it stands for is used.
#[test]
fn ghost_code_does_not_call() {
    let code = verus_code! {
        spec fn spec_inc(x: u64) -> u64 {
            (x + 1) as u64
        }

        #[verifier::when_used_as_spec(spec_inc)]
        fn inc(x: u64) -> (r: u64)
            requires x < 100,
            ensures r == spec_inc(x),
        {
            x + 1
        }

        fn main()
            requires inc(1) == 2,
        {
            assert(inc(1) == 2);
            proof {
                let _ = inc(2);
            }
        }
    };
    let (result, report) = reach("ghost", code);
    result.unwrap();
    assert_eq!(
        edge_kinds(&report, "test_crate::main", "test_crate::inc"),
        vec![EdgeKind::Contract, EdgeKind::Proof]
    );
    assert_eq!(
        edge_kinds(&report, "test_crate::inc", "test_crate::spec_inc"),
        vec![EdgeKind::Contract]
    );
    let graph = graph_from_main(&report);
    assert!(!graph.is_reachable(node(&report, "test_crate::inc")));
    assert!(graph.is_reachable(node(&report, "test_crate::spec_inc")));
    assert!(!graph.reachable.contains("test_crate::spec_inc"));
}

/// Ghost functions are used through the contracts and proofs of reachable
/// code: directly, through other specs, and through the lemmas a proof
/// calls.
#[test]
fn dead_ghost_functions() {
    let code = verus_code! {
        spec fn small(x: u64) -> bool {
            x < 100
        }

        spec fn bounded(x: u64) -> bool {
            small(x) && x > 0
        }

        spec fn by_lemma(x: u64) -> bool {
            x < 200
        }

        proof fn lemma(x: u64)
            requires bounded(x),
            ensures by_lemma(x),
        {
        }

        spec fn dead(x: u64) -> bool {
            x > 1
        }

        spec fn only_by_twin(x: u64) -> bool {
            x > 2
        }

        fn twin(x: u64)
            requires only_by_twin(x), dead(x),
        {
        }

        fn main(x: u64)
            requires bounded(x),
        {
            proof {
                lemma(x);
            }
        }
    };
    let (result, report) = reach("dead_ghost_functions", code);
    result.unwrap();
    assert_eq!(
        edge_kinds(&report, "test_crate::main", "test_crate::bounded"),
        vec![EdgeKind::Contract]
    );
    assert_eq!(edge_kinds(&report, "test_crate::main", "test_crate::lemma"), vec![EdgeKind::Proof]);
    assert_eq!(
        edge_kinds(&report, "test_crate::bounded", "test_crate::small"),
        vec![EdgeKind::Call]
    );

    let graph = graph_from_main(&report);
    let ghost = |name: &str| node(&report, &format!("test_crate::{name}"));
    for name in ["bounded", "small", "by_lemma", "lemma"] {
        assert!(graph.is_reachable(ghost(name)), "{}", name);
        assert!(!graph.reachable.contains(&ghost(name).id), "{} runs", name);
    }
    for name in ["dead", "only_by_twin", "twin"] {
        assert!(!graph.is_reachable(ghost(name)), "{}", name);
    }
    assert_eq!(graph.ghost_coverage(), (4, 6));
}

/// The spec accessors `verus!` synthesizes for enum fields are not the
/// user's specs.
#[test]
fn synthesized_enum_accessors_are_not_reported() {
    let code = verus_code! {
        enum E {
            A { n: u64 },
            B(u64),
        }

        spec fn n_of(e: E) -> u64 {
            e->A_n
        }

        impl E {
            spec fn is_a(self) -> bool {
                self is A
            }
        }

        fn main() {
            let _ = E::B(1);
        }
    };
    let (result, report) = reach("enum_accessors", code);
    result.unwrap();
    let specs: Vec<&str> =
        report.nodes.iter().filter(|n| n.is_ghost()).map(|n| n.def_path.as_str()).collect();
    assert_eq!(specs, vec!["test_crate::E::is_a", "test_crate::n_of"]);
}

/// A type invariant is used wherever its type is.
#[test]
fn type_invariant_is_used_with_its_type() {
    let code = verus_code! {
        struct S {
            n: u64,
        }

        #[verifier::type_invariant]
        spec fn inv(s: S) -> bool {
            s.n < 10
        }

        fn main() {
            let s = S { n: 1 };
        }
    };
    let (result, report) = reach("type_invariant", code);
    result.unwrap();
    assert_eq!(edge_kinds(&report, "test_crate::S", "test_crate::inv"), vec![EdgeKind::Contract]);
    assert!(graph_from_main(&report).is_reachable(node(&report, "test_crate::inv")));
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
    assert!(graph_from_main(&report).is_reachable(node(&report, "test_crate::S::step")));
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
    assert!(graph_from_main(&report).is_reachable(node(&report, "test_crate::helper")));
}

/// The type is only ever named as `Self`, and only constructed inside a
/// trait impl reached through dispatch.
#[test]
fn type_used_through_self() {
    let code = verus_code! {
        struct S {
            n: u64,
        }

        fn helper() -> u64 {
            1
        }

        #[verifier::external]
        impl Default for S {
            fn default() -> Self {
                Self { n: 0 }
            }
        }

        #[verifier::external]
        impl core::fmt::Display for S {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                let _ = helper();
                write!(f, "{}", self.n)
            }
        }

        #[verifier::external]
        fn main() {
            let _ = S::default().to_string();
        }
    };
    let (result, report) = reach("type_used_through_self", code);
    result.unwrap();
    assert!(graph_from_main(&report).is_reachable(node(&report, "test_crate::helper")));
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
    assert!(node(&report, "test_crate::verified::inc").exported);

    let all = Graph::new(std::slice::from_ref(&report), &Roots::default()).unwrap();
    assert_eq!(all.roots, vec!["test_crate::inc", "test_crate::verified::inc"]);
    assert!(all.is_reachable(node(&report, "test_crate::verified::inc")));

    let roots = Roots {
        add: vec![],
        exclude: vec![glob::Pattern::new("test_crate::verified::*").unwrap()],
    };
    let excluded = Graph::new(std::slice::from_ref(&report), &roots).unwrap();
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
    assert!(run.status.success(), "{}", String::from_utf8_lossy(&run.stderr));

    let reports = verus_reach::load(&[reach_dir.path().to_path_buf()]).unwrap();
    let mut names: Vec<String> = reports.iter().map(|r| r.file_name()).collect();
    names.sort();
    assert_eq!(names, vec!["reach_lib_bin.bin.json", "reach_lib_bin.lib.json"]);

    let graph = Graph::new(&reports, &Roots::default()).unwrap();
    assert_eq!(graph.roots, vec!["reach_lib_bin(bin)::main"]);
    let by_id = |id: &str| &graph.nodes[id];
    assert!(graph.is_reachable(by_id("reach_lib_bin::double")));
    assert!(graph.is_reachable(by_id("reach_lib_bin::impl&%0::bump")));
    assert!(graph.is_reachable(by_id("reach_lib_bin(bin)::helper")));
    assert!(!graph.is_reachable(by_id("reach_lib_bin::helper")));
    assert!(!graph.is_reachable(by_id("reach_lib_bin::twin::double")));
}
