#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

/// Runs verus with `--reach` and returns the parsed report.
fn reach(
    name: &str,
    code: String,
    extra: &[&str],
) -> (Result<TestErr, TestErr>, serde_json::Value) {
    let path = std::env::temp_dir().join(format!("verus-reach-{name}.json"));
    let reach_opt = format!("--reach {}", path.display());
    let mut options: Vec<&str> = vec![&reach_opt];
    options.extend_from_slice(extra);
    let result = verify_one_file(name, code, &options);
    let report = serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
    (result, report)
}

fn function<'a>(report: &'a serde_json::Value, def_path: &str) -> &'a serde_json::Value {
    report["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f["def_path"] == def_path)
        .unwrap_or_else(|| panic!("no function {} in {:#}", def_path, report))
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
    let (result, report) = reach("twin", twin_code(), &[]);
    result.unwrap();
    assert_eq!(report["roots"], serde_json::json!(["test_crate::main"]));
    let twin = function(&report, "test_crate::verified::inc");
    assert_eq!(twin["verified"], true);
    assert_eq!(twin["mode"], "exec");
    assert_eq!(twin["reachable"], false);
    let original = function(&report, "test_crate::inc");
    assert_eq!(original["verified"], false);
    assert_eq!(original["reachable"], true);
    let main = function(&report, "test_crate::main");
    assert_eq!(main["verified"], false);
    assert_eq!(main["reachable"], true);
}

#[test]
fn twin_fail_under() {
    let (result, _) = reach("twin_fail_under", twin_code(), &["--reach-fail-under 50"]);
    let err = result.unwrap_err();
    assert!(err.errors.iter().any(|e| e.message.contains("below --reach-fail-under")), "{err:?}");
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
    let (result, report) = reach("wired", code, &["--reach-fail-under 100"]);
    result.unwrap();
    assert_eq!(function(&report, "test_crate::verified::inc")["reachable"], true);
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
    let (result, report) = reach("trait_dispatch", code, &[]);
    result.unwrap();
    assert_eq!(function(&report, "test_crate::S::step")["reachable"], true);
}

fn lib_pub_twin_code() -> String {
    verus_code! {
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

    #[verifier::external]
    fn main() {
        let _ = inc(1);
    }
    }
}

#[test]
fn lib_pub_twin() {
    let (result, report) = reach("lib_pub_twin", lib_pub_twin_code(), &[]);
    result.unwrap();
    assert_eq!(
        report["roots"],
        serde_json::json!(["test_crate::inc", "test_crate::main", "test_crate::verified::inc"])
    );
    assert_eq!(function(&report, "test_crate::verified::inc")["reachable"], true);
}

#[test]
fn lib_pub_twin_roots_exclude() {
    let (result, report) = reach(
        "lib_pub_twin_roots_exclude",
        lib_pub_twin_code(),
        &["--reach-roots-exclude test_crate::verified::*"],
    );
    result.unwrap();
    assert_eq!(report["roots"], serde_json::json!(["test_crate::inc", "test_crate::main"]));
    assert_eq!(function(&report, "test_crate::verified::inc")["reachable"], false);
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
    let (result, report) = reach("proxies", code, &["--reach-fail-under 100"]);
    result.unwrap();
    let proxies: Vec<_> =
        report["functions"].as_array().unwrap().iter().filter(|f| f["proxy"] == true).collect();
    assert_eq!(proxies.len(), 1, "{report:#}");
    assert_eq!(proxies[0]["verified"], true);
    assert_eq!(proxies[0]["reachable"], false);
    let ext = function(&report, "test_crate::ext");
    assert_eq!(ext["verified"], true);
    assert_eq!(ext["external_body"], true);
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
    let (result, report) = reach("trait_impl_called_by_upstream", code, &[]);
    result.unwrap();
    assert_eq!(function(&report, "test_crate::helper")["reachable"], true);
}
