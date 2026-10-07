#![feature(rustc_private)]

use std::fs;
use std::process::Command;

// Attribute expansion allocates the first module's definition ID after the
// second module's. Enumerating definition IDs reverses their SMT declarations.
// Keep the upstream HIR order instead: bounded SMT search depends on it.
#[test]
fn attributed_sibling_keeps_its_source_order_in_smt() {
    let dir = tempfile::tempdir().unwrap();
    let input = dir.path().join("fixture.rs");
    fs::write(
        &input,
        r#"
use vstd::prelude::*;
#[verus::trusted]
mod first {
    use vstd::prelude::*;
    verus! { pub open spec fn value() -> int { 1 } }
}
mod second {
    use vstd::prelude::*;
    verus! { pub open spec fn value() -> int { 2 } }
}
verus! { proof fn check() { assert(first::value() + second::value() == 3); } }
"#,
    )
    .unwrap();
    let current = std::env::current_exe().unwrap();
    let binary = current.parent().unwrap().parent().unwrap().join("rust_verify");
    let logs = dir.path().join("logs");
    let output = Command::new(binary)
        .args(["--mcp", "--crate-type=lib", "--verify-root", "-V", "no-solver-version-check"])
        .arg(&input)
        .args(["--log", "smt", "--log-dir"])
        .arg(&logs)
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
    let smt = fs::read_dir(&logs)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "smt2"))
        .map(|path| fs::read_to_string(path).unwrap())
        .find(|text| {
            text.contains("fuel%fixture!first.value.")
                && text.contains("fuel%fixture!second.value.")
        })
        .expect("root query must contain both spec functions");
    let first = smt.find("(declare-const fuel%fixture!first.value.").unwrap();
    let second = smt.find("(declare-const fuel%fixture!second.value.").unwrap();
    assert!(first < second, "attribute expansion changed sibling fuel declaration order");
}
