//! Build-wide constants shared by `rust_verify` and `vargo` (included by
//! `#[path]`).
//!
//! The solver pins come from `tools/common/solvers.toml`, embedded at compile
//! time; see that file for who else reads it. Nothing solver-related is
//! spelled out here so the manifest stays the only place a pin lives.
//!
//! This file is formatted under two rustfmt configurations (the `source`
//! workspace's and vargo's), so expressions are kept short enough that both
//! agree on them.
#![allow(dead_code)]

pub const VERUS_GITHUB_BUG_REPORT_URL: &str =
    "https://github.com/verus-lang/verus/issues/new?template=bug_report.md";

/// The solver pin manifest, verbatim.
pub const SOLVERS_MANIFEST: &str = include_str!("solvers.toml");

/// The solvers the manifest pins, in manifest order.
pub const SOLVERS: [&str; 2] = ["z3", "cvc5"];

/// The version string a running z3 must report.
pub fn expected_z3_version() -> &'static str {
    solver_pin("z3", "version").expect("solvers.toml pins a z3 version")
}

/// The version string a running cvc5 must report.
pub fn expected_cvc5_version() -> &'static str {
    solver_pin("cvc5", "version").expect("solvers.toml pins a cvc5 version")
}

/// One value from the manifest: `[solver]` table, `key = "value"` line.
pub fn solver_pin(solver: &str, key: &str) -> Option<&'static str> {
    let pins = solver_pins(solver);
    let found = pins.into_iter().find(|(k, _)| *k == key);
    found.map(|(_, v)| v)
}

/// Every `key = "value"` pair of the manifest's `[solver]` table, in order.
pub fn solver_pins(solver: &str) -> Vec<(&'static str, &'static str)> {
    parse_pins(SOLVERS_MANIFEST, solver)
}

/// The manifest reader: `[table]` headers and `key = "value"` lines, `#`
/// comments, nothing else — the format is kept this small on purpose.
fn parse_pins<'a>(manifest: &'a str, solver: &str) -> Vec<(&'a str, &'a str)> {
    let mut pins = Vec::new();
    let mut in_table = false;
    for line in manifest.lines().map(str::trim) {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(header) = table_header(line) {
            in_table = header == solver;
            continue;
        }
        if !in_table {
            continue;
        }
        if let Some(pin) = key_value(line) {
            pins.push(pin);
        }
    }
    pins
}

/// `[name]` → `name`.
fn table_header(line: &str) -> Option<&str> {
    let inner = line.strip_prefix('[')?.strip_suffix(']')?;
    Some(inner.trim())
}

/// `key = "value" # comment` → `(key, value)`.
fn key_value(line: &str) -> Option<(&str, &str)> {
    let (key, rest) = line.split_once('=')?;
    let quoted = rest.trim().strip_prefix('"')?;
    let (value, _) = quoted.split_once('"')?;
    Some((key.trim(), value))
}

#[cfg(test)]
mod tests {
    use super::*;

    const PIN_KEYS: [&str; 7] = [
        "version",
        "repo",
        "tag",
        "asset_arm64_macos",
        "sha256_arm64_macos",
        "asset_x86_linux",
        "sha256_x86_linux",
    ];

    #[test]
    fn manifest_pins_every_solver_completely() {
        for solver in SOLVERS {
            for key in PIN_KEYS {
                let value = solver_pin(solver, key);
                let value = value.unwrap_or_else(|| panic!("[{solver}] lacks {key}"));
                assert!(!value.is_empty(), "[{solver}] {key} is empty");
                if key.starts_with("sha256") {
                    assert_eq!(value.len(), 64, "[{solver}] {key} is not a sha256");
                    let lower_hex = |b: u8| b.is_ascii_hexdigit() && !b.is_ascii_uppercase();
                    assert!(value.bytes().all(lower_hex), "[{solver}] {key}");
                }
            }
        }
        let z3 = solver_pin("z3", "version").unwrap();
        let cvc5 = solver_pin("cvc5", "version").unwrap();
        assert_eq!(expected_z3_version(), z3);
        assert_eq!(expected_cvc5_version(), cvc5);
    }

    #[test]
    fn reader_scopes_keys_to_their_table_and_ignores_comments() {
        let manifest = r#"
            # leading comment
            [a]
            version = "1" # trailing comment
            tag = "t-a"
            [b]
            version = "2"
            junk line without equals
            unquoted = 3
        "#;
        let a = parse_pins(manifest, "a");
        assert_eq!(a, vec![("version", "1"), ("tag", "t-a")]);
        assert_eq!(parse_pins(manifest, "b"), vec![("version", "2")]);
        assert!(parse_pins(manifest, "c").is_empty());
    }
}
