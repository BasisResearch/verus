//! The one authorization gate shared by every Verus entry point (`verus`,
//! `rust_verify`, `cargo-verus`), included by `#[path]` so each binary
//! compiles exactly this logic.
//!
//! These binaries are meant to be driven by the Verus MCP server, not run by
//! hand. An invocation is authorized in either of two equivalent ways:
//!
//! * `--mcp` on the command line, or
//! * `VERUS_MCP_ENABLED` set (to anything but `0`/`false`/`no`/`off`/empty) in
//!   the environment — the MCP server exports this for every subprocess, so
//!   a `cargo-verus` → `verus` → `rust_verify` chain is authorized once.
//!
//! Callers see a single `bool`; which of the two routes authorized the run
//! is not observable past this module.
#![allow(dead_code)]

/// The command-line route.
pub const FLAG: &str = "--mcp";
/// The environment route.
pub const ENV_VAR: &str = "VERUS_MCP_ENABLED";

/// Whether `VERUS_MCP_ENABLED` in the current environment authorizes this run.
pub fn env_enabled() -> bool {
    env_value_enables(std::env::var(ENV_VAR).ok().as_deref())
}

/// Whether a `VERUS_MCP_ENABLED` value is truthy (anything but `0`, `false`, `no`, `off`, empty).
pub fn env_value_enables(value: Option<&str>) -> bool {
    match value {
        None => false,
        Some(v) => {
            !matches!(v.trim().to_ascii_lowercase().as_str(), "" | "0" | "false" | "no" | "off")
        }
    }
}

/// Strip every `--mcp` from `args` and report whether the invocation is
/// authorized, by the flag or by the environment.
pub fn consume(args: impl IntoIterator<Item = String>) -> (bool, Vec<String>) {
    consume_with(args, env_enabled())
}

/// [`consume`] with the environment's verdict supplied by the caller.
pub fn consume_with(
    args: impl IntoIterator<Item = String>,
    env_authorizes: bool,
) -> (bool, Vec<String>) {
    let mut flag = false;
    let args = args
        .into_iter()
        .filter(|arg| {
            if arg == FLAG {
                flag = true;
                false
            } else {
                true
            }
        })
        .collect();
    (flag || env_authorizes, args)
}

/// The refusal printed when neither route authorized the run.
pub fn refusal(binary: &str) -> String {
    format!(
        "{binary} is only meant to be invoked by the MCP server, not directly from bash; \
         use the `verus` MCP server's tools instead (or pass {FLAG}, or set {ENV_VAR}=1, \
         if you really are the MCP server)"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(list: &[&str]) -> Vec<String> {
        list.iter().map(|s| s.to_string()).collect()
    }

    #[test]
    fn flag_authorizes_and_is_removed_wherever_it_appears() {
        let (authorized, rest) =
            consume_with(args(&["rust_verify", "--mcp", "input.rs", "--mcp"]), false);
        assert!(authorized);
        assert_eq!(rest, args(&["rust_verify", "input.rs"]));
    }

    #[test]
    fn environment_authorizes_without_the_flag() {
        let (authorized, rest) = consume_with(args(&["rust_verify", "input.rs"]), true);
        assert!(authorized);
        assert_eq!(rest, args(&["rust_verify", "input.rs"]));
    }

    #[test]
    fn neither_route_means_refused() {
        let (authorized, rest) = consume_with(args(&["rust_verify", "input.rs"]), false);
        assert!(!authorized);
        assert_eq!(rest, args(&["rust_verify", "input.rs"]));
    }

    #[test]
    fn env_values() {
        for on in ["1", "true", "YES", " on ", "anything"] {
            assert!(env_value_enables(Some(on)), "{on:?} should enable");
        }
        for off in ["", "0", "false", "No", "OFF", "  "] {
            assert!(!env_value_enables(Some(off)), "{off:?} should not enable");
        }
        assert!(!env_value_enables(None));
    }

    #[test]
    fn refusal_names_both_routes() {
        let msg = refusal("cargo-verus");
        assert!(msg.starts_with("cargo-verus is only meant"));
        assert!(msg.contains(FLAG) && msg.contains(ENV_VAR));
    }
}
