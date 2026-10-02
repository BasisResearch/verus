#![allow(dead_code)]
pub const Z3_VERSION: &str = "4.16.0";
/// The cvc5 `source/tools/get-cvc5.sh` downloads: the Basis fork
/// (BasisResearch/cvc5, release `basis-6c96b55f6c`), which answers the
/// `get-info` keys the failure diagnostics read. Recorded in the toolchain
/// manifest; not checked against the cvc5 in use, which may be any.
pub const CVC5_VERSION: &str = "1.3.5.dev+main@6c96b55";
pub const SINGULAR_VERSION: &str = "4.3.2";
