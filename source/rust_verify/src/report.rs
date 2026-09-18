//! The machine report: one self-describing JSON artifact per crate.
//!
//! `--output-json` prints its report onto stdout, interleaved with whatever
//! else the run writes there. Under cargo that stream also carries cargo's
//! own JSON messages, so a consumer has to find the report in the stream,
//! decide which crate it belongs to, and know its shape in advance — none of
//! which the report tells it. `--report-json PATH` writes the same
//! verification data to a file of its own, tagged with a schema version and
//! the crate it describes, and adds the diagnostics Verus raised, resolved to
//! source coordinates and attributed to the function whose obligation raised
//! them.
//!
//! The point of the attribution is that Verus knows it. A consumer that only
//! sees rendered rustc diagnostics has to recover the function by matching
//! spans against its own index of the source, which is a guess at something
//! that was exact a moment earlier.
//!
//! Nothing here changes `--output-json`. Its consumers — `tools/verita`,
//! `verus/src/record.rs`, and the metrics scripts in the verified projects —
//! keep the report they already parse.

use std::collections::BTreeMap;
use std::path::Path;

use serde::{Deserialize, Serialize};

/// Bumped when a field changes meaning or disappears; adding one does not
/// bump it. A consumer that does not recognise the version should say so
/// rather than guess.
pub const SCHEMA_VERSION: u32 = 1;

/// A source range, resolved by the compiler session that produced it.
///
/// Lines and columns are one-based and the end is exclusive, which is how
/// Verus's own diagnostics read. `text` is the source the range covers when
/// the file was readable.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceSpan {
    pub file: String,
    pub line: usize,
    pub col: usize,
    pub end_line: usize,
    pub end_col: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub text: Option<String>,
}

/// One of a diagnostic's secondary spans, with the note attached to it.
///
/// `span` is null when the label's span could not be resolved against this
/// session's source map, which happens for spans imported from another
/// crate. A null span is not the same as a span at the origin.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Label {
    pub span: Option<SourceSpan>,
    pub note: String,
    /// Written by the user as `#[verifier::proof_note(..)]`.
    pub is_proof_note: bool,
    /// Written by the user as `#[verifier::custom_err(..)]`; replaces the
    /// rendered message rather than adding to it.
    pub is_custom_err: bool,
}

/// One diagnostic as Verus raised it, before rustc rendered it.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Diagnostic {
    /// `error`, `warning` or `note`, as the level the message was reported
    /// at — not the level it was created with, which can differ when a
    /// recommends check downgrades an error.
    pub level: String,
    /// The top-level description: "precondition not satisfied", and such.
    pub message: String,
    /// The primary spans, the ones rustc underlines.
    pub spans: Vec<SourceSpan>,
    pub labels: Vec<Label>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub help: Option<String>,
    /// The function whose obligation raised this, in friendly Rust spelling
    /// (`crate::module::f`). Null for a diagnostic raised outside the
    /// verification of any one function.
    pub function: Option<String>,
    /// The solver assertion ids the failing query reported, when it named
    /// any. Run-local: they identify an obligation within this run only.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub assert_ids: Vec<String>,
}

/// What the run concluded about the crate.
///
/// The counts are null rather than zero when the run did not get far enough
/// to have them, so that "nothing failed" and "we never looked" stay apart.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Results {
    /// Whether the crate verified. Null when the run verified only part of
    /// it, so the question has no answer.
    pub success: Option<bool>,
    pub verified: Option<u64>,
    pub errors: Option<u64>,
    pub encountered_error: bool,
    pub encountered_vir_error: bool,
    pub is_verifying_entire_crate: bool,
}

/// The whole artifact.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Report {
    pub schema_version: u32,
    /// The crate this report describes. Null only when the run failed before
    /// a crate was resolved.
    pub crate_name: Option<String>,
    pub results: Results,
    /// Every diagnostic Verus raised, in the order it raised them.
    pub diagnostics: Vec<Diagnostic>,
    /// Per-function detail, the same records `--output-json` prints under
    /// `func-details`, keyed by friendly Rust name.
    pub functions: BTreeMap<String, serde_json::Value>,
    /// The timing breakdown, present when the run was asked for one
    /// (`--time`); the same shape `--output-json` prints under `times-ms`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub times_ms: Option<serde_json::Value>,
    /// Which Verus built this, and which solvers it is pinned to.
    pub build_info: serde_json::Value,
}

impl Report {
    pub fn new(
        crate_name: Option<String>,
        results: Results,
        build_info: serde_json::Value,
    ) -> Self {
        Report {
            schema_version: SCHEMA_VERSION,
            crate_name,
            results,
            diagnostics: Vec::new(),
            functions: BTreeMap::new(),
            times_ms: None,
            build_info,
        }
    }
}

/// The file a report goes to, given what the caller asked for.
///
/// A path naming a directory — an existing one, or one written with a
/// trailing separator — takes the crate's name inside it. Cargo invokes
/// Verus once per target, so a fixed filename would have each invocation
/// clobber the last one's report and leave the caller with whichever
/// finished last. Naming the file after the crate keeps them apart.
pub fn destination(path: &Path, crate_name: Option<&str>) -> std::path::PathBuf {
    let names_a_directory =
        path.is_dir() || path.as_os_str().to_string_lossy().ends_with(std::path::MAIN_SEPARATOR);
    if !names_a_directory {
        return path.to_path_buf();
    }
    // A crate whose name has a path separator in it cannot happen, but the
    // name reaches a filesystem path, so it is not taken on trust.
    let stem: String = crate_name
        .unwrap_or("report")
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() || c == '_' { c } else { '-' })
        .collect();
    path.join(format!("{stem}.json"))
}

/// Write `report` to `path`, atomically.
///
/// `path` may name a file or a directory; see [`destination`].
///
/// The report is written beside its destination and renamed onto it, so a
/// reader polling the path sees either no file or a complete one — never a
/// half-written object it would have to tell apart from a malformed one.
/// `rename` is atomic within a directory, which is why the temporary goes
/// next to the destination rather than in the system temp directory.
pub fn write(path: &Path, report: &Report) -> std::io::Result<()> {
    let path = &destination(path, report.crate_name.as_deref());
    if let Some(parent) = path.parent().filter(|p| !p.as_os_str().is_empty()) {
        std::fs::create_dir_all(parent)?;
    }
    let json = serde_json::to_vec_pretty(report)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;

    // `.tmp.<pid>` keeps concurrent cargo targets writing to one path from
    // clobbering each other's temporary.
    let mut temp = path.as_os_str().to_owned();
    temp.push(format!(".tmp.{}", std::process::id()));
    let temp = std::path::PathBuf::from(temp);

    // Whichever step fails, the temporary does not outlive the attempt: a
    // full disk that stops the write half-way would otherwise leave a
    // `.tmp.<pid>` beside every report until someone noticed.
    let written = std::fs::write(&temp, &json).and_then(|()| std::fs::rename(&temp, path));
    if written.is_err() {
        let _ = std::fs::remove_file(&temp);
    }
    written
}
