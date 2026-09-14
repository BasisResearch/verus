//! Serve retained AIR queries after compilation in their original solvers.
//!
//! This driver serves one immutable compilation over JSON lines. It never reads
//! replacement source or accepts new assertions from its caller.
//!
//! On Unix, `VERUS_RESIDENT_SOCKET` selects a Unix socket pathname instead of
//! stdin/stdout. This supports Cargo's closed compiler stdin and keeps normal
//! JSON/timing/trace output separate. The caller drains stdout and stderr.
//! `ready.input_files` lists local source and explicit compiler dependencies,
//! including imported VIR files, for the MCP caller's snapshot coverage check.
//! It does not enumerate undeclared external reads by macros or build scripts.
//!
//! The catalogue names each query's `prover`: `default`, `nonlinear`, or
//! `bit_vector`. Specialised queries keep their original separate solvers;
//! bit-vector solvers remain prelude-free but use incremental query scopes.
//! Checked provenance describes round zero, matching the result and assertion
//! ID. Diagnostics can include further rounds requested by `--multiple-errors`.
//! Under `-V matching-loops`, `ready.matching_loops` is true and a check whose
//! round zero came back unknown carries its source-resolved `matching_loops`.
//!
//! `ready.smt_options` echoes the ordered name/value pairs already applied at
//! solver startup. Rechecks preserve those settings in the original contexts;
//! only the recorded per-query resource budget is set again before a check.
//!
//! An `egraph` request checks a retained query once more and reads, after its
//! `check-sat`, the equalities cvc5's e-graph holds in the classes of the
//! query's own terms. With `inject`, it then checks the query again with one
//! of those equalities asserted, named by the id the first reading gave it,
//! and reports how the verdict and the equalities changed. The equality is
//! one the solver itself reported for the same query, never text from the
//! caller, and it is popped with the query's scope. Neither verdict is a
//! `checked` one, and neither check saves a certificate.

use crate::buckets::BucketId;
use crate::commands::{QueryOp, Style};
use air::ast::{CommandX, Commands, Query};
use air::context::{
    Context, EgraphReply, EgraphRequest, QueryContext, SmtSolver, ValidityResult, VariableVersions,
};
use air::instantiations::ImportInstantiations;
use air::messages::{ArcDynMessage, Diagnostics, MessageLevel};
use serde::{Deserialize, Serialize};
use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};
use std::io::{self, BufRead, Read, Write};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Instant, SystemTime, UNIX_EPOCH};
use vir::air_names::SourceNames;
use vir::ast_util::fun_as_friendly_rust_name;
use vir::def::{CommandContext, CommandsWithContext};
use vir::messages::{MessageX, VirMessageInterface};

#[derive(Clone, Copy, Deserialize, Serialize)]
#[serde(transparent)]
struct QueryId(usize);

#[derive(Clone, Copy, Deserialize, Serialize)]
#[serde(transparent)]
struct BucketIndex(usize);

struct RetainedQuery {
    query: Query,
    context: CommandContext,
    prefix: usize,
    rlimit: f32,
    kind: QueryKind,
    prover: vir::def::ProverChoice,
    /// The severity the original invocation reports a failure of this query
    /// at, read from the same `QueryOp` the verifier reads. A recheck of a
    /// recommends query stays a warning.
    level: MessageLevel,
}

#[derive(Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
enum QueryKind {
    Termination,
    Body,
    RecommendsFollowup,
    Recommends,
    Expanded,
    ApiSafety,
}

impl QueryKind {
    fn from_op(op: &QueryOp) -> Self {
        match op {
            QueryOp::SpecTermination => Self::Termination,
            QueryOp::Body(Style::Normal) => Self::Body,
            QueryOp::Body(Style::RecommendsFollowupFromError) => Self::RecommendsFollowup,
            QueryOp::Body(Style::RecommendsChecked) => Self::Recommends,
            QueryOp::Body(Style::Expanded) => Self::Expanded,
            QueryOp::Body(Style::CheckApiSafety) => Self::ApiSafety,
        }
    }
}

/// A journal of bucket declarations and queries from one compilation.
///
/// Each journal entry has its own AIR/SMT scope. `applied` is the length of
/// the prefix currently asserted. A query can run only at its recorded prefix,
/// so declarations and axioms introduced later cannot affect an earlier query.
///
/// One entry holds every declaration batch sharing a scope. A scope is only
/// worth opening where some query can ask to return to it, so batches with no
/// query recorded between them are grouped. Scope depth and replay work then
/// follow the number of retained queries rather than the number of declaration
/// batches, which is roughly the size of the pruned call graph.
pub(crate) struct QueryJournal {
    contexts: Vec<Vec<Commands>>,
    queries: Vec<RetainedQuery>,
    applied: usize,
    /// Whether a query has been recorded since the open scope began.
    recorded_in_scope: bool,
}

#[derive(Deserialize)]
#[serde(tag = "command", rename_all = "snake_case", deny_unknown_fields)]
enum Request {
    List {
        session: Option<String>,
    },
    Check {
        session: String,
        bucket: BucketIndex,
        query: QueryId,
    },
    Egraph {
        session: String,
        bucket: BucketIndex,
        query: QueryId,
        /// The most equalities to list; default 20, at most 200.
        #[serde(default)]
        limit: Option<u32>,
        /// List equalities with a side a quantifier was instantiated with.
        #[serde(default)]
        include_used: bool,
        /// The id of an equality from this query's reading to assert in a
        /// second check.
        #[serde(default)]
        inject: Option<String>,
    },
    Close {
        session: String,
    },
}

#[derive(Clone, Serialize)]
struct QueryDescription {
    id: QueryId,
    function: String,
    description: String,
    kind: QueryKind,
    prover: &'static str,
    span: String,
}

#[derive(Serialize)]
struct BucketDescription {
    id: BucketIndex,
    name: String,
    queries: Vec<QueryDescription>,
}

/// Owned solver state transferred from compilation workers to the server.
/// The mutex keeps context restoration, checking and query cleanup atomic and
/// marks the bucket poisoned if a check panics. Poisoned state is never reused.
pub(crate) struct RetainedBucket {
    id: BucketId,
    queries: Vec<QueryDescription>,
    /// Catalogue ordinal -> original solver and its local query ordinal.
    addresses: Vec<(usize, usize)>,
    /// Catalogue ordinal -> the name its instantiation certificate is saved
    /// and exported under, the same for the same query in a later compilation.
    cert_keys: Vec<String>,
    state: Mutex<Vec<SolverState>>,
    symbols: Option<crate::provenance::Symbols>,
    /// Joins an `unknown` answer's culprits to source; kept in every mode.
    quantifiers: crate::provenance::Quantifiers,
}

pub(crate) struct SolverState {
    air: Context,
    journal: QueryJournal,
}

impl SolverState {
    pub(crate) fn new(air: Context, journal: QueryJournal) -> Self {
        Self { air, journal }
    }
}

impl RetainedBucket {
    pub(crate) fn new(
        id: BucketId,
        air: Context,
        journal: QueryJournal,
        mut spinoffs: Vec<SolverState>,
        symbols: Option<crate::provenance::Symbols>,
        quantifiers: crate::provenance::Quantifiers,
    ) -> Self {
        let mut states = Vec::new();
        // Spinoff queries already own their declaration context. The unused
        // primary context need not stay alive when every query was spun off.
        if !journal.queries.is_empty() || spinoffs.is_empty() {
            states.push(SolverState::new(air, journal));
        }
        states.append(&mut spinoffs);
        let mut queries = Vec::new();
        let mut addresses = Vec::new();
        let mut cert_keys = Vec::new();
        let mut repeats = std::collections::HashMap::new();
        for (solver, state) in states.iter().enumerate() {
            for (local, query) in state.journal.queries.iter().enumerate() {
                let function = fun_as_friendly_rust_name(&query.context.fun);
                let repeat = repeats
                    .entry(certificate_key(&function, query.kind, &query.context.desc, 0))
                    .or_insert(0);
                cert_keys.push(certificate_key(
                    &function,
                    query.kind,
                    &query.context.desc,
                    *repeat,
                ));
                *repeat += 1;
                queries.push(QueryDescription {
                    id: QueryId(queries.len()),
                    function,
                    description: query.context.desc.clone(),
                    kind: query.kind,
                    prover: match query.prover {
                        vir::def::ProverChoice::DefaultProver => "default",
                        vir::def::ProverChoice::Nonlinear => "nonlinear",
                        vir::def::ProverChoice::BitVector => "bit_vector",
                        vir::def::ProverChoice::Singular => "singular",
                    },
                    span: query.context.span.as_string.clone(),
                });
                addresses.push((solver, local));
            }
        }
        Self { id, queries, addresses, cert_keys, state: Mutex::new(states), symbols, quantifiers }
    }
}

/// The name a query's instantiation certificate goes by: FNV-1a over its
/// function, kind and description, and its position among the queries that
/// share all three. Spans are left out, so an edit elsewhere in the crate, or
/// in the function's own body, keeps the name.
fn certificate_key(function: &str, kind: QueryKind, description: &str, repeat: usize) -> String {
    let kind = serde_json::to_string(&kind).unwrap_or_default();
    let repeat = repeat.to_string();
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for part in [function, kind.as_str(), description, repeat.as_str()] {
        for byte in part.bytes().chain(std::iter::once(0)) {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    format!("c{hash:016x}")
}

/// The most a certificate file may hold for it to be read.
const MAX_CERTIFICATE_BYTES: u64 = 64 << 20;

/// The text of the certificate at `path`, if it is a regular file of at most
/// `MAX_CERTIFICATE_BYTES`. The directory is shared, so anything may sit at
/// that name. On unix the file is opened without blocking, so a FIFO there
/// cannot stall the server, and its type is checked on the open handle, so it
/// cannot be swapped between the check and the read.
fn read_certificate(path: &std::path::Path) -> Option<String> {
    let mut options = std::fs::OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    std::os::unix::fs::OpenOptionsExt::custom_flags(
        &mut options,
        libc::O_NONBLOCK | libc::O_NOCTTY,
    );
    let file = options.open(path).ok()?;
    let metadata = file.metadata().ok()?;
    if !metadata.is_file() || metadata.len() > MAX_CERTIFICATE_BYTES {
        return None;
    }
    // The file may grow after the check, so the read is capped too.
    let mut text = String::new();
    file.take(MAX_CERTIFICATE_BYTES + 1).read_to_string(&mut text).ok()?;
    (text.len() as u64 <= MAX_CERTIFICATE_BYTES).then_some(text)
}

/// Export what `key` saved to `<dir>/<key>.smt2`, where a later session's
/// solver can import it. Only a certificate that names an instance is written.
/// It goes to a file no other writer uses, then is renamed into place, so a
/// reader never sees half a file, nor two sessions' writes interleaved. A
/// failure only costs a later session its certificate.
fn write_certificate(air: &mut Context, dir: &std::path::Path, key: &str) {
    static WRITES: AtomicUsize = AtomicUsize::new(0);
    let Some(certificate) = air.export_instantiations(key) else {
        return;
    };
    let path = dir.join(format!("{key}.smt2"));
    let write = WRITES.fetch_add(1, Ordering::Relaxed);
    let partial = dir.join(format!("{key}.smt2.{}-{write}.partial", std::process::id()));
    if std::fs::write(&partial, certificate.to_text()).is_err()
        || std::fs::rename(&partial, &path).is_err()
    {
        let _ = std::fs::remove_file(&partial);
    }
}

/// One invocation owns every selected bucket. Only this layer owns protocol
/// I/O; compiler workers finish and return their contexts before it starts.
pub(crate) struct Server {
    buckets: Vec<RetainedBucket>,
    info: SessionInfo,
}

/// What a session reports about the invocation behind it, and the settings a
/// recheck has to reproduce. Passed whole rather than assembled by builders:
/// each field has to come from the invocation, so none of them has a default
/// that would be right to fall back to.
pub(crate) struct SessionInfo {
    pub(crate) provenance: bool,
    /// Whether the retained solvers record instantiations for
    /// `(get-info :matching-loops)` (`-V matching-loops`).
    pub(crate) matching_loops: bool,
    pub(crate) spinoff_all: bool,
    /// How many errors one query may report, as `--multiple-errors` set it. A
    /// recheck looks for as many as the original invocation did.
    pub(crate) multiple_errors: u32,
    pub(crate) input_files: Vec<String>,
    /// The ordered startup settings. They already live in every retained
    /// solver and must not be reapplied after initialization.
    pub(crate) smt_options: Vec<(String, String)>,
    /// Whether ordinary cvc5 solvers were launched for instantiation replay
    /// (`VERUS_RESIDENT_INST_REPLAY`), so rechecks try certificates first.
    pub(crate) instantiation_replay: bool,
}

#[derive(Serialize)]
#[serde(tag = "event", rename_all = "snake_case")]
enum Response<'a> {
    Ready {
        protocol: u32,
        session: &'a str,
        process_id: u32,
        invocation_succeeded: bool,
        provenance: bool,
        matching_loops: bool,
        spinoff_all: bool,
        smt_options: &'a [(String, String)],
        instantiation_replay: bool,
        input_files: &'a [String],
        buckets: &'a [BucketDescription],
    },
    Queries {
        session: &'a str,
        buckets: &'a [BucketDescription],
    },
    Checked {
        session: &'a str,
        bucket: BucketIndex,
        query: QueryId,
        result: QueryResult,
        assert_id: Option<Vec<u64>>,
        diagnostics: Vec<SourceDiagnostic>,
        elapsed_ms: u128,
        restore_ms: u128,
        provenance: Option<&'a crate::provenance::ResolvedQueryProvenance>,
        /// Present when the first round answered `unknown`: the solver's reason
        /// and candidate culprit quantifiers.
        unknown_reason: Option<&'a crate::provenance::ResolvedUnknownReason>,
        /// Present when round zero came back unknown under `-V matching-loops`.
        matching_loops: Option<&'a crate::provenance::ResolvedQueryMatchingLoops>,
        /// Present when this check tried a certificate before searching.
        certificate: Option<CertificateAttempt>,
    },
    Egraph {
        session: &'a str,
        bucket: BucketIndex,
        query: QueryId,
        #[serde(flatten)]
        outcome: Box<EgraphOutcome>,
    },
    Error {
        message: &'a str,
    },
    Closed {
        session: &'a str,
    },
}

/// Where a tried certificate came from: this solver's own save from an earlier
/// check, or a file an earlier session exported.
#[derive(Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
enum CertificateSource {
    Session,
    Imported,
}

/// A certificate attempt: `closed` when the restored instances alone proved
/// the query, otherwise the verdict comes from the ordinary check that
/// followed. `elapsed_ms` is the attempt alone and is part of the check's.
#[derive(Clone, Copy, Serialize)]
struct CertificateAttempt {
    source: CertificateSource,
    closed: bool,
    elapsed_ms: u128,
}

#[derive(Clone, Copy, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
enum QueryResult {
    Valid,
    Invalid,
    ResourceLimit,
}

/// `air::messages::MessageLevel` serialises its Rust variant names, and the
/// protocol spells every other enum in snake case.
#[derive(Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
enum DiagnosticLevel {
    Error,
    Warning,
    Note,
}

impl From<MessageLevel> for DiagnosticLevel {
    fn from(level: MessageLevel) -> Self {
        match level {
            MessageLevel::Error => Self::Error,
            MessageLevel::Warning => Self::Warning,
            MessageLevel::Note => Self::Note,
        }
    }
}

#[derive(Serialize)]
struct SourceDiagnostic {
    level: DiagnosticLevel,
    message: String,
    spans: Vec<String>,
    labels: Vec<SourceLabel>,
}

#[derive(Serialize)]
struct SourceLabel {
    message: String,
    span: String,
}

#[derive(Default)]
struct QueryDiagnostics(RefCell<Vec<SourceDiagnostic>>);

impl QueryDiagnostics {
    fn record(&self, message: &ArcDynMessage, level: MessageLevel) {
        let message = message.downcast_ref::<MessageX>().expect("VIR diagnostic message");
        self.0.borrow_mut().push(SourceDiagnostic {
            level: level.into(),
            message: message.note.clone(),
            spans: message.spans.iter().map(|span| span.as_string.clone()).collect(),
            labels: message
                .labels
                .iter()
                .map(|label| SourceLabel {
                    message: label.note.clone(),
                    span: label.span.as_string.clone(),
                })
                .collect(),
        });
    }

    /// A diagnostic about the query as a whole rather than about one assertion
    /// the solver named: no labels, and the query's own span.
    fn bare(&self, level: DiagnosticLevel, message: String, span: &str) {
        self.0.borrow_mut().push(SourceDiagnostic {
            level,
            message,
            spans: vec![span.to_owned()],
            labels: Vec::new(),
        });
    }
}

impl Diagnostics for QueryDiagnostics {
    fn report(&self, message: &ArcDynMessage) {
        let level = message.downcast_ref::<MessageX>().expect("VIR diagnostic message").level;
        self.record(message, level);
    }

    fn report_now(&self, message: &ArcDynMessage) {
        self.report(message);
    }

    fn report_as(&self, message: &ArcDynMessage, level: MessageLevel) {
        self.record(message, level);
    }

    fn report_as_now(&self, message: &ArcDynMessage, level: MessageLevel) {
        self.record(message, level);
    }
}

fn send(output: &mut impl Write, response: &Response<'_>) -> io::Result<()> {
    serde_json::to_writer(&mut *output, response)?;
    writeln!(output)?;
    output.flush()
}

/// Tell a caller that no session is coming, over whichever transport it is
/// waiting on. Preparation can fail after the compiler driver has returned,
/// and the summary line is suppressed under `--resident`, so without this the
/// caller sees an empty stdout, or a socket that never accepts, and cannot
/// tell that apart from a crash. The reason itself has already gone to stderr.
pub(crate) fn report_unavailable(reason: &str) -> io::Result<()> {
    let response = Response::Error { message: reason };
    #[cfg(unix)]
    if let Some(path) = std::env::var_os("VERUS_RESIDENT_SOCKET") {
        let mut stream = std::os::unix::net::UnixStream::connect(path)?;
        return send(&mut stream, &response);
    }
    send(&mut io::stdout().lock(), &response)
}

/// End the session, telling the caller why before the pipe closes. Without a
/// final frame the only signal is EOF, which a caller cannot tell apart from
/// an orderly shutdown. A failure to send is discarded: the error being
/// reported is the one worth returning.
fn fatal<T>(output: &mut impl Write, error: io::Error) -> io::Result<T> {
    let message = error.to_string();
    let _ = send(output, &Response::Error { message: &message });
    Err(error)
}

/// How many equalities one reading of the e-graph asks cvc5 for. A listing
/// shows fewer; the rest let an injection find its equality again, and let
/// the two checks' readings be compared.
const EGRAPH_READ_LIMIT: u32 = 1000;
/// The default and the most equalities a listing shows.
const EGRAPH_LIST_DEFAULT: u32 = 20;
const EGRAPH_LIST_MAX: u32 = 200;
/// The most new equalities a frontier delta names.
const FRONTIER_SHOWN: usize = 20;

const INJECTION_CAVEAT: &str = "The equality was asserted in a scope popped right after this check, so the session's solver state is unchanged. This verdict is not a verification result: add the assert to the source and verify it normally.";

/// What an e-graph request found.
#[derive(Serialize)]
struct EgraphOutcome {
    /// The query checked as usual, with the e-graph read after `check-sat`.
    before: EgraphRun,
    summary: EgraphSummary,
    equalities: Vec<ResolvedEquality>,
    /// Present when the request named an equality to inject.
    #[serde(skip_serializing_if = "Option::is_none")]
    injection: Option<Injection>,
}

/// One check an e-graph request made. Its verdict is never a `checked` one:
/// an injected check asserts more than the query does.
#[derive(Serialize)]
struct EgraphRun {
    result: QueryResult,
    assert_id: Option<Vec<u64>>,
    elapsed_ms: u128,
    /// Why the e-graph could not be read, as after a valid check, which
    /// leaves none.
    #[serde(skip_serializing_if = "Option::is_none")]
    egraph_error: Option<String>,
}

/// What one reading counted.
#[derive(Serialize)]
struct EgraphSummary {
    /// The classes cvc5 listed from, and the equalities it found in them.
    classes: u64,
    candidates: u64,
    /// The query's terms sent to focus the reading, and how many of them the
    /// e-graph holds.
    focus_terms: u64,
    focus_found: u64,
    /// Equalities read and shown to the caller, of which `equalities` lists
    /// at most `limit`.
    listed: usize,
    /// Equalities not listed because a quantifier was already instantiated
    /// with a side (see `include_used`).
    used_omitted: usize,
    /// Equalities not listed because both sides render alike (a box and the
    /// value inside it), neither renders as source, or an equality listed
    /// before reads the same (the same one between differently boxed terms).
    hidden: usize,
    /// Terms cvc5 left out because they print larger than its size limit.
    too_large: u64,
}

#[derive(Clone, Serialize)]
struct ResolvedEquality {
    /// Names this equality in an `inject` request. The same two terms get the
    /// same id in every reading of the same query.
    id: String,
    /// The two sides in source spelling, each mutable variable with its
    /// assignment version.
    lhs: String,
    rhs: String,
    /// `entailed`: follows from what the query asserts, which includes the
    /// negated goal. `decision`: holds only on the branch the search was on.
    /// `unknown`: no single theory explains it.
    level: String,
    /// Whether a quantifier a proof relies on, one the user wrote or one
    /// defining a function, was instantiated with either side. Instances of
    /// the encoding's own axioms (the prelude, boxing, type invariants, fuel)
    /// do not count.
    used_by_proof: bool,
    /// Where those quantifiers are written.
    used_by: Vec<String>,
    /// How many of the two sides are terms of the query itself, 0 to 2.
    focus: u32,
    /// The literals the equality follows from, in source spelling, except
    /// those `because_hidden` counts.
    holds_because: Vec<String>,
    /// Literals of the explanation cvc5 left out, as naming a skolem or
    /// printing larger than its size limit. When present, `holds_because`
    /// alone does not imply the equality.
    #[serde(skip_serializing_if = "is_zero")]
    because_hidden: u64,
    /// `assert(lhs == rhs);` to add to the source, when the equality is
    /// entailed, both sides render as source, and no variable appears at two
    /// assignment versions. Variables are named without versions and the
    /// crate's own items under `crate::`: place it where the variables hold
    /// the versions `lhs` and `rhs` show.
    #[serde(skip_serializing_if = "Option::is_none")]
    verus_assert: Option<String>,
    /// The two sides as the solver spells them.
    smt_lhs: String,
    smt_rhs: String,
}

#[derive(Serialize)]
struct Injection {
    equality: ResolvedEquality,
    after: EgraphRun,
    /// The query failed without the equality and holds with it asserted.
    closed: bool,
    /// How the injected check's reading differs from the first, when the
    /// injected check left an e-graph to read.
    #[serde(skip_serializing_if = "Option::is_none")]
    frontier_delta: Option<FrontierDelta>,
    caveat: &'static str,
}

#[derive(Debug, PartialEq, Serialize)]
struct FrontierDelta {
    /// Equalities the injected check's reading holds between terms the first
    /// reading held apart or did not hold, in source spelling.
    new_equalities: Vec<(String, String)>,
    new_equality_count: usize,
    /// Equalities of the first reading whose sides the second holds apart:
    /// the injected search went another way.
    lost_equality_count: usize,
    /// How many of the first reading's classes merged into another.
    classes_merged: usize,
}

fn is_zero(count: &u64) -> bool {
    *count == 0
}

/// Names this equality in an `inject` request: FNV-1a over the two terms as
/// the solver spells them, so it survives a second reading of the same query.
fn equality_id(lhs: &str, rhs: &str) -> String {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for part in [lhs, rhs] {
        for byte in part.bytes().chain(std::iter::once(0)) {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }
    format!("eq#{:012x}", hash >> 16)
}

/// Source names for rendering one query's solver terms.
struct QueryNames<'a> {
    symbols: Option<&'a crate::provenance::Symbols>,
    /// SSA symbols as their variable with its assignment version, to show.
    shown: Cow<'a, SourceNames>,
    /// Source to paste: SSA symbols as their variable alone, and the crate's
    /// own items under `crate::`.
    plain: Cow<'a, SourceNames>,
    /// Each SSA symbol's variable and version. Two versions of one variable
    /// read alike in `plain`, so an assert naming both cannot be pasted.
    versions: &'a VariableVersions,
}

impl<'a> QueryNames<'a> {
    fn new(
        symbols: Option<&'a crate::provenance::Symbols>,
        versions: &'a VariableVersions,
        empty: &'a SourceNames,
    ) -> Self {
        match symbols {
            Some(symbols) => Self {
                symbols: Some(symbols),
                shown: symbols.query_names(versions, true),
                plain: symbols.paste_names(versions),
                versions,
            },
            None => Self {
                symbols: None,
                shown: Cow::Borrowed(empty),
                plain: Cow::Borrowed(empty),
                versions,
            },
        }
    }

    /// `assert(lhs == rhs);` to add to the source, when that assert says what
    /// the equality says: it is entailed, both sides render as source, and no
    /// variable appears in it at two assignment versions.
    fn verus_assert(&self, equality: &air::context::EgraphEquality) -> Option<String> {
        if equality.level != "entailed" {
            return None;
        }
        let terms = [equality.lhs.as_str(), equality.rhs.as_str()];
        if !terms.iter().all(|term| vir::air_names::renders_as_source(&self.plain, term)) {
            return None;
        }
        // SSA symbols are plain SMT-LIB symbols, never quoted, so splitting
        // on parentheses and spaces finds every one.
        let mut version_of: HashMap<&str, u32> = HashMap::new();
        for atom in terms.iter().flat_map(|term| term.split(['(', ')', ' ', '\n'])) {
            if let Some((base, version)) = self.versions.get(atom) {
                if *version_of.entry(base.as_str()).or_insert(*version) != *version {
                    return None;
                }
            }
        }
        Some(format!(
            "assert({} == {});",
            vir::air_names::render_term(&self.plain, &equality.lhs),
            vir::air_names::render_term(&self.plain, &equality.rhs)
        ))
    }

    /// Where the quantifiers a proof relies on among `qids` are written.
    /// Without symbols to tell which those are, every one, by its name.
    fn proof_uses(&self, qids: &[String]) -> Vec<String> {
        match self.symbols {
            Some(symbols) => qids
                .iter()
                .filter_map(|qid| symbols.proof_quantifier_site(qid))
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect(),
            None => qids.to_vec(),
        }
    }

    fn show(&self, term: &str) -> String {
        vir::air_names::render_term(&self.shown, term)
    }

    /// Whether an equality is worth showing: its sides render differently,
    /// and at least one reads as source.
    fn shows(&self, lhs: &str, rhs: &str) -> bool {
        self.show(lhs) != self.show(rhs)
            && (vir::air_names::renders_as_source(&self.plain, lhs)
                || vir::air_names::renders_as_source(&self.plain, rhs))
    }

    /// The reading's equalities worth showing, in its order, and how many
    /// were hidden.
    fn resolve(&self, reply: &EgraphReply) -> (Vec<ResolvedEquality>, usize) {
        let mut hidden = 0;
        let mut resolved: Vec<ResolvedEquality> = Vec::new();
        let mut seen: HashMap<(String, String), usize> = HashMap::new();
        for equality in &reply.equalities {
            if !self.shows(&equality.lhs, &equality.rhs) {
                hidden += 1;
                continue;
            }
            let (lhs, rhs) = (self.show(&equality.lhs), self.show(&equality.rhs));
            let key =
                if lhs <= rhs { (lhs.clone(), rhs.clone()) } else { (rhs.clone(), lhs.clone()) };
            let used_by = self.proof_uses(&equality.used_by);
            // The same equality between differently boxed terms reads the
            // same; show it once, under the first reading's terms. A proof
            // uses it when it uses either spelling, whichever came first.
            if let Some(&index) = seen.get(&key) {
                let kept = &mut resolved[index];
                let merged: BTreeSet<String> = kept.used_by.drain(..).chain(used_by).collect();
                kept.used_by = merged.into_iter().collect();
                kept.used_by_proof = !kept.used_by.is_empty();
                if kept.verus_assert.is_none() {
                    kept.verus_assert = self.verus_assert(equality);
                }
                hidden += 1;
                continue;
            }
            seen.insert(key, resolved.len());
            resolved.push(ResolvedEquality {
                id: equality_id(&equality.lhs, &equality.rhs),
                lhs,
                rhs,
                level: equality.level.clone(),
                used_by_proof: !used_by.is_empty(),
                used_by,
                focus: equality.focus,
                holds_because: equality.because.iter().map(|lit| self.show(lit)).collect(),
                because_hidden: equality.because_hidden,
                verus_assert: self.verus_assert(equality),
                smt_lhs: equality.lhs.clone(),
                smt_rhs: equality.rhs.clone(),
            });
        }
        (resolved, hidden)
    }
}

/// Each term of a reading, mapped to its class: each listed equality joins
/// its two sides.
fn term_classes(reply: &EgraphReply) -> HashMap<&str, usize> {
    fn find(parent: &mut Vec<usize>, mut i: usize) -> usize {
        while parent[i] != i {
            parent[i] = parent[parent[i]];
            i = parent[i];
        }
        i
    }
    let mut index: HashMap<&str, usize> = HashMap::new();
    let mut parent: Vec<usize> = Vec::new();
    for equality in &reply.equalities {
        let mut ids = [0; 2];
        for (slot, term) in ids.iter_mut().zip([equality.lhs.as_str(), equality.rhs.as_str()]) {
            *slot = *index.entry(term).or_insert_with(|| {
                parent.push(parent.len());
                parent.len() - 1
            });
        }
        let (a, b) = (find(&mut parent, ids[0]), find(&mut parent, ids[1]));
        if a != b {
            parent[a] = b;
        }
    }
    index.iter().map(|(term, &i)| (*term, find(&mut parent, i))).collect()
}

/// How the injected check's reading differs from the first. The injected
/// equality itself is not new.
fn frontier_delta(
    before: &EgraphReply,
    after: &EgraphReply,
    injected: (&str, &str),
    names: &QueryNames,
) -> FrontierDelta {
    let old = term_classes(before);
    let new = term_classes(after);
    let together = |classes: &HashMap<&str, usize>, lhs: &str, rhs: &str| matches!((classes.get(lhs), classes.get(rhs)), (Some(a), Some(b)) if a == b);
    let mut new_equalities = Vec::new();
    let mut new_equality_count = 0;
    for equality in &after.equalities {
        let (lhs, rhs) = (equality.lhs.as_str(), equality.rhs.as_str());
        if (lhs, rhs) == injected || (rhs, lhs) == injected || together(&old, lhs, rhs) {
            continue;
        }
        new_equality_count += 1;
        if new_equalities.len() < FRONTIER_SHOWN && names.shows(lhs, rhs) {
            new_equalities.push((names.show(lhs), names.show(rhs)));
        }
    }
    let lost_equality_count = before
        .equalities
        .iter()
        .filter(|e| {
            new.contains_key(e.lhs.as_str())
                && new.contains_key(e.rhs.as_str())
                && !together(&new, &e.lhs, &e.rhs)
        })
        .count();
    let mut joined: HashMap<usize, BTreeSet<usize>> = HashMap::new();
    for (term, class) in &new {
        if let Some(old_class) = old.get(term) {
            joined.entry(*class).or_default().insert(*old_class);
        }
    }
    FrontierDelta {
        new_equalities,
        new_equality_count,
        lost_equality_count,
        classes_merged: joined.values().map(|classes| classes.len() - 1).sum(),
    }
}

/// Check a retained query for an e-graph request, with the e-graph read after
/// its first `check-sat` and, when given, an equality asserted before it.
/// Rounds for further errors are not run, and nothing is saved as a
/// certificate. The caller has restored the query's prefix.
fn egraph_check(
    air: &mut Context,
    query: &RetainedQuery,
    inject: Option<(&str, &str)>,
    set_rlimit: &impl Fn(&mut Context, f32),
) -> io::Result<(EgraphRun, EgraphReply)> {
    set_rlimit(air, query.rlimit);
    air.set_egraph_request(Some(EgraphRequest { limit: EGRAPH_READ_LIMIT, include_used: true }));
    if let Some((lhs, rhs)) = inject {
        air.set_inject_equality(lhs, rhs).map_err(io::Error::other)?;
    }
    let start = Instant::now();
    let outcome = air.check_valid(
        &VirMessageInterface {},
        &QueryDiagnostics::default(),
        &query.query,
        QueryContext::default(),
    );
    let elapsed_ms = start.elapsed().as_millis();
    let reply = air.take_egraph();
    air.set_egraph_request(None);
    drop(air.take_provenance());
    let (result, assert_id) = match outcome {
        ValidityResult::Valid(_) => (QueryResult::Valid, None),
        ValidityResult::Invalid(_, _, id) => (QueryResult::Invalid, id.map(|id| (*id).clone())),
        ValidityResult::Canceled => (QueryResult::ResourceLimit, None),
        ValidityResult::TypeError(error) => return Err(io::Error::other(error.to_string())),
        ValidityResult::UnexpectedOutput(error) => return Err(io::Error::other(error)),
    };
    air.finish_query();
    let reply = reply.unwrap_or_else(|| EgraphReply {
        error: Some("the check did not reach check-sat".to_owned()),
        ..EgraphReply::default()
    });
    let run = EgraphRun { result, assert_id, elapsed_ms, egraph_error: reply.error.clone() };
    Ok((run, reply))
}

/// Serve an e-graph request for one query of `bucket`, whose address the
/// caller has checked. `Ok(Err(_))` is a refusal to report; `Err` ends the
/// session.
fn serve_egraph(
    bucket: &RetainedBucket,
    id: QueryId,
    limit: Option<u32>,
    include_used: bool,
    inject: Option<&str>,
    set_rlimit: &impl Fn(&mut Context, f32),
) -> io::Result<Result<EgraphOutcome, &'static str>> {
    let mut state =
        bucket.state.lock().map_err(|_| io::Error::other("resident bucket poisoned"))?;
    let (solver, local) = bucket.addresses[id.0];
    let SolverState { air, journal } = &mut state[solver];
    if !matches!(air.get_solver(), SmtSolver::Cvc5) {
        return Ok(Err("e-graph requests need cvc5"));
    }
    let prefix = journal.queries[local].prefix;
    journal.restore_prefix(air, prefix)?;
    let query = &journal.queries[local];
    let (before, reading) = egraph_check(air, query, None, set_rlimit)?;
    let empty = SourceNames::new();
    let names = QueryNames::new(bucket.symbols.as_ref(), &reading.variable_versions, &empty);
    let (listed, hidden) = names.resolve(&reading);
    let injection = match inject {
        None => None,
        Some(wanted) => {
            let Some(equality) = listed.iter().find(|equality| equality.id == wanted).cloned()
            else {
                return Ok(Err(
                    "no equality has that id in this check's reading; list the equalities again",
                ));
            };
            let injected = (equality.smt_lhs.as_str(), equality.smt_rhs.as_str());
            let (after, second) = egraph_check(air, query, Some(injected), set_rlimit)?;
            let frontier_delta =
                second.error.is_none().then(|| frontier_delta(&reading, &second, injected, &names));
            let closed = before.result != QueryResult::Valid && after.result == QueryResult::Valid;
            Some(Injection { equality, after, closed, frontier_delta, caveat: INJECTION_CAVEAT })
        }
    };
    let limit = limit.unwrap_or(EGRAPH_LIST_DEFAULT).clamp(1, EGRAPH_LIST_MAX) as usize;
    let (shown, used): (Vec<_>, Vec<_>) =
        listed.into_iter().partition(|equality| include_used || !equality.used_by_proof);
    let summary = EgraphSummary {
        classes: reading.classes,
        candidates: reading.candidates,
        focus_terms: reading.focus,
        focus_found: reading.focus_found,
        listed: shown.len(),
        used_omitted: used.len(),
        hidden,
        too_large: reading.too_large,
    };
    let equalities = shown.into_iter().take(limit).collect();
    Ok(Ok(EgraphOutcome { before, summary, equalities, injection }))
}

impl QueryJournal {
    pub(crate) fn new() -> Self {
        Self { contexts: Vec::new(), queries: Vec::new(), applied: 0, recorded_in_scope: false }
    }

    /// Retain the next declaration batch, opening a scope when one is needed.
    pub(crate) fn push_context(
        &mut self,
        air: &mut Context,
        commands: Commands,
    ) -> Result<(), &'static str> {
        if commands.iter().any(|command| !matches!(**command, CommandX::Global(_))) {
            return Err("resident context batches must contain only declarations");
        }
        debug_assert_eq!(self.applied, self.contexts.len());
        // No recorded prefix can fall inside a run of batches that no query
        // separates, so such a run needs no scope boundary between its parts.
        if self.recorded_in_scope || self.contexts.is_empty() {
            air.push();
            self.contexts.push(Vec::new());
            self.applied += 1;
            self.recorded_in_scope = false;
        }
        self.contexts.last_mut().expect("scope opened above").push(commands);
        Ok(())
    }

    /// Retain the lowered query and the declaration prefix that precedes it.
    pub(crate) fn record_query(
        &mut self,
        commands: CommandsWithContext,
        op: &QueryOp,
        rlimit: f32,
    ) -> Result<(), &'static str> {
        if commands.commands.iter().any(|command| !matches!(**command, CommandX::CheckValid(_))) {
            return Err("resident query batches must contain only check-valid commands");
        }
        for command in commands.commands.iter() {
            if let CommandX::CheckValid(query) = &**command {
                self.queries.push(RetainedQuery {
                    query: query.clone(),
                    context: commands.context.clone(),
                    prefix: self.applied,
                    rlimit,
                    kind: QueryKind::from_op(op),
                    prover: commands.prover_choice,
                    level: op.message_level(),
                });
                // The next declaration batch must start a scope: this query
                // can ask to return to the prefix that ends here.
                self.recorded_in_scope = true;
            }
        }
        Ok(())
    }

    fn restore_prefix(&mut self, air: &mut Context, prefix: usize) -> io::Result<()> {
        while self.applied > prefix {
            air.pop();
            self.applied -= 1;
        }
        while self.applied < prefix {
            air.push();
            // Count the scope before replaying into it, so that a failure part
            // way through still leaves `applied` describing the real depth.
            let scope = self.applied;
            self.applied += 1;
            for batch in self.contexts[scope].iter() {
                for command in batch.iter() {
                    if let CommandX::Global(decl) = &**command {
                        air.global(decl).map_err(|error| io::Error::other(error.to_string()))?;
                    }
                }
            }
        }
        // `push`, `pop` and `global` only fill the pipe buffer, so without this
        // the solver's share of the replay would be charged to the query that
        // follows. Flushing here also surfaces a solver complaint about a
        // replayed declaration as a restoration failure rather than as
        // unexpected output from the next check.
        let output = air.flush_commands();
        if !output.is_empty() {
            return Err(io::Error::other(format!(
                "solver rejected the restored context: {}",
                output.join(" ")
            )));
        }
        Ok(())
    }
}

impl Server {
    pub(crate) fn new(mut buckets: Vec<RetainedBucket>, info: SessionInfo) -> Self {
        // Compilation can finish in any order. Protocol ordinals follow the
        // verifier's bucket identity, not worker completion order.
        buckets.sort_by(|left, right| left.id.cmp(&right.id));
        Self { buckets, info }
    }

    pub(crate) fn serve(
        mut self,
        invocation_succeeded: bool,
        set_rlimit: impl Fn(&mut Context, f32),
    ) -> io::Result<()> {
        let stamp = SystemTime::now().duration_since(UNIX_EPOCH).map_err(io::Error::other)?;
        let session = format!("{}-{}", std::process::id(), stamp.as_nanos());
        #[cfg(unix)]
        if let Some(path) = std::env::var_os("VERUS_RESIDENT_SOCKET") {
            let stream = std::os::unix::net::UnixStream::connect(path)?;
            return self.run(
                &session,
                invocation_succeeded,
                io::BufReader::new(stream.try_clone()?),
                stream,
                set_rlimit,
            );
        }
        let input = io::stdin();
        let output = io::stdout();
        self.run(&session, invocation_succeeded, input.lock(), output.lock(), set_rlimit)
    }

    fn shutdown(&mut self) -> io::Result<()> {
        for bucket in &mut self.buckets {
            let state =
                bucket.state.get_mut().map_err(|_| io::Error::other("resident bucket poisoned"))?;
            for solver in state {
                solver.journal.restore_prefix(&mut solver.air, 0)?;
            }
        }
        // Dropping AIR contexts closes and waits for every solver. A closed
        // acknowledgement is sent only after all children have exited.
        self.buckets.clear();
        Ok(())
    }

    fn run(
        &mut self,
        session: &str,
        invocation_succeeded: bool,
        mut input: impl BufRead,
        mut output: impl Write,
        set_rlimit: impl Fn(&mut Context, f32),
    ) -> io::Result<()> {
        let buckets: Vec<_> = self
            .buckets
            .iter()
            .enumerate()
            .map(|(id, bucket)| BucketDescription {
                id: BucketIndex(id),
                name: bucket.id.friendly_name(),
                queries: bucket.queries.clone(),
            })
            .collect();
        send(
            &mut output,
            &Response::Ready {
                protocol: 2,
                session,
                process_id: std::process::id(),
                invocation_succeeded,
                provenance: self.info.provenance,
                matching_loops: self.info.matching_loops,
                spinoff_all: self.info.spinoff_all,
                smt_options: &self.info.smt_options,
                instantiation_replay: self.info.instantiation_replay,
                input_files: &self.info.input_files,
                buckets: &buckets,
            },
        )?;
        let multiple_errors = self.info.multiple_errors;
        // Where certificates outlive this session, if replay is on.
        let cert_dir = std::env::var_os("VERUS_RESIDENT_INST_DIR").map(std::path::PathBuf::from);
        loop {
            // A framing failure closes the session. Never interpret a suffix of
            // an oversized request as a second request. Say so before closing:
            // a caller cannot tell a silent close apart from an orderly one.
            let mut line = String::new();
            match input.by_ref().take(65537).read_line(&mut line) {
                Ok(0) => {
                    self.shutdown()?;
                    return Ok(());
                }
                Ok(_) => {}
                Err(error) => return fatal(&mut output, error),
            }
            if line.len() > 65536 {
                return fatal(
                    &mut output,
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        "resident request exceeds 64 KiB including its newline",
                    ),
                );
            }
            let request = match serde_json::from_str::<Request>(&line) {
                Ok(request) => request,
                Err(_) => {
                    send(&mut output, &Response::Error { message: "invalid resident request" })?;
                    continue;
                }
            };
            match request {
                Request::List { session: Some(requested) }
                | Request::Check { session: requested, .. }
                | Request::Egraph { session: requested, .. }
                | Request::Close { session: requested }
                    if requested != session =>
                {
                    send(
                        &mut output,
                        &Response::Error { message: "session does not match this compilation" },
                    )?;
                }
                Request::List { .. } => {
                    send(&mut output, &Response::Queries { session, buckets: &buckets })?
                }
                Request::Close { .. } => {
                    if let Err(error) = self.shutdown() {
                        return fatal(&mut output, error);
                    }
                    send(&mut output, &Response::Closed { session })?;
                    return Ok(());
                }
                Request::Egraph {
                    bucket: bucket_id,
                    query: id,
                    limit,
                    include_used,
                    inject,
                    ..
                } => {
                    let Some(bucket) = self.buckets.get(bucket_id.0) else {
                        send(&mut output, &Response::Error { message: "unknown bucket" })?;
                        continue;
                    };
                    if bucket.queries.get(id.0).is_none() {
                        send(&mut output, &Response::Error { message: "unknown query" })?;
                        continue;
                    }
                    match serve_egraph(
                        bucket,
                        id,
                        limit,
                        include_used,
                        inject.as_deref(),
                        &set_rlimit,
                    ) {
                        Ok(Ok(outcome)) => send(
                            &mut output,
                            &Response::Egraph {
                                session,
                                bucket: bucket_id,
                                query: id,
                                outcome: Box::new(outcome),
                            },
                        )?,
                        Ok(Err(message)) => send(&mut output, &Response::Error { message })?,
                        Err(error) => return fatal(&mut output, error),
                    }
                }
                Request::Check { bucket: bucket_id, query: id, .. } => {
                    let Some(bucket) = self.buckets.get(bucket_id.0) else {
                        send(&mut output, &Response::Error { message: "unknown bucket" })?;
                        continue;
                    };
                    // Check both coordinates before locking or mutating solver state.
                    if bucket.queries.get(id.0).is_none() {
                        send(&mut output, &Response::Error { message: "unknown query" })?;
                        continue;
                    }
                    let mut state = match bucket.state.lock() {
                        Ok(state) => state,
                        Err(_) => {
                            return fatal(
                                &mut output,
                                io::Error::other("resident bucket poisoned"),
                            );
                        }
                    };
                    let (solver, local) = bucket.addresses[id.0];
                    let SolverState { air, journal } = &mut state[solver];
                    let prefix = journal.queries[local].prefix;
                    // Restoration replays declarations through AIR and the
                    // solver, so it is timed apart from the check itself.
                    let restore_start = Instant::now();
                    if let Err(error) = journal.restore_prefix(air, prefix) {
                        return fatal(&mut output, error);
                    }
                    let restore_ms = restore_start.elapsed().as_millis();
                    let query = &journal.queries[local];
                    // The severity the original invocation would have reported
                    // this failure at, so a recommends recheck stays a warning.
                    let level = query.level;
                    set_rlimit(air, query.rlimit);
                    // With replay on, each check saves its instantiations
                    // under the query's certificate key.
                    let replay_key =
                        air.instantiation_replay().then(|| bucket.cert_keys[id.0].clone());
                    let diagnostics = QueryDiagnostics::default();
                    let start = Instant::now();
                    // Certificate first: once this query has saved
                    // instantiations, here or in an earlier session's
                    // exported certificate, check with them alone. `:only`
                    // lets no strategy run, so the solver answers from the
                    // replayed instances, each an instance of a formula this
                    // scope asserts, and a valid answer is sound. Any other
                    // answer is discarded, with its diagnostics, before the
                    // ordinary check.
                    let mut certified = None;
                    let mut attempted = None;
                    let certificate = replay_key.as_ref().and_then(|key| {
                        if air.has_saved_instantiations(key) {
                            return Some((key.clone(), None));
                        }
                        // A file that is not exactly a certificate for this
                        // key is never sent: it could assert anything.
                        let path = cert_dir.as_ref()?.join(format!("{key}.smt2"));
                        let text = read_certificate(&path)?;
                        let import = ImportInstantiations::parse(&text, key)?;
                        Some((key.clone(), Some(import)))
                    });
                    if let Some((key, import)) = certificate {
                        let source = match import {
                            Some(_) => CertificateSource::Imported,
                            None => CertificateSource::Session,
                        };
                        air.set_restore_instantiations(Some(key), true);
                        air.set_import_instantiations(import);
                        let attempt = air.check_valid(
                            &VirMessageInterface {},
                            &QueryDiagnostics::default(),
                            &query.query,
                            QueryContext::default(),
                        );
                        air.set_restore_instantiations(None, false);
                        air.set_import_instantiations(None);
                        drop(air.take_provenance());
                        drop(air.take_unknown_reason());
                        drop(air.take_matching_loops());
                        drop(air.take_inst_pressure());
                        match attempt {
                            ValidityResult::Valid(usage) => {
                                certified = Some(ValidityResult::Valid(usage))
                            }
                            ValidityResult::TypeError(error) => {
                                return fatal(&mut output, io::Error::other(error.to_string()));
                            }
                            ValidityResult::UnexpectedOutput(error) => {
                                return fatal(&mut output, io::Error::other(error));
                            }
                            _ => air.finish_query(),
                        }
                        attempted = Some(CertificateAttempt {
                            source,
                            closed: certified.is_some(),
                            elapsed_ms: start.elapsed().as_millis(),
                        });
                    }
                    let mut outcome = match certified {
                        Some(outcome) => outcome,
                        None => air.check_valid(
                            &VirMessageInterface {},
                            &diagnostics,
                            &query.query,
                            QueryContext::default(),
                        ),
                    };
                    // The response describes round zero. Later error searches
                    // replace AIR's provenance, even when their verdict differs.
                    let first_provenance = air.take_provenance();
                    let first_unknown_reason = air.take_unknown_reason();
                    let first_matching_loops = air.take_matching_loops();
                    // Sessions do not report instantiation pressure yet.
                    drop(air.take_inst_pressure());
                    // Ask for further errors exactly as far as the original
                    // invocation did, so rechecking a function with several
                    // failing assertions reports the same ones rather than
                    // only the first. Mirrors `check_result_validity`.
                    let mut checks_remaining = multiple_errors;
                    let mut only_check_earlier = false;
                    let mut verdict = None;
                    let mut assert_id = None;
                    loop {
                        match outcome {
                            ValidityResult::Valid(_) => {
                                verdict.get_or_insert(QueryResult::Valid);
                                break;
                            }
                            ValidityResult::Canceled => {
                                // On the first round the verdict carries this.
                                // On a later one the verdict is already
                                // `invalid`, so without the diagnostic the
                                // caller cannot tell a complete error list from
                                // one the rlimit cut short. The batch run
                                // reports it on every round, and so does this.
                                // It omits the batch's `--profile` hint, which
                                // is a rerun the caller of a session does not
                                // make.
                                diagnostics.bare(
                                    level.into(),
                                    format!(
                                        "{}: Resource limit (rlimit) exceeded",
                                        query.context.desc
                                    ),
                                    &query.context.span.as_string,
                                );
                                verdict.get_or_insert(QueryResult::ResourceLimit);
                                break;
                            }
                            // A failure the solver gave no model for cannot be
                            // localised any further: `check_valid_again` panics
                            // on it rather than reporting it, so this must stop
                            // where `check_result_validity` stops.
                            ValidityResult::Invalid(None, error, id)
                            | ValidityResult::Invalid(_, error @ None, id) => {
                                match error {
                                    Some(error) => diagnostics.record(&error, level),
                                    // Nothing came back to describe the
                                    // failure. Name the obligation, as the
                                    // batch run does.
                                    None => diagnostics.bare(
                                        level.into(),
                                        query.context.desc.clone(),
                                        &query.context.span.as_string,
                                    ),
                                }
                                if verdict.is_none() {
                                    verdict = Some(QueryResult::Invalid);
                                    assert_id = id.map(|id| (*id).clone());
                                }
                                break;
                            }
                            ValidityResult::Invalid(_, error, id) => {
                                if let Some(error) = error {
                                    diagnostics.record(&error, level);
                                }
                                // Later rounds only add diagnostics: the
                                // verdict and the reported assertion stay
                                // those of the first failure.
                                if verdict.is_none() {
                                    verdict = Some(QueryResult::Invalid);
                                    assert_id = id.map(|id| (*id).clone());
                                }
                                if multiple_errors == 0 {
                                    break;
                                }
                                if !only_check_earlier {
                                    checks_remaining -= 1;
                                    only_check_earlier = checks_remaining == 0;
                                }
                                outcome = air.check_valid_again(
                                    &diagnostics,
                                    only_check_earlier,
                                    QueryContext::default(),
                                );
                                drop(air.take_provenance());
                                drop(air.take_matching_loops());
                                drop(air.take_inst_pressure());
                            }
                            ValidityResult::TypeError(error) => {
                                return fatal(&mut output, io::Error::other(error.to_string()));
                            }
                            ValidityResult::UnexpectedOutput(error) => {
                                return fatal(&mut output, io::Error::other(error));
                            }
                        }
                    }
                    let result = verdict.expect("every path out of the loop sets a verdict");
                    // The batch run guards this on the level and the counter
                    // alone, so at `--multiple-errors 0`, where the counter
                    // starts spent, it says the search was cut short even for a
                    // query that passed. Requiring a failure is a deliberate
                    // departure: a caller diffing a session against that run
                    // sees the note only where errors were actually withheld.
                    if matches!(result, QueryResult::Invalid)
                        && level == MessageLevel::Error
                        && checks_remaining == 0
                    {
                        diagnostics.bare(
                            DiagnosticLevel::Note,
                            format!(
                                "{}: not all errors may have been reported; rerun with a higher value for --multiple-errors to find other potential errors in this function",
                                query.context.desc
                            ),
                            &query.context.span.as_string,
                        );
                    }
                    let provenance = first_provenance.and_then(|info| {
                        bucket.symbols.as_ref().map(|symbols| {
                            symbols.resolve(
                                &query.context.fun,
                                crate::provenance::QueryProvenance {
                                    desc: query.context.desc.clone(),
                                    span: query.context.span.as_string.clone(),
                                    round: 0,
                                    result: match result {
                                        QueryResult::Valid => "valid",
                                        QueryResult::Invalid => "invalid",
                                        QueryResult::ResourceLimit => "canceled",
                                    }
                                    .to_owned(),
                                    sources: info.sources,
                                    instantiations: info.instantiations,
                                    variable_versions: info.variable_versions,
                                    unparsed: info.unparsed,
                                },
                            )
                        })
                    });
                    let unknown_reason = first_unknown_reason.map(|reason| {
                        bucket.quantifiers.resolve_unknown(
                            &query.context.desc,
                            &query.context.span.as_string,
                            reason,
                        )
                    });
                    let matching_loops = first_matching_loops.and_then(|info| {
                        bucket.symbols.as_ref().map(|symbols| {
                            symbols.resolve_matching_loops(
                                &query.context.fun,
                                crate::provenance::QueryMatchingLoops {
                                    desc: query.context.desc.clone(),
                                    span: query.context.span.as_string.clone(),
                                    round: 0,
                                    result: match result {
                                        QueryResult::Valid => "valid",
                                        QueryResult::Invalid => "invalid",
                                        QueryResult::ResourceLimit => "canceled",
                                    }
                                    .to_owned(),
                                    info,
                                },
                            )
                        })
                    });
                    // Only a proof is worth keeping. A failed check's instances
                    // are no certificate, and saving them would replace one
                    // that still closes the query once the failing edit is
                    // undone. Every path here came from a solver answer, so
                    // the save has a result to read from.
                    if let Some(key) =
                        replay_key.as_ref().filter(|_| matches!(result, QueryResult::Valid))
                    {
                        air.save_instantiations(key);
                        if let Some(dir) = &cert_dir {
                            write_certificate(air, dir, key);
                        }
                    }
                    air.finish_query();
                    send(
                        &mut output,
                        &Response::Checked {
                            session,
                            bucket: bucket_id,
                            query: id,
                            result,
                            assert_id,
                            diagnostics: diagnostics.0.into_inner(),
                            elapsed_ms: start.elapsed().as_millis(),
                            restore_ms,
                            provenance: provenance.as_ref(),
                            unknown_reason: unknown_reason.as_ref(),
                            matching_loops: matching_loops.as_ref(),
                            certificate: attempted,
                        },
                    )?;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use air::context::SmtSolver;
    use std::sync::Arc;

    fn commands(text: &str) -> Commands {
        let text = format!("({text})");
        let node = sise::parse_tree(&mut sise::Parser::new(&text)).unwrap();
        let sise::TreeNode::List(nodes) = node else { panic!("expected command list") };
        air::parser::Parser::new(Arc::new(VirMessageInterface {}))
            .nodes_to_commands(&nodes)
            .unwrap()
    }

    #[test]
    fn later_axioms_cannot_prove_an_earlier_query() {
        let mut air = Context::new(Arc::new(VirMessageInterface {}), SmtSolver::Cvc5);
        air.set_z3_param("air_recommended_options", "true");
        let diagnostics = QueryDiagnostics::default();
        let base = commands("(declare-const x Int)");
        let later = commands("(declare-const y Int) (axiom (= x y)) (axiom (= y 0))");
        let query = commands("(check-valid (assert (= x 0)))");
        let mut session = QueryJournal::new();
        for command in base.iter() {
            if let CommandX::Global(decl) = &**command {
                air.global(decl).unwrap();
            }
        }
        session.push_context(&mut air, later.clone()).unwrap();
        for command in later.iter() {
            if let CommandX::Global(decl) = &**command {
                air.global(decl).unwrap();
            }
        }
        // Repeated backwards/forwards jumps exercise both removal of axioms
        // and redeclaration of names removed with their scope.
        for (prefix, valid) in [(1, true), (0, false), (1, true), (0, false)] {
            session.restore_prefix(&mut air, prefix).unwrap();
            let result = air.command(
                &VirMessageInterface {},
                &diagnostics,
                &query[0],
                QueryContext::default(),
            );
            if valid {
                assert!(matches!(result, ValidityResult::Valid(_)), "{result:?}");
            } else {
                assert!(matches!(result, ValidityResult::Invalid(..)), "{result:?}");
            }
            air.finish_query();
        }
    }

    /// Apply a declaration batch the way the verifier does: retain it, then
    /// let AIR assert it into the scope the journal just chose.
    fn apply(journal: &mut QueryJournal, air: &mut Context, batch: &Commands) {
        journal.push_context(air, batch.clone()).unwrap();
        for command in batch.iter() {
            if let CommandX::Global(decl) = &**command {
                air.global(decl).unwrap();
            }
        }
    }

    #[test]
    fn declaration_batches_share_a_scope_until_a_query_pins_one() {
        let mut air = Context::new(Arc::new(VirMessageInterface {}), SmtSolver::Cvc5);
        air.set_z3_param("air_recommended_options", "true");
        let diagnostics = QueryDiagnostics::default();
        let base = commands("(declare-const x Int)");
        let first = commands("(declare-const y Int) (axiom (= y 0))");
        let second = commands("(declare-const z Int) (axiom (= z y))");
        let third = commands("(axiom (= x 5))");
        let mut journal = QueryJournal::new();
        for command in base.iter() {
            if let CommandX::Global(decl) = &**command {
                air.global(decl).unwrap();
            }
        }

        apply(&mut journal, &mut air, &first);
        apply(&mut journal, &mut air, &second);
        // No query separates these batches, so they share a single scope.
        assert_eq!(journal.applied, 1);
        assert_eq!(journal.contexts.len(), 1);
        assert_eq!(journal.contexts[0].len(), 2);

        // Stands in for record_query, which pins the prefix ending here.
        journal.recorded_in_scope = true;
        apply(&mut journal, &mut air, &third);
        assert_eq!(journal.applied, 2);
        assert_eq!(journal.contexts.len(), 2);

        // Grouping keeps both batches on the pinned side of the boundary, and
        // leaves the batch recorded after it on the other.
        let grouped = commands("(check-valid (assert (= z 0)))");
        let later = commands("(check-valid (assert (= x 5)))");
        for (prefix, query, valid) in
            [(2, &later, true), (1, &later, false), (1, &grouped, true), (2, &grouped, true)]
        {
            journal.restore_prefix(&mut air, prefix).unwrap();
            let result = air.command(
                &VirMessageInterface {},
                &diagnostics,
                &query[0],
                QueryContext::default(),
            );
            if valid {
                assert!(matches!(result, ValidityResult::Valid(_)), "prefix {prefix}: {result:?}");
            } else {
                assert!(
                    matches!(result, ValidityResult::Invalid(..)),
                    "prefix {prefix}: {result:?}"
                );
            }
            air.finish_query();
        }
    }

    fn reading(pairs: &[(&str, &str)]) -> EgraphReply {
        EgraphReply {
            equalities: pairs
                .iter()
                .map(|(lhs, rhs)| air::context::EgraphEquality {
                    lhs: lhs.to_string(),
                    rhs: rhs.to_string(),
                    level: "entailed".to_string(),
                    used: false,
                    used_by: Vec::new(),
                    focus: 1,
                    because: Vec::new(),
                    because_hidden: 0,
                })
                .collect(),
            ..EgraphReply::default()
        }
    }

    #[test]
    fn frontier_delta_counts_new_lost_and_merged_equalities() {
        // Every symbol reads as source, so no new equality is hidden.
        let recorded: SourceNames = ["a", "b", "c", "d", "e", "f", "e2", "f2"]
            .iter()
            .map(|x| (x.to_string(), vir::air_names::SourceName::Symbol(x.to_string())))
            .collect();
        let versions = VariableVersions::new();
        let names = QueryNames {
            symbols: None,
            shown: Cow::Borrowed(&recorded),
            plain: Cow::Borrowed(&recorded),
            versions: &versions,
        };
        // Three classes, {a, b}, {c, d} and {e, f}; the second reading loses the last.
        let before = reading(&[("a", "b"), ("c", "d"), ("e", "f")]);
        // Injecting a = b merged both classes; e and f went apart.
        let after = reading(&[("a", "b"), ("a", "c"), ("a", "d"), ("e", "e2"), ("f", "f2")]);
        let delta = frontier_delta(&before, &after, ("a", "b"), &names);
        assert_eq!(delta.new_equality_count, 4, "{delta:?}");
        assert_eq!(delta.classes_merged, 1, "{delta:?}");
        assert_eq!(delta.lost_equality_count, 1, "{delta:?}");
        assert!(delta.new_equalities.contains(&("a".to_string(), "c".to_string())));
        // Nothing changes when the second reading is the first.
        let same = frontier_delta(&before, &before, ("a", "b"), &names);
        assert_eq!(
            (same.new_equality_count, same.lost_equality_count, same.classes_merged),
            (0, 0, 0)
        );
    }

    fn equality(
        lhs: &str,
        rhs: &str,
        level: &str,
        used_by: &[&str],
    ) -> air::context::EgraphEquality {
        air::context::EgraphEquality {
            lhs: lhs.to_string(),
            rhs: rhs.to_string(),
            level: level.to_string(),
            used: !used_by.is_empty(),
            used_by: used_by.iter().map(|qid| qid.to_string()).collect(),
            focus: 1,
            because: Vec::new(),
            because_hidden: 0,
        }
    }

    /// Names as `Symbols::query_names` and `paste_names` give them, for a
    /// query where `z@0` and `z@1` are two assignments of `z`.
    fn versioned_names() -> (SourceNames, SourceNames, VariableVersions) {
        let symbol = |name: &str| vir::air_names::SourceName::Symbol(name.to_string());
        let mut plain: SourceNames =
            ["x", "y"].iter().map(|x| (x.to_string(), symbol(x))).collect();
        let mut shown = plain.clone();
        let mut versions = VariableVersions::new();
        for version in [0, 1] {
            let ssa = format!("z@{version}");
            plain.insert(ssa.clone(), symbol("z"));
            shown.insert(ssa.clone(), symbol(&format!("z (version {version})")));
            versions.insert(ssa, ("z".to_string(), version));
        }
        (plain, shown, versions)
    }

    #[test]
    fn pasted_asserts_need_entailment_and_one_version_per_variable() {
        let (plain, shown, versions) = versioned_names();
        let names = QueryNames {
            symbols: None,
            shown: Cow::Borrowed(&shown),
            plain: Cow::Borrowed(&plain),
            versions: &versions,
        };
        assert_eq!(
            names.verus_assert(&equality("z@1", "(+ x 1)", "entailed", &[])).as_deref(),
            Some("assert(z == (x + 1));")
        );
        // `z == (z + 1)` would paste one name for two assignments.
        assert_eq!(names.verus_assert(&equality("z@1", "(+ z@0 1)", "entailed", &[])), None);
        // Holds only in the model the search ended on.
        assert_eq!(names.verus_assert(&equality("z@1", "x", "decision", &[])), None);
        // `tmp` renders as no source.
        assert_eq!(names.verus_assert(&equality("z@1", "tmp", "entailed", &[])), None);
    }

    #[test]
    fn differently_spelled_duplicates_merge_whichever_comes_first() {
        let (plain, shown, versions) = versioned_names();
        let names = QueryNames {
            symbols: None,
            shown: Cow::Borrowed(&shown),
            plain: Cow::Borrowed(&plain),
            versions: &versions,
        };
        // The same equality in two spellings, as between a boxed and an
        // unboxed term; only the second has a quantifier instantiated with it.
        let unused = equality("x", "y", "entailed", &[]);
        let used = equality("y", "x", "entailed", &["user_q"]);
        for pairs in [[&unused, &used], [&used, &unused]] {
            let reply = EgraphReply {
                equalities: pairs.iter().map(|e| (*e).clone()).collect(),
                ..EgraphReply::default()
            };
            let (listed, hidden) = names.resolve(&reply);
            assert_eq!((listed.len(), hidden), (1, 1));
            assert!(listed[0].used_by_proof);
            assert_eq!(listed[0].used_by, vec!["user_q"]);
        }
    }

    #[test]
    fn equality_ids_name_the_terms_in_order() {
        assert_eq!(equality_id("(f b)", "c"), equality_id("(f b)", "c"));
        assert_ne!(equality_id("(f b)", "c"), equality_id("c", "(f b)"));
        // The separator keeps a split point from moving between the sides.
        assert_ne!(equality_id("ab", "c"), equality_id("a", "bc"));
        assert!(equality_id("x", "y").starts_with("eq#"));
    }

    /// A query's certificate names formulas of its prefix, and those mention
    /// AIR's generated helpers, so replaying a popped prefix must name them as
    /// building it did.
    #[test]
    fn replayed_prefix_reproduces_generated_names() {
        #[derive(Clone, Default)]
        struct Log(Arc<std::sync::Mutex<Vec<u8>>>);
        impl std::io::Write for Log {
            fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
                self.0.lock().unwrap().extend_from_slice(bytes);
                Ok(bytes.len())
            }
            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }
        // The generated helpers `bytes` declares, in order.
        fn helpers(bytes: &[u8]) -> Vec<String> {
            String::from_utf8(bytes.to_vec())
                .unwrap()
                .lines()
                .map(|line| line.trim_start())
                .filter(|line| {
                    line.starts_with("(declare-fun %%") || line.starts_with("(declare-const %%")
                })
                .map(|line| line.split_whitespace().nth(1).unwrap().to_string())
                .collect()
        }
        let log = Log::default();
        let mut air = Context::new(Arc::new(VirMessageInterface {}), SmtSolver::Z3);
        air.set_smt_log(Box::new(log.clone()));
        let first = commands("(axiom (= 10 (apply Int (lambda ((x Int) (y Int)) (+ x y 5)) 2 3)))");
        let second = commands(
            "(declare-fun g (Int) Bool)
             (axiom (g 4))
             (axiom (= 20 (apply Int (array 10 20 30) 1)))
             (axiom (g (choose ((x Int)) (! (g x) :pattern ((g x))) x)))",
        );
        let mut journal = QueryJournal::new();
        apply(&mut journal, &mut air, &first);
        // Stands in for record_query, which pins the prefix ending here.
        journal.recorded_in_scope = true;
        apply(&mut journal, &mut air, &second);
        let built = helpers(&log.0.lock().unwrap());
        for helper in ["%%lambda%%", "%%apply%%", "%%array%%", "%%choose%%"] {
            assert!(built.iter().any(|name| name.starts_with(helper)), "{built:?}");
        }
        let mark = log.0.lock().unwrap().len();
        journal.restore_prefix(&mut air, 0).unwrap();
        journal.restore_prefix(&mut air, 2).unwrap();
        let replayed = helpers(&log.0.lock().unwrap()[mark..]);
        assert_eq!(built, replayed);
    }

    #[test]
    fn oversized_request_closes_without_parsing_its_suffix() {
        let mut session = Server::new(
            Vec::new(),
            SessionInfo {
                provenance: false,
                matching_loops: false,
                spinoff_all: false,
                multiple_errors: 2,
                input_files: Vec::new(),
                smt_options: Vec::new(),
                instantiation_replay: false,
            },
        );
        let input = format!("{}\n{{\"command\":\"list\"}}\n", " ".repeat(65537));
        let mut output = Vec::new();
        let error =
            session.run("test", true, input.as_bytes(), &mut output, |_, _| {}).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        // `ready`, then the refusal. The suffix of the oversized line is never
        // taken for a second request, so no `queries` reply appears.
        let output = String::from_utf8(output).unwrap();
        assert_eq!(output.lines().count(), 2, "{output}");
        assert!(!output.contains("\"queries\""), "{output}");
        assert!(output.lines().nth(1).unwrap().contains("64 KiB"), "{output}");
    }
}
