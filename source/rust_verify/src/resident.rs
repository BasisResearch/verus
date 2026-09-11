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
//!
//! `ready.smt_options` echoes the ordered name/value pairs already applied at
//! solver startup. Rechecks preserve those settings in the original contexts;
//! only the recorded per-query resource budget is set again before a check.

use crate::buckets::BucketId;
use crate::commands::{QueryOp, Style};
use air::ast::{CommandX, Commands, Query};
use air::context::{Context, QueryContext, ValidityResult};
use air::messages::{ArcDynMessage, Diagnostics, MessageLevel};
use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::io::{self, BufRead, Read, Write};
use std::sync::Mutex;
use std::time::{Instant, SystemTime, UNIX_EPOCH};
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
    List { session: Option<String> },
    Check { session: String, bucket: BucketIndex, query: QueryId },
    Close { session: String },
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
        Self { id, queries, addresses, cert_keys, state: Mutex::new(states), symbols }
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

/// Export what `key` saved to `<dir>/<key>.smt2`, where a later session's
/// solver can import it. Written beside and renamed into place, so a reader
/// never sees half a file; a failure only costs a later session its
/// certificate.
fn write_certificate(air: &mut Context, dir: &std::path::Path, key: &str) {
    let lines = air.export_instantiations(key);
    if lines.iter().any(|line| line.starts_with("(error")) {
        return;
    }
    let text: Vec<&str> =
        lines.iter().map(String::as_str).filter(|line| !line.starts_with(';')).collect();
    let path = dir.join(format!("{key}.smt2"));
    let partial = dir.join(format!("{key}.smt2.partial"));
    if std::fs::write(&partial, text.join("\n")).is_ok() {
        let _ = std::fs::rename(&partial, &path);
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
    pub(crate) spinoff_all: bool,
    /// How many errors one query may report, as `--multiple-errors` set it. A
    /// recheck looks for as many as the original invocation did.
    pub(crate) multiple_errors: u32,
    pub(crate) input_files: Vec<String>,
    /// The ordered startup settings. They already live in every retained
    /// solver and must not be reapplied after initialization.
    pub(crate) smt_options: Vec<(String, String)>,
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
        spinoff_all: bool,
        smt_options: &'a [(String, String)],
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
    },
    Error {
        message: &'a str,
    },
    Closed {
        session: &'a str,
    },
}

#[derive(Serialize)]
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
                spinoff_all: self.info.spinoff_all,
                smt_options: &self.info.smt_options,
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
                    let certificate = replay_key.as_ref().and_then(|key| {
                        if air.has_saved_instantiations(key) {
                            return Some((key.clone(), None));
                        }
                        let path = cert_dir.as_ref()?.join(format!("{key}.smt2"));
                        std::fs::read_to_string(path).ok().map(|text| (key.clone(), Some(text)))
                    });
                    if let Some((key, import)) = certificate {
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
                    // Every path here came from a solver answer, so the save
                    // has a result to read from.
                    if let Some(key) = &replay_key {
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

    #[test]
    fn oversized_request_closes_without_parsing_its_suffix() {
        let mut session = Server::new(
            Vec::new(),
            SessionInfo {
                provenance: false,
                spinoff_all: false,
                multiple_errors: 2,
                input_files: Vec::new(),
                smt_options: Vec::new(),
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
