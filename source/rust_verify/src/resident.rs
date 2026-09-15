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
//! Under `-V difficulty`, `ready.difficulty` is true and every check carries its
//! source-resolved `difficulty`: round zero's gradient, since that is the round
//! the response describes.
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
//!
//! A `speculate` request checks a retained query as usual, observed for
//! matching loops, then again with one hypothesis about quantifier
//! instantiation sent in the query's own scope: instantiate a quantifier at
//! given terms, give it one more trigger, or refuse its instantiations that
//! match a fingerprint (see `air::speculate`). cvc5 holds the hypothesis in
//! that scope's user context, which the check pops. The reply says whether
//! the hypothesis closed the query (it failed without it, and again right
//! after), whether it introduced a matching loop, and what source to paste.
//! No probe verdict is a `checked` one, and no probe saves a certificate.

use crate::buckets::BucketId;
use crate::commands::{QueryOp, Style};
use air::ast::{CommandX, Commands, Decl, DeclX, Query};
use air::context::{
    Context, EgraphReply, EgraphRequest, QueryContext, SmtSolver, ValidityResult, VariableVersions,
};
use air::inst_graph::{GraphFilter, GraphOp, GraphReply, GraphSummary, Site};
use air::instantiations::ImportInstantiations;
use air::messages::{ArcDynMessage, Diagnostics, MessageLevel};
use air::profiler::InstantiationGraph;
use air::speculate::{Hypothesis, QuantifierSmt, SpeculationReply, SpeculationRequest};
use serde::{Deserialize, Serialize};
use sise::TreeNode;
use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
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
    /// What the diagnostic records call this kind of check. The batch run
    /// reads the same name off the `QueryOp` (`QueryOp::kind`), and
    /// `kind_names_match_the_batch_run` holds the two together.
    fn name(self) -> &'static str {
        match self {
            Self::Termination => "termination",
            Self::Body => "body",
            Self::RecommendsFollowup => "recommends",
            Self::Recommends => "recommends_checked",
            Self::Expanded => "expanded",
            Self::ApiSafety => "api_safety",
        }
    }

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
    /// The declarations the solver held before the journal's first scope
    /// (the bucket's fuel, traits, datatypes and function declarations, or a
    /// spun-off query's whole context). Kept only to be read: they sit below
    /// every scope, so they are never replayed.
    base: Vec<Commands>,
}

/// The requests this worker serves, as `ready` reports them. A client reads
/// the list rather than guessing from `protocol`: requests reach releases in
/// their own order, and a worker that does not know a request answers exactly
/// as it does a malformed one. Every `Request` variant belongs here, in the
/// protocol's snake case, which `resident_ready_lists_the_requests_it_serves`
/// checks by sending each one.
const COMMANDS: &[&str] =
    &["list", "check", "bisect", "egraph", "scaffold", "close", "inst_graph", "speculate"];

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
    /// Probe the query with parts of it switched off (see `air::bisect`).
    Bisect {
        session: String,
        bucket: BucketIndex,
        query: QueryId,
        mode: BisectMode,
        /// Flip mode only. Default: `not_valid` for a valid query, else `valid`.
        target: Option<BisectTarget>,
        /// At most this many probes, 1..=`MAX_BISECT_CHECKS`.
        budget_checks: Option<usize>,
        /// Which kinds of unit may be removed (flip) or kept (core). Default:
        /// every kind for a `valid` or `changed` flip, hypotheses and facts
        /// otherwise, since removing a goal cannot break a proof.
        kinds: Option<Vec<BisectKind>>,
        /// Only units whose `AssertId` starts with this prefix.
        under: Option<Vec<u64>>,
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
    /// Check the query as usual, then again with one hypothesis about
    /// quantifier instantiation in its scope (see `air::speculate`).
    Speculate {
        session: String,
        bucket: BucketIndex,
        query: QueryId,
        /// Without one, the query is checked once and the quantifiers
        /// written in source that its scope asserts are listed.
        #[serde(default)]
        hypothesis: Option<HypothesisRequest>,
        /// The rounds in which a quantifier's instantiating terms get
        /// deeper that make a matching loop, 1 to `MAX_LOOP_THRESHOLD`;
        /// cvc5's default (5) when absent.
        #[serde(default)]
        loop_threshold: Option<u32>,
    },
    /// Try a proposed assertion `P` at one goal of the query: is `P`
    /// provable there, and does the goal hold once `P` is assumed there
    /// (see `air::scaffold`). Each check runs in the query's own scope.
    Scaffold {
        session: String,
        bucket: BucketIndex,
        query: QueryId,
        /// `P` as Verus source: `P`, `assert(P)` or `assert(P);`.
        assert: String,
        /// The goal to place `P` before, by assert id. Default: the goal the
        /// query's own check fails at first.
        assert_id: Option<Vec<u64>>,
        /// The goal by its index among the query's asserts (`target.goal` of
        /// a reply, or a refusal's list), for one without an assert id, such
        /// as a loop invariant at the end of the loop body. `assert_id` wins
        /// when both are given.
        #[serde(default)]
        goal: Option<usize>,
        /// Skip the check of `P` itself, when it is known to hold.
        #[serde(default)]
        goal_only: bool,
    },
    Close {
        session: String,
    },
    /// Query the instantiation graph the last check of this query recorded.
    /// `path` needs `to_inst`, and starts from `from_qid` or else a root.
    InstGraph {
        session: String,
        bucket: BucketIndex,
        query: QueryId,
        op: GraphOpName,
        #[serde(default)]
        filter: GraphFilterRequest,
        from_qid: Option<String>,
        to_inst: Option<u64>,
        /// How many items the answer lists at most: 1 to 1000, default 20.
        limit: Option<usize>,
    },
}

#[derive(Clone, Copy, Deserialize)]
#[serde(rename_all = "snake_case")]
enum GraphOpName {
    Cycles,
    TopCost,
    Subgraph,
    Path,
    Growth,
}

/// Which instantiations an `inst_graph` request looks at. Every given field
/// restricts them further.
#[derive(Default, Deserialize)]
#[serde(deny_unknown_fields)]
struct GraphFilterRequest {
    /// Only instantiations of this `:qid`.
    quantifier: Option<String>,
    /// Only quantifiers owned at this path or inside it, by whole segments:
    /// a function's, or for internal axioms a datatype's, trait's or impl's.
    source_fn: Option<String>,
    min_depth: Option<u64>,
}

#[derive(Clone, Copy, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
enum BisectMode {
    Flip,
    Core,
}

#[derive(Clone, Copy, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
enum BisectTarget {
    Valid,
    NotValid,
    Changed,
}

#[derive(Clone, Copy, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum BisectKind {
    Hypothesis,
    Goal,
    Fact,
}

impl BisectKind {
    fn of(kind: air::bisect::UnitKind) -> Self {
        match kind {
            air::bisect::UnitKind::Hypothesis => Self::Hypothesis,
            air::bisect::UnitKind::Goal => Self::Goal,
            air::bisect::UnitKind::Fact => Self::Fact,
        }
    }
}

const DEFAULT_BISECT_CHECKS: usize = 24;
const MAX_BISECT_CHECKS: usize = 256;

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

/// The largest `inst_graph` reply sent. A larger answer is refused with an
/// error instead: a caller that caps replies (the MCP client, at 16 MiB)
/// would otherwise take it for a dead worker and end the session.
const MAX_GRAPH_REPLY_BYTES: usize = 8 << 20;

/// The most instantiations a session's kept graphs hold together: about ten
/// graphs at the solver's per-check cap (`--inst-graph-max=100000`). A graph at
/// the cap takes about 34 MB, so without a budget a session that checks many
/// looping queries would grow without bound.
const MAX_KEPT_INSTANTIATIONS: usize = 1_000_000;

/// Each query's instantiation graph from its last check, keyed by (bucket,
/// query). Past `budget` instantiations in all, the graphs least recently
/// checked or queried are dropped, never the one just kept.
struct KeptGraphs {
    graphs: HashMap<(usize, usize), (InstantiationGraph, u64)>,
    budget: usize,
    total: usize,
    clock: u64,
}

impl KeptGraphs {
    fn new(budget: usize) -> Self {
        Self { graphs: HashMap::new(), budget, total: 0, clock: 0 }
    }

    fn tick(&mut self) -> u64 {
        self.clock += 1;
        self.clock
    }

    fn insert(&mut self, key: (usize, usize), graph: InstantiationGraph) {
        self.remove(&key);
        self.total += graph.nodes.len();
        let used = self.tick();
        self.graphs.insert(key, (graph, used));
        while self.total > self.budget {
            let oldest = self
                .graphs
                .iter()
                .filter(|(other, _)| **other != key)
                .min_by_key(|(_, (_, used))| *used)
                .map(|(other, _)| *other);
            let Some(oldest) = oldest else { break };
            self.remove(&oldest);
        }
    }

    fn remove(&mut self, key: &(usize, usize)) {
        if let Some((graph, _)) = self.graphs.remove(key) {
            self.total -= graph.nodes.len();
        }
    }

    fn get(&mut self, key: &(usize, usize)) -> Option<&InstantiationGraph> {
        let used = self.tick();
        let (graph, last) = self.graphs.get_mut(key)?;
        *last = used;
        Some(graph)
    }
}

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
    /// (bucket, query) -> the instantiation graph of its last check, when
    /// the solvers record them, within `MAX_KEPT_INSTANTIATIONS`. Queries
    /// read these; they never reach the solver, so they cannot change its
    /// state.
    graphs: KeptGraphs,
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
    /// Whether the retained solvers track per-assertion difficulty and unsat
    /// cores for `(get-info :difficulty-gradient)` (`-V difficulty`).
    pub(crate) difficulty: bool,
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
    /// Whether cvc5 solvers were launched recording instantiation graphs
    /// (`VERUS_RESIDENT_INST_GRAPH`), so each check keeps its graph.
    pub(crate) inst_graph: bool,
}

#[derive(Serialize)]
#[serde(tag = "event", rename_all = "snake_case")]
enum Response<'a> {
    Ready {
        protocol: u32,
        /// The requests this worker serves; see `COMMANDS`.
        commands: &'a [&'a str],
        session: &'a str,
        process_id: u32,
        invocation_succeeded: bool,
        provenance: bool,
        matching_loops: bool,
        difficulty: bool,
        spinoff_all: bool,
        smt_options: &'a [(String, String)],
        instantiation_replay: bool,
        inst_graph: bool,
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
        /// Round zero's difficulty gradient, under `-V difficulty`.
        difficulty: Option<&'a crate::provenance::ResolvedQueryDifficulty>,
        /// Present when this check tried a certificate before searching.
        certificate: Option<CertificateAttempt>,
        /// The size of the instantiation graph this check kept, in a
        /// session that records them.
        inst_graph: Option<GraphSummary>,
        /// Why a session that records graphs kept none for this check.
        inst_graph_error: Option<String>,
    },
    InstGraph {
        session: &'a str,
        bucket: BucketIndex,
        query: QueryId,
        result: &'a GraphReply,
    },
    Bisected {
        session: &'a str,
        bucket: BucketIndex,
        query: QueryId,
        #[serde(flatten)]
        report: BisectReport,
    },
    Egraph {
        session: &'a str,
        bucket: BucketIndex,
        query: QueryId,
        #[serde(flatten)]
        outcome: Box<EgraphOutcome>,
    },
    Speculated {
        session: &'a str,
        bucket: BucketIndex,
        query: QueryId,
        #[serde(flatten)]
        outcome: Box<SpeculationOutcome>,
    },
    Scaffold {
        session: &'a str,
        bucket: BucketIndex,
        query: QueryId,
        #[serde(flatten)]
        report: Box<ScaffoldReport>,
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

/// A solver answer to one bisect probe.
#[derive(Serialize)]
struct ProbeVerdict {
    /// `valid` (unsat), `invalid` (sat) or `unknown`
    result: &'static str,
    /// the solver's reason for `unknown`, such as `resourceout` or `incomplete`
    #[serde(skip_serializing_if = "Option::is_none")]
    reason: Option<String>,
}

impl From<&air::bisect::Answer> for ProbeVerdict {
    fn from(answer: &air::bisect::Answer) -> Self {
        Self { result: answer.result(), reason: answer.reason().map(str::to_owned) }
    }
}

/// One switchable part of a query, joined back to source.
#[derive(Serialize)]
struct BisectUnit {
    /// Position among the query's units; probes name units by it.
    index: usize,
    kind: BisectKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    assert_id: Option<Vec<u64>>,
    /// A hypothesis's kind (`requires`, `type_invariant`, `fuel`,
    /// `trait_bound`); a goal's or fact's error message, such as
    /// `assertion failed` or `precondition not satisfied`.
    description: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    span: Option<String>,
    /// The message's labels, such as the callee `requires` a precondition
    /// goal is about.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    labels: Vec<SourceLabel>,
}

#[derive(Serialize)]
struct BisectProbe {
    /// How many units the probe switched off.
    removed: usize,
    /// Which ones, by their `index` among the query's units.
    removed_units: Vec<usize>,
    verdict: ProbeVerdict,
}

/// The reply to a bisect request. Every verdict after `verdict_before`
/// describes a weaker query than the original, never the original itself.
#[derive(Serialize)]
struct BisectReport {
    mode: BisectMode,
    /// The flip target searched for, after defaulting.
    #[serde(skip_serializing_if = "Option::is_none")]
    target: Option<BisectTarget>,
    /// `found`, `already_at_target`, `unreachable`, `not_valid`,
    /// `no_candidates` or `budget_exhausted`.
    status: &'static str,
    /// The probe with nothing removed. It can differ from an ordinary check
    /// near the resource limit: hypotheses are guarded, so the solver cannot
    /// substitute them away.
    verdict_before: Option<ProbeVerdict>,
    /// Flip: the units whose removal reaches the target. Core: the units that
    /// have to stay for the query to remain valid when every other candidate
    /// is removed.
    minimal_statement_ids: Vec<BisectUnit>,
    /// The probe of that configuration; null unless `status` is `found`.
    verdict_after_removal: Option<ProbeVerdict>,
    /// The probe with every candidate removed, when the search ran it. For
    /// `unreachable` it is what removing everything answered.
    verdict_all_removed: Option<ProbeVerdict>,
    /// Whether restoring (flip) or removing (core) any one member was probed
    /// and loses the result. False when the budget ran out first.
    minimal: bool,
    /// The set was found by trying units one at a time, because removing
    /// every candidate did not reach the target.
    non_monotone: bool,
    checks_used: usize,
    budget_checks: usize,
    /// Units the search could remove (flip) or keep (core).
    candidates: usize,
    units: usize,
    /// Every `AssertId` in the query has one component, so splitting by id
    /// prefix is splitting a flat list.
    flat_ids: bool,
    probes: Vec<BisectProbe>,
    elapsed_ms: u128,
    restore_ms: u128,
}

struct BisectRequest {
    mode: BisectMode,
    target: Option<BisectTarget>,
    budget: usize,
    kinds: Option<Vec<BisectKind>>,
    under: Option<Vec<u64>>,
}

/// Run one bisect over `query` in `air`, which must be at the query's prefix
/// with its budget set. The probes' scope is popped before this returns.
fn bisect(
    air: &mut Context,
    query: &RetainedQuery,
    symbols: Option<&crate::provenance::Symbols>,
    request: BisectRequest,
) -> io::Result<BisectReport> {
    use air::bisect::{Answer, Mode, Status, Target, UnitKind};
    let mut prober =
        air.bisect_query(&query.query).map_err(|error| io::Error::other(error.to_string()))?;
    let count = prober.units().len();
    let before = prober.probe(&vec![false; count]).map_err(io::Error::other)?;
    let target = match request.mode {
        BisectMode::Core => None,
        BisectMode::Flip => Some(request.target.unwrap_or(if before == Answer::Valid {
            BisectTarget::NotValid
        } else {
            BisectTarget::Valid
        })),
    };
    let mode = match target {
        None => Mode::Core,
        Some(BisectTarget::Valid) => Mode::Flip(Target::Valid),
        Some(BisectTarget::NotValid) => Mode::Flip(Target::NotValid),
        Some(BisectTarget::Changed) => Mode::Flip(Target::Changed),
    };
    let kinds = request.kinds.unwrap_or_else(|| match mode {
        Mode::Flip(Target::Valid | Target::Changed) => {
            vec![BisectKind::Hypothesis, BisectKind::Goal, BisectKind::Fact]
        }
        Mode::Flip(Target::NotValid) | Mode::Core => {
            vec![BisectKind::Hypothesis, BisectKind::Fact]
        }
    });
    let units = prober.units().to_vec();
    let under = request.under.map(|prefix| air::bisect::units_under_prefix(&units, &prefix));
    let candidates: Vec<usize> = (0..count)
        .filter(|&i| kinds.contains(&BisectKind::of(units[i].kind)))
        .filter(|i| under.as_ref().is_none_or(|under| under.contains(i)))
        .collect();
    let outcome = air::bisect::search(
        mode,
        count,
        &candidates,
        request.budget,
        Some(before),
        &mut |disabled| prober.probe(disabled),
    )
    .map_err(io::Error::other)?;
    drop(prober);

    let fun = &query.context.fun;
    let describe = |index: usize| {
        let unit = &units[index];
        let (description, span, labels) = match unit.kind {
            UnitKind::Hypothesis => {
                let found = match &unit.tag {
                    Some(air::def::ProvenanceTag::Hyp(air::def::HypId(k))) => {
                        symbols.and_then(|symbols| symbols.hypothesis(fun, *k))
                    }
                    _ => None,
                };
                match found {
                    Some((kind, span)) => (kind.to_owned(), Some(span.to_owned()), Vec::new()),
                    None => ("hypothesis".to_owned(), None, Vec::new()),
                }
            }
            UnitKind::Goal | UnitKind::Fact => {
                match unit.error.as_ref().and_then(|e| e.downcast_ref::<MessageX>()) {
                    Some(message) => (
                        message.note.clone(),
                        message.spans.first().map(|s| s.as_string.clone()),
                        message
                            .labels
                            .iter()
                            .map(|label| SourceLabel {
                                message: label.note.clone(),
                                span: label.span.as_string.clone(),
                            })
                            .collect(),
                    ),
                    None => (String::new(), None, Vec::new()),
                }
            }
        };
        BisectUnit {
            index,
            kind: BisectKind::of(unit.kind),
            assert_id: unit.assert_id.as_ref().map(|id| (**id).clone()),
            description,
            span,
            labels,
        }
    };
    Ok(BisectReport {
        mode: request.mode,
        target,
        status: match outcome.status {
            Status::Found => "found",
            Status::AlreadyAtTarget => "already_at_target",
            Status::Unreachable => "unreachable",
            Status::NotValid => "not_valid",
            Status::NoCandidates => "no_candidates",
            Status::BudgetExhausted => "budget_exhausted",
        },
        verdict_before: outcome.before.as_ref().map(ProbeVerdict::from),
        minimal_statement_ids: outcome.set.iter().map(|&i| describe(i)).collect(),
        verdict_after_removal: outcome.after.as_ref().map(ProbeVerdict::from),
        verdict_all_removed: outcome.all_removed.as_ref().map(ProbeVerdict::from),
        minimal: outcome.minimal,
        non_monotone: outcome.non_monotone,
        checks_used: outcome.probes.len(),
        budget_checks: request.budget,
        candidates: candidates.len(),
        units: count,
        flat_ids: units.iter().all(|u| u.assert_id.as_ref().is_none_or(|id| id.len() <= 1)),
        probes: outcome
            .probes
            .iter()
            .map(|p| BisectProbe {
                removed: p.disabled.len(),
                removed_units: p.disabled.clone(),
                verdict: (&p.answer).into(),
            })
            .collect(),
        elapsed_ms: 0,
        restore_ms: 0,
    })
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
    /// the equality says: it is entailed, and both sides paste as source.
    fn verus_assert(&self, equality: &air::context::EgraphEquality) -> Option<String> {
        if equality.level != "entailed" || !self.pasteable(&[&equality.lhs, &equality.rhs]) {
            return None;
        }
        Some(format!(
            "assert({} == {});",
            self.render_plain(&equality.lhs),
            self.render_plain(&equality.rhs)
        ))
    }

    /// Whether `terms` paste as source together: each renders as source, and
    /// no variable appears in them at two assignment versions, which would
    /// read alike.
    fn pasteable(&self, terms: &[&str]) -> bool {
        if !terms.iter().all(|term| vir::air_names::renders_as_source(&self.plain, term)) {
            return false;
        }
        // SSA symbols are plain SMT-LIB symbols, never quoted, so splitting
        // on parentheses and spaces finds every one.
        let mut version_of: HashMap<&str, u32> = HashMap::new();
        for atom in terms.iter().flat_map(|term| term.split(['(', ')', ' ', '\n'])) {
            if let Some((base, version)) = self.versions.get(atom) {
                if *version_of.entry(base.as_str()).or_insert(*version) != *version {
                    return false;
                }
            }
        }
        true
    }

    /// A term as source to paste.
    fn render_plain(&self, term: &str) -> String {
        vir::air_names::render_term(&self.plain, term)
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

/// The most rounds of rising depth a probe may ask to make a matching loop.
const MAX_LOOP_THRESHOLD: u32 = 1000;
/// The most quantifiers a probe lists as candidates.
const MAX_CANDIDATES: usize = 40;

const SPECULATION_CAVEAT: &str = "The hypothesis was sent in the query's own scope and popped right after the check, so the session's solver state is unchanged. A closed verdict is not a verification result: paste the snippet into the source and verify it normally.";

/// A hypothesis as a `speculate` request names it. A term is an SMT term in
/// the solver's spelling, as the `smt_*` fields of other replies give them,
/// or with symbols named by their source names instead, which are looked up
/// among the query's declarations. A variable of the quantifier may be
/// named either way.
#[derive(Deserialize)]
#[serde(rename_all = "snake_case", deny_unknown_fields)]
enum HypothesisRequest {
    /// Instantiate the quantifier once, with a term for each variable.
    Instantiation { qid: String, subst: BTreeMap<String, String> },
    /// Match the quantifier with one more trigger, whose terms are over its
    /// variables.
    TriggerPattern { qid: String, pattern: OneOrMore },
    /// Refuse the quantifier's instantiations whose terms, or trigger
    /// instance, match the fingerprint: an SMT term whose holes `_`, `_<n>`
    /// and `#<n>` match any term, as a matching loop's `step` is written.
    BlockCycle { qid: String, fingerprint: String },
}

impl HypothesisRequest {
    fn qid(&self) -> &str {
        match self {
            Self::Instantiation { qid, .. }
            | Self::TriggerPattern { qid, .. }
            | Self::BlockCycle { qid, .. } => qid,
        }
    }

    fn name(&self) -> &'static str {
        match self {
            Self::Instantiation { .. } => "instantiation",
            Self::TriggerPattern { .. } => "trigger_pattern",
            Self::BlockCycle { .. } => "block_cycle",
        }
    }
}

/// One term, or a multi-trigger's several.
#[derive(Deserialize)]
#[serde(untagged)]
enum OneOrMore {
    One(String),
    More(Vec<String>),
}

impl OneOrMore {
    fn terms(&self) -> Vec<&str> {
        match self {
            Self::One(term) => vec![term.as_str()],
            Self::More(terms) => terms.iter().map(String::as_str).collect(),
        }
    }
}

/// One check a probe made. Never a verification result.
#[derive(Serialize)]
struct SpeculationRun {
    result: QueryResult,
    elapsed_ms: u128,
    /// cvc5's instantiation rounds
    rounds: u64,
    /// Quantifiers whose instantiating terms got deeper in at least the
    /// loop threshold of rounds: matching loops.
    loops: Vec<ResolvedSpeculationLoop>,
}

#[derive(Clone, Serialize)]
struct ResolvedSpeculationLoop {
    qid: String,
    /// the function it belongs to, and for a quantifier written in source,
    /// where
    #[serde(skip_serializing_if = "Option::is_none")]
    function: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    span: Option<String>,
    instantiations: u64,
    /// of them directed by the hypothesis
    directed: u64,
    rounds: u64,
    /// rounds in which its deepest instantiating term got deeper
    rises: u64,
    first_depth: u64,
    max_depth: u64,
}

#[derive(Serialize)]
struct BinderDescription {
    /// in source spelling, when the encoder recorded one
    name: String,
    /// as the solver spells it
    smt_name: String,
    sort: String,
}

/// A quantifier the query's scope asserts.
#[derive(Serialize)]
struct QuantifierDescription {
    qid: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    function: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    span: Option<String>,
    /// The query asserts it itself (a `requires`, an `assert forall`)
    /// rather than a declaration before it (a broadcast lemma, a spec
    /// function's definition, the prelude).
    in_query: bool,
    binders: Vec<BinderDescription>,
    /// each trigger's terms, in source spelling and as the solver spells them
    triggers: Vec<Vec<String>>,
    smt_triggers: Vec<Vec<String>>,
}

#[derive(Serialize)]
struct DirectedInstance {
    qid: String,
    terms: Vec<String>,
    smt_terms: Vec<String>,
    /// how cvc5 tags every instantiation a hypothesis made
    inference_id: &'static str,
}

#[derive(Serialize)]
struct NewProvenance {
    /// The instantiations the hypothesis made, the first 20. A directed
    /// instance is the one requested; a trigger's are all it matched, not
    /// only those the proof used.
    closing_instantiations: Vec<DirectedInstance>,
    extra_inst_count: u64,
}

/// What a `speculate` request found.
#[derive(Serialize)]
struct SpeculationOutcome {
    /// `instantiation`, `trigger_pattern`, `block_cycle`, or `none`
    hypothesis: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    qid: Option<String>,
    /// The quantifier the hypothesis names, as the query's scope asserts it.
    #[serde(skip_serializing_if = "Option::is_none")]
    quantifier: Option<QuantifierDescription>,
    /// The query checked with nothing added.
    #[serde(skip_serializing_if = "Option::is_none")]
    before: Option<SpeculationRun>,
    /// The query checked with the hypothesis.
    #[serde(skip_serializing_if = "Option::is_none")]
    after: Option<SpeculationRun>,
    /// `applied`; `rejected` (the instantiation was made already); `mismatch`
    /// (the terms do not fit the variables); `unusable` (the pattern cannot
    /// be a trigger); `no_quantifier`; `could_not_lower` (a term the solver
    /// cannot read); `pending` (no instantiation round ran)
    #[serde(skip_serializing_if = "Option::is_none")]
    status: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    reason: Option<String>,
    /// The query failed without the hypothesis, before and again right
    /// after, and holds with it.
    closed: bool,
    /// The check without the hypothesis, run again after one that closed.
    #[serde(skip_serializing_if = "Option::is_none")]
    recheck: Option<SpeculationRun>,
    /// Whether the check with the hypothesis has a matching loop that the
    /// check without it does not.
    #[serde(skip_serializing_if = "Option::is_none")]
    introduced_loop: Option<bool>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    new_loops: Vec<ResolvedSpeculationLoop>,
    #[serde(skip_serializing_if = "Option::is_none")]
    new_provenance: Option<NewProvenance>,
    /// Instantiations a block refused, and the first few refused vectors.
    #[serde(skip_serializing_if = "Option::is_none")]
    blocked: Option<u64>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    blocked_examples: Vec<Vec<String>>,
    /// Source to paste when the hypothesis closed the query: an `assert`
    /// of the directed instance, or a trigger annotation.
    #[serde(skip_serializing_if = "Option::is_none")]
    verus_snippet: Option<String>,
    /// For a trigger, an `assert` of one instance it made, which needs no
    /// change to the quantifier.
    #[serde(skip_serializing_if = "Option::is_none")]
    fallback_snippet: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    suggestion: Option<String>,
    notes: String,
    /// Quantifiers written in source that the query's scope asserts, the
    /// query's own first, when the request named none or one not there.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    candidates: Vec<QuantifierDescription>,
    caveat: &'static str,
    elapsed_ms: u128,
    restore_ms: u128,
}

impl SpeculationOutcome {
    fn new(hypothesis: &'static str, qid: Option<String>) -> Self {
        Self {
            hypothesis,
            qid,
            quantifier: None,
            before: None,
            after: None,
            status: None,
            reason: None,
            closed: false,
            recheck: None,
            introduced_loop: None,
            new_loops: Vec::new(),
            new_provenance: None,
            blocked: None,
            blocked_examples: Vec::new(),
            verus_snippet: None,
            fallback_snippet: None,
            suggestion: None,
            notes: String::new(),
            candidates: Vec::new(),
            caveat: SPECULATION_CAVEAT,
            elapsed_ms: 0,
            restore_ms: 0,
        }
    }
}

/// A term on one line, as the solver spells it.
fn flat(node: &TreeNode) -> String {
    match node {
        TreeNode::Atom(atom) => atom.clone(),
        TreeNode::List(items) => {
            format!("({})", items.iter().map(flat).collect::<Vec<_>>().join(" "))
        }
    }
}

/// `text` as one term, if it is exactly one.
fn parse_term(text: &str) -> Option<TreeNode> {
    let mut parser = sise::Parser::new(text);
    let node = sise::parse_tree(&mut parser).ok()?;
    parser.finish().ok()?;
    Some(node)
}

fn result_name(result: QueryResult) -> &'static str {
    match result {
        QueryResult::Valid => "valid",
        QueryResult::Invalid => "invalid",
        QueryResult::ResourceLimit => "resource_limit",
    }
}

/// Whether the solver reads an atom as itself: a numeral, a Boolean, a
/// string or a bit-vector literal.
fn is_literal(atom: &str) -> bool {
    atom == "true"
        || atom == "false"
        || atom.starts_with('"')
        || atom.starts_with('#')
        || (!atom.is_empty() && atom.bytes().all(|b| b.is_ascii_digit() || b == b'.'))
}

/// The sort the solver is sent for an AIR type.
fn sort_name(typ: &air::ast::Typ) -> String {
    use air::ast::TypX;
    match &**typ {
        TypX::Bool => "Bool".to_owned(),
        TypX::Int => "Int".to_owned(),
        TypX::Real => "Real".to_owned(),
        TypX::Fun => "Fun".to_owned(),
        TypX::Named(name) => name.to_string(),
        TypX::BitVec(bits) => format!("(_ BitVec {bits})"),
        TypX::Float { exp_bits, sig_bits } => format!("(_ FloatingPoint {exp_bits} {sig_bits})"),
    }
}

/// The sort Verus boxes values into.
const POLY: &str = "Poly";

/// What the query's scope declares, with sorts: constants and variables,
/// and functions (datatype constructors and fields included) with their
/// argument and result sorts.
#[derive(Default)]
struct Declarations {
    constants: HashMap<String, String>,
    functions: HashMap<String, (Vec<String>, String)>,
}

impl Declarations {
    fn of(decls: &[&Decl], query: &Query) -> Self {
        let mut out = Self::default();
        // The prelude reaches each solver directly, never through the
        // journal, so its boxes for integers and booleans are named here;
        // a datatype's are the bucket's own declarations.
        for (f, arg, result) in [
            (vir::def::BOX_INT, "Int", POLY),
            (vir::def::BOX_BOOL, "Bool", POLY),
            (vir::def::UNBOX_INT, POLY, "Int"),
            (vir::def::UNBOX_BOOL, POLY, "Bool"),
        ] {
            out.functions.insert(f.to_owned(), (vec![arg.to_owned()], result.to_owned()));
        }
        for decl in decls.iter().copied().chain(query.local.iter()) {
            match &**decl {
                DeclX::Const(x, typ) | DeclX::Var(x, typ) => {
                    out.constants.insert(x.to_string(), sort_name(typ));
                }
                DeclX::Fun(x, typs, typ) => {
                    let args = typs.iter().map(sort_name).collect();
                    out.functions.insert(x.to_string(), (args, sort_name(typ)));
                }
                DeclX::Datatypes(datatypes) => {
                    for datatype in datatypes.iter() {
                        let sort = datatype.name.to_string();
                        for variant in datatype.a.iter() {
                            let fields: Vec<String> =
                                variant.a.iter().map(|field| sort_name(&field.a)).collect();
                            out.functions.insert(variant.name.to_string(), (fields, sort.clone()));
                            for field in variant.a.iter() {
                                out.functions.insert(
                                    field.name.to_string(),
                                    (vec![sort.clone()], sort_name(&field.a)),
                                );
                            }
                        }
                    }
                }
                DeclX::Sort(_) | DeclX::Axiom(_) => {}
            }
        }
        out
    }

    fn declares(&self, symbol: &str) -> bool {
        self.constants.contains_key(symbol) || self.functions.contains_key(symbol)
    }
}

/// Turns the terms of a hypothesis into the solver's spelling: names
/// resolved, and values boxed into `Poly` or unboxed out of it where a
/// function, operator or variable takes the other, as Verus's encoding does.
struct Lowering {
    /// A variable of the quantifier, by its own name and by its source
    /// name: its own name.
    binders: HashMap<String, String>,
    /// Each variable's sort, by its own name.
    binder_sorts: HashMap<String, String>,
    declared: Declarations,
    /// A declared symbol by its source name, whole and by its last path
    /// segment. Only symbols an encoder minted for the name itself count,
    /// not the helpers named after it (a function's `req%`, `ens%`).
    by_source: HashMap<String, BTreeSet<String>>,
}

impl Lowering {
    fn new(quantifier: &QuantifierSmt, declared: Declarations, names: &[&SourceNames]) -> Self {
        let mut binders: HashMap<String, String> =
            quantifier.binders.iter().map(|(smt, _)| (smt.clone(), smt.clone())).collect();
        let binder_sorts =
            quantifier.binders.iter().map(|(smt, sort)| (smt.clone(), flat(sort))).collect();
        let mut by_source: HashMap<String, BTreeSet<String>> = HashMap::new();
        let symbols: Vec<&String> =
            declared.constants.keys().chain(declared.functions.keys()).collect();
        for names in names {
            for (smt, _) in &quantifier.binders {
                if let Some(source) = vir::air_names::source_symbol(names, smt) {
                    binders.entry(source).or_insert_with(|| smt.clone());
                }
            }
            for &symbol in &symbols {
                // A call head is recorded under its whole symbol, `?` and all,
                // which `source_symbol` strips before looking up.
                let source = match names.get(symbol.as_str()) {
                    Some(name) => Some(name.name().to_owned()),
                    None => symbol
                        .strip_suffix(vir::def::AIR_GLOBAL_SUFFIX)
                        .filter(|stem| names.contains_key(*stem))
                        .and_then(|_| vir::air_names::source_symbol(names, symbol)),
                };
                let Some(source) = source else { continue };
                let last = source.rsplit("::").next().unwrap_or(&source).to_string();
                by_source.entry(last).or_default().insert(symbol.clone());
                by_source.entry(source).or_default().insert(symbol.clone());
            }
        }
        Self { binders, binder_sorts, declared, by_source }
    }

    fn atom(&self, atom: &str) -> Result<String, String> {
        if let Some(binder) = self.binders.get(atom) {
            return Ok(binder.clone());
        }
        if self.declared.declares(atom) || is_literal(atom) {
            return Ok(atom.to_string());
        }
        match self.by_source.get(atom) {
            Some(symbols) if symbols.len() == 1 => Ok(symbols.iter().next().unwrap().clone()),
            Some(symbols) => Err(format!(
                "`{atom}` could name any of {}; write the one meant",
                symbols.iter().cloned().collect::<Vec<_>>().join(", ")
            )),
            // an operator, a hole, or a symbol the solver declared itself
            None => Ok(atom.to_string()),
        }
    }

    fn node(&self, node: &TreeNode) -> Result<TreeNode, String> {
        match node {
            TreeNode::Atom(atom) => Ok(TreeNode::Atom(self.atom(atom)?)),
            TreeNode::List(items) => {
                Ok(TreeNode::List(items.iter().map(|n| self.node(n)).collect::<Result<_, _>>()?))
            }
        }
    }

    /// `term`, in the solver's spelling and boxed or unboxed to `want` when
    /// that is its sort's counterpart.
    fn term_as(&self, text: &str, want: Option<&str>) -> Result<TreeNode, String> {
        let (node, sort) = self.typed(&self.term(text)?);
        Ok(self.coerce(node, sort.as_deref(), want))
    }

    /// The function that boxes a value of `sort` into `Poly`, or unboxes it.
    fn boxing(&self, sort: &str, unbox: bool) -> Option<String> {
        let head = match (sort, unbox) {
            ("Int", false) => vir::def::BOX_INT.to_owned(),
            ("Bool", false) => vir::def::BOX_BOOL.to_owned(),
            ("Int", true) => vir::def::UNBOX_INT.to_owned(),
            ("Bool", true) => vir::def::UNBOX_BOOL.to_owned(),
            (_, false) => format!("{}{sort}", vir::def::PREFIX_BOX),
            (_, true) => format!("{}{sort}", vir::def::PREFIX_UNBOX),
        };
        self.declared.functions.contains_key(&head).then_some(head)
    }

    /// `node`, of sort `have`, as a value of sort `want`: boxed or unboxed
    /// when one of them is `Poly`, else as it is.
    fn coerce(&self, node: TreeNode, have: Option<&str>, want: Option<&str>) -> TreeNode {
        let head = match (have, want) {
            (Some(have), Some(want)) if have != want && want == POLY => self.boxing(have, false),
            (Some(have), Some(want)) if have != want && have == POLY => self.boxing(want, true),
            _ => None,
        };
        match head {
            Some(head) => TreeNode::List(vec![TreeNode::Atom(head), node]),
            None => node,
        }
    }

    /// `node` with its arguments coerced to the sorts its functions and
    /// operators take, and its own sort, when that can be told.
    fn typed(&self, node: &TreeNode) -> (TreeNode, Option<String>) {
        let items = match node {
            TreeNode::Atom(atom) => {
                let sort = self
                    .binder_sorts
                    .get(atom)
                    .or_else(|| self.declared.constants.get(atom))
                    .cloned()
                    .or_else(|| match atom.as_str() {
                        "true" | "false" => Some("Bool".to_owned()),
                        _ if !atom.is_empty() && atom.bytes().all(|b| b.is_ascii_digit()) => {
                            Some("Int".to_owned())
                        }
                        _ => None,
                    });
                return (node.clone(), sort);
            }
            TreeNode::List(items) => items,
        };
        let Some((TreeNode::Atom(head), args)) = items.split_first() else {
            return (node.clone(), None);
        };
        let typed: Vec<(TreeNode, Option<String>)> = args.iter().map(|a| self.typed(a)).collect();
        let all = |sort: &str| vec![Some(sort.to_owned()); typed.len()];
        let (wants, sort): (Vec<Option<String>>, Option<String>) =
            match self.declared.functions.get(head) {
                Some((params, result)) if params.len() == typed.len() => {
                    (params.iter().cloned().map(Some).collect(), Some(result.clone()))
                }
                Some(_) => (vec![None; typed.len()], None),
                None => match head.as_str() {
                    "+" | "-" | "*" | "div" | "mod" => (all("Int"), Some("Int".to_owned())),
                    "<" | "<=" | ">" | ">=" => (all("Int"), Some("Bool".to_owned())),
                    "and" | "or" | "not" | "=>" => (all("Bool"), Some("Bool".to_owned())),
                    // both sides alike: boxed if either is
                    "=" | "distinct" => {
                        let boxed = typed.iter().any(|(_, s)| s.as_deref() == Some(POLY));
                        let side = if boxed { Some(POLY.to_owned()) } else { None };
                        (vec![side; typed.len()], Some("Bool".to_owned()))
                    }
                    "ite" if typed.len() == 3 => {
                        let boxed = typed[1..].iter().any(|(_, s)| s.as_deref() == Some(POLY));
                        let branch = if boxed { Some(POLY.to_owned()) } else { typed[1].1.clone() };
                        (vec![Some("Bool".to_owned()), branch.clone(), branch.clone()], branch)
                    }
                    _ => (vec![None; typed.len()], None),
                },
            };
        let mut out = vec![TreeNode::Atom(head.clone())];
        for ((arg, have), want) in typed.into_iter().zip(wants) {
            out.push(self.coerce(arg, have.as_deref(), want.as_deref()));
        }
        (TreeNode::List(out), sort)
    }

    /// An SMT term (one symbol, or starting with `(`) or a Verus expression
    /// (see `surface_term`), in the solver's spelling.
    fn term(&self, text: &str) -> Result<TreeNode, String> {
        let text = text.trim();
        let node = match parse_term(text) {
            Some(node @ TreeNode::Atom(_)) => node,
            Some(node) if text.starts_with('(') => node,
            _ if text.starts_with('(') && !text.contains(',') => {
                return Err(format!("not a single SMT term: {text}"));
            }
            _ => surface_term(text)?,
        };
        self.node(&node)
    }
}

/// A Verus expression as an SMT term: calls `f(a, b)` and paths, variables,
/// numerals, `true` and `false`, parentheses, and the operators `!` and unary
/// `-`, `* / %`, `+ -`, `< <= > >= == !=`, `&&`, `||` and `==>`, loosest
/// last. Names stay as written, for `Lowering` to resolve; `#0` and `_0` are
/// names too, so a fingerprint's holes survive.
fn surface_term(text: &str) -> Result<TreeNode, String> {
    let chars: Vec<char> = text.chars().collect();
    let name_char = |c: char| c.is_ascii_alphanumeric() || c == '_' || c == '#' || c == '@';
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if name_char(c) {
            let start = i;
            while i < chars.len() {
                if name_char(chars[i]) {
                    i += 1;
                } else if chars[i] == ':' && chars.get(i + 1) == Some(&':') {
                    i += 2;
                } else {
                    break;
                }
            }
            tokens.push(chars[start..i].iter().collect::<String>());
        } else {
            let rest: String = chars[i..].iter().take(3).collect();
            let op = ["==>", "==", "!=", "<=", ">=", "&&", "||"]
                .into_iter()
                .find(|op| rest.starts_with(op))
                .map(str::to_string)
                .or_else(|| "(),+-*/%<>!".contains(c).then(|| c.to_string()))
                .ok_or_else(|| format!("unexpected `{c}` in {text}"))?;
            i += op.chars().count();
            tokens.push(op);
        }
    }
    let mut parser = Surface { tokens, pos: 0 };
    let node = parser.binary(0)?;
    match parser.tokens.get(parser.pos) {
        None => Ok(node),
        Some(token) => Err(format!("unexpected `{token}` in {text}")),
    }
}

struct Surface {
    tokens: Vec<String>,
    pos: usize,
}

impl Surface {
    fn peek(&self) -> Option<&str> {
        self.tokens.get(self.pos).map(String::as_str)
    }

    fn next(&mut self) -> Result<String, String> {
        let token = self.tokens.get(self.pos).cloned().ok_or("the expression ends too soon")?;
        self.pos += 1;
        Ok(token)
    }

    fn binary(&mut self, min: u8) -> Result<TreeNode, String> {
        let mut lhs = self.unary()?;
        while let Some(op) = self.peek() {
            let (precedence, right) = match op {
                "==>" => (1, true),
                "||" => (2, false),
                "&&" => (3, false),
                "==" | "!=" | "<" | "<=" | ">" | ">=" => (4, false),
                "+" | "-" => (5, false),
                "*" | "/" | "%" => (6, false),
                _ => break,
            };
            if precedence < min {
                break;
            }
            let op = self.next()?;
            let rhs = self.binary(if right { precedence } else { precedence + 1 })?;
            let atom = |s: &str| TreeNode::Atom(s.to_string());
            lhs = match op.as_str() {
                "!=" => {
                    TreeNode::List(vec![atom("not"), TreeNode::List(vec![atom("="), lhs, rhs])])
                }
                _ => {
                    let head = match op.as_str() {
                        "==" => "=",
                        "&&" => "and",
                        "||" => "or",
                        "==>" => "=>",
                        "/" => "div",
                        "%" => "mod",
                        other => other,
                    };
                    TreeNode::List(vec![atom(head), lhs, rhs])
                }
            };
        }
        Ok(lhs)
    }

    fn unary(&mut self) -> Result<TreeNode, String> {
        let head = match self.peek() {
            Some("!") => "not",
            Some("-") => "-",
            _ => return self.primary(),
        };
        self.pos += 1;
        Ok(TreeNode::List(vec![TreeNode::Atom(head.to_string()), self.unary()?]))
    }

    fn primary(&mut self) -> Result<TreeNode, String> {
        let token = self.next()?;
        if token == "(" {
            let inner = self.binary(0)?;
            return match self.next()?.as_str() {
                ")" => Ok(inner),
                other => Err(format!("expected `)`, found `{other}`")),
            };
        }
        if !token.starts_with(|c: char| c.is_ascii_alphanumeric() || c == '_' || c == '#') {
            return Err(format!("unexpected `{token}`"));
        }
        if self.peek() != Some("(") {
            return Ok(TreeNode::Atom(token));
        }
        self.pos += 1;
        let mut items = vec![TreeNode::Atom(token)];
        if self.peek() == Some(")") {
            self.pos += 1;
        } else {
            loop {
                items.push(self.binary(0)?);
                match self.next()?.as_str() {
                    "," => {}
                    ")" => break,
                    other => return Err(format!("expected `,` or `)`, found `{other}`")),
                }
            }
        }
        // a call without arguments is the constant itself
        Ok(if items.len() == 1 { items.pop().unwrap() } else { TreeNode::List(items) })
    }
}

/// The hypothesis in the solver's spelling, and for an instantiation, its
/// term for each variable; or why it cannot be sent.
fn lower_hypothesis(
    request: &HypothesisRequest,
    quantifier: &QuantifierSmt,
    lowering: &Lowering,
) -> Result<(Hypothesis, HashMap<String, TreeNode>), (&'static str, String)> {
    let qid = quantifier.qid.clone();
    match request {
        HypothesisRequest::Instantiation { subst, .. } => {
            let mut terms: HashMap<String, TreeNode> = HashMap::new();
            for (name, text) in subst {
                let Some(smt) = lowering.binders.get(name.as_str()) else {
                    let binders: Vec<&str> =
                        quantifier.binders.iter().map(|(smt, _)| smt.as_str()).collect();
                    return Err((
                        "mismatch",
                        format!("{qid} binds no variable {name}; it binds {}", binders.join(", ")),
                    ));
                };
                let sort = lowering.binder_sorts.get(smt).map(String::as_str);
                let term = lowering.term_as(text, sort).map_err(|e| ("could_not_lower", e))?;
                if terms.insert(smt.clone(), term).is_some() {
                    return Err(("mismatch", format!("two terms for the variable {smt}")));
                }
            }
            let missing: Vec<String> = quantifier
                .binders
                .iter()
                .filter(|(smt, _)| !terms.contains_key(smt))
                .map(|(smt, sort)| format!("{smt} ({})", flat(sort)))
                .collect();
            if !missing.is_empty() {
                return Err((
                    "mismatch",
                    format!(
                        "no term for {}: every variable needs one, type variables included",
                        missing.join(", ")
                    ),
                ));
            }
            let subst = quantifier
                .binders
                .iter()
                .map(|(smt, _)| (smt.clone(), flat(&terms[smt])))
                .collect();
            Ok((Hypothesis::Instantiate { qid, subst }, terms))
        }
        HypothesisRequest::TriggerPattern { pattern, .. } => {
            let pattern: Vec<String> = pattern
                .terms()
                .into_iter()
                .map(|term| lowering.term_as(term, None).map(|node| flat(&node)))
                .collect::<Result<_, _>>()
                .map_err(|e| ("could_not_lower", e))?;
            if pattern.is_empty() {
                return Err(("mismatch", "the pattern has no terms".to_string()));
            }
            Ok((
                Hypothesis::Trigger { qid, vars: quantifier.binders.clone(), pattern },
                HashMap::new(),
            ))
        }
        HypothesisRequest::BlockCycle { fingerprint, .. } => {
            let fingerprint =
                flat(&lowering.term_as(fingerprint, None).map_err(|e| ("could_not_lower", e))?);
            Ok((Hypothesis::Block { qid, fingerprint }, HashMap::new()))
        }
    }
}

/// `(=> G P)` without the `has_type` conjuncts of `G`, which a term of the
/// variable's type satisfies and source never writes.
fn without_type_guards(node: &TreeNode) -> TreeNode {
    let guard = |n: &TreeNode| {
        matches!(n, TreeNode::List(items)
            if matches!(items.first(), Some(TreeNode::Atom(head)) if head == vir::def::HAS_TYPE))
    };
    let TreeNode::List(items) = node else { return node.clone() };
    let [TreeNode::Atom(implies), hypothesis, conclusion] = &items[..] else {
        return node.clone();
    };
    if implies != "=>" {
        return node.clone();
    }
    let kept: Vec<TreeNode> = match hypothesis {
        TreeNode::List(conjuncts) if matches!(conjuncts.first(), Some(TreeNode::Atom(head)) if head == "and") => {
            conjuncts[1..].iter().filter(|n| !guard(n)).cloned().collect()
        }
        n if guard(n) => Vec::new(),
        n => vec![n.clone()],
    };
    let atom = |s: &str| TreeNode::Atom(s.to_string());
    match kept.len() {
        0 => conclusion.clone(),
        1 => TreeNode::List(vec![atom("=>"), kept[0].clone(), conclusion.clone()]),
        _ => {
            let and = TreeNode::List(std::iter::once(atom("and")).chain(kept).collect());
            TreeNode::List(vec![atom("=>"), and, conclusion.clone()])
        }
    }
}

/// `assert(<the body at subst>);` when that pastes as source; else an assert
/// that mentions the instance of one of the quantifier's triggers, which
/// makes it fire at those terms.
fn instance_assert(
    quantifier: &QuantifierSmt,
    subst: &HashMap<String, TreeNode>,
    names: &QueryNames,
) -> Option<String> {
    let body = flat(&without_type_guards(&quantifier.instance(subst)));
    if names.pasteable(&[&body]) {
        return Some(format!("assert({});", names.render_plain(&body)));
    }
    quantifier.trigger_instances(subst).iter().find_map(|trigger| {
        let terms: Vec<String> = trigger.iter().map(flat).collect();
        let refs: Vec<&str> = terms.iter().map(String::as_str).collect();
        names.pasteable(&refs).then(|| {
            let mentions: Vec<String> = terms
                .iter()
                .map(|term| {
                    let term = names.render_plain(term);
                    format!("{term} == {term}")
                })
                .collect();
            format!("assert({});", mentions.join(" && "))
        })
    })
}

fn describe_quantifier(
    quantifier: &QuantifierSmt,
    symbols: Option<&crate::provenance::Symbols>,
    names: &QueryNames,
) -> QuantifierDescription {
    let site = symbols.and_then(|symbols| symbols.quantifier_site(&quantifier.qid));
    QuantifierDescription {
        qid: quantifier.qid.clone(),
        function: site.map(|(function, _)| function.to_owned()),
        span: site.and_then(|(_, span)| span.map(str::to_owned)),
        in_query: quantifier.in_query,
        binders: quantifier
            .binders
            .iter()
            .map(|(smt, sort)| BinderDescription {
                name: vir::air_names::source_symbol(&names.shown, smt)
                    .unwrap_or_else(|| smt.clone()),
                smt_name: smt.clone(),
                sort: flat(sort),
            })
            .collect(),
        triggers: quantifier
            .triggers
            .iter()
            .map(|trigger| trigger.iter().map(|term| names.show(&flat(term))).collect())
            .collect(),
        smt_triggers: quantifier
            .triggers
            .iter()
            .map(|trigger| trigger.iter().map(flat).collect())
            .collect(),
    }
}

fn speculation_run(
    result: QueryResult,
    elapsed_ms: u128,
    reply: &SpeculationReply,
    symbols: Option<&crate::provenance::Symbols>,
) -> SpeculationRun {
    SpeculationRun {
        result,
        elapsed_ms,
        rounds: reply.rounds,
        loops: reply
            .loops
            .iter()
            .map(|l| {
                let site = symbols.and_then(|symbols| symbols.quantifier_site(&l.qid));
                ResolvedSpeculationLoop {
                    qid: l.qid.clone(),
                    function: site.map(|(function, _)| function.to_owned()),
                    span: site.and_then(|(_, span)| span.map(str::to_owned)),
                    instantiations: l.instantiations,
                    directed: l.directed,
                    rounds: l.rounds,
                    rises: l.rises,
                    first_depth: l.first_depth,
                    max_depth: l.max_depth,
                }
            })
            .collect(),
    }
}

/// Check a retained query with `hypothesis` in its scope, and read what cvc5
/// reported about it. Rounds for further errors are not run, and nothing is
/// saved as a certificate. The caller has restored the query's prefix.
fn speculation_check(
    air: &mut Context,
    query: &RetainedQuery,
    hypothesis: Hypothesis,
    loop_threshold: Option<u32>,
    set_rlimit: &impl Fn(&mut Context, f32),
) -> io::Result<(QueryResult, u128, SpeculationReply)> {
    set_rlimit(air, query.rlimit);
    air.set_speculation(Some(SpeculationRequest { hypothesis, loop_threshold }));
    let start = Instant::now();
    let outcome = air.check_valid(
        &VirMessageInterface {},
        &QueryDiagnostics::default(),
        &query.query,
        QueryContext::default(),
    );
    let elapsed_ms = start.elapsed().as_millis();
    // a check that never reached the solver leaves the request behind
    air.set_speculation(None);
    let reply = air.take_speculation();
    drop(air.take_provenance());
    drop(air.take_unknown_reason());
    drop(air.take_matching_loops());
    drop(air.take_difficulty());
    drop(air.take_inst_pressure());
    let result = match outcome {
        ValidityResult::Valid(_) => QueryResult::Valid,
        ValidityResult::Invalid(..) => QueryResult::Invalid,
        ValidityResult::Canceled => QueryResult::ResourceLimit,
        ValidityResult::TypeError(error) => return Err(io::Error::other(error.to_string())),
        ValidityResult::UnexpectedOutput(error) => return Err(io::Error::other(error)),
    };
    air.finish_query();
    let reply = reply.unwrap_or_else(|| SpeculationReply {
        unparsed: Some("the check did not reach check-sat".to_owned()),
        ..SpeculationReply::default()
    });
    Ok((result, elapsed_ms, reply))
}

/// cvc5's `(error "...")` as its message.
fn error_message(line: &str) -> String {
    line.strip_prefix("(error \"")
        .and_then(|rest| rest.strip_suffix("\")"))
        .map(|message| message.replace("\"\"", "\""))
        .unwrap_or_else(|| line.to_owned())
}

/// Serve a `speculate` request for one query of `bucket`, whose address the
/// caller has checked. `Ok(Err(_))` is a refusal to report; `Err` ends the
/// session.
fn serve_speculate(
    bucket: &RetainedBucket,
    id: QueryId,
    hypothesis: Option<HypothesisRequest>,
    loop_threshold: Option<u32>,
    set_rlimit: &impl Fn(&mut Context, f32),
) -> io::Result<Result<SpeculationOutcome, &'static str>> {
    let mut state =
        bucket.state.lock().map_err(|_| io::Error::other("resident bucket poisoned"))?;
    let (solver, local) = bucket.addresses[id.0];
    let SolverState { air, journal } = &mut state[solver];
    if !matches!(air.get_solver(), SmtSolver::Cvc5) {
        return Ok(Err("speculative probes need cvc5"));
    }
    let prefix = journal.queries[local].prefix;
    let restore_start = Instant::now();
    journal.restore_prefix(air, prefix)?;
    let restore_ms = restore_start.elapsed().as_millis();
    if !air.supports_speculation() {
        return Ok(Err(
            "this cvc5 does not serve speculative probes: it needs (speculate ...) and (get-info :speculation)",
        ));
    }
    let start = Instant::now();
    let query = &journal.queries[local];
    let decls: Vec<&Decl> = journal
        .base
        .iter()
        .chain(journal.contexts[..prefix].iter().flatten())
        .flat_map(|batch| batch.iter())
        .filter_map(|command| match &**command {
            CommandX::Global(decl) => Some(decl),
            _ => None,
        })
        .collect();
    let symbols = bucket.symbols.as_ref();
    let no_versions = VariableVersions::new();
    let empty = SourceNames::new();
    let unversioned = QueryNames::new(symbols, &no_versions, &empty);
    let mut outcome = SpeculationOutcome::new(
        hypothesis.as_ref().map_or("none", HypothesisRequest::name),
        hypothesis.as_ref().map(|h| h.qid().to_owned()),
    );
    outcome.restore_ms = restore_ms;
    // The first MAX_CANDIDATES quantifiers written in source, and a sentence
    // saying so when the scope asserts more.
    let candidates = |air: &Context| -> (Vec<QuantifierDescription>, String) {
        let written = |qid: &str, in_query: bool| {
            in_query
                || symbols
                    .and_then(|symbols| symbols.quantifier_site(qid))
                    .is_some_and(|(_, span)| span.is_some())
        };
        let all = air.quantifiers(decls.iter().copied(), &query.query, written);
        let listed: Vec<QuantifierDescription> = all
            .iter()
            .take(MAX_CANDIDATES)
            .map(|q| describe_quantifier(q, symbols, &unversioned))
            .collect();
        let note = if listed.len() < all.len() {
            format!(
                "The candidates are the first {} of the {} quantifiers written in source that this query's scope asserts.",
                listed.len(),
                all.len()
            )
        } else {
            "The candidates are the quantifiers written in source that this query's scope asserts."
                .to_owned()
        };
        (listed, note)
    };

    // The quantifier the hypothesis names, and the hypothesis in the
    // solver's spelling, or why nothing will be checked.
    let mut target = None;
    if let Some(request) = &hypothesis {
        let Some(quantifier) =
            air.find_quantifier(decls.iter().copied(), &query.query, request.qid())
        else {
            outcome.status = Some("no_quantifier".to_owned());
            outcome.reason = Some(format!(
                "no quantifier named {} is asserted in this query's scope",
                request.qid()
            ));
            let (listed, note) = candidates(air);
            outcome.candidates = listed;
            outcome.notes = format!("Nothing was checked. {note}");
            outcome.elapsed_ms = start.elapsed().as_millis();
            return Ok(Ok(outcome));
        };
        outcome.quantifier = Some(describe_quantifier(&quantifier, symbols, &unversioned));
        let lowering = Lowering::new(
            &quantifier,
            Declarations::of(&decls, &query.query),
            &[&unversioned.shown, &unversioned.plain],
        );
        match lower_hypothesis(request, &quantifier, &lowering) {
            Ok((lowered, subst)) => target = Some((quantifier, lowered, subst)),
            Err((status, reason)) => {
                outcome.status = Some(status.to_owned());
                outcome.notes = format!("Nothing was checked: {reason}.");
                outcome.reason = Some(reason);
                outcome.elapsed_ms = start.elapsed().as_millis();
                return Ok(Ok(outcome));
            }
        }
    }

    let (before_result, before_ms, before_reply) =
        speculation_check(air, query, Hypothesis::Observe, loop_threshold, set_rlimit)?;
    let before = speculation_run(before_result, before_ms, &before_reply, symbols);
    let before_loops: HashSet<String> = before.loops.iter().map(|l| l.qid.clone()).collect();
    let before_loop_count = before.loops.len();
    outcome.before = Some(before);
    let Some((quantifier, lowered, subst)) = target else {
        let (listed, note) = candidates(air);
        outcome.candidates = listed;
        outcome.notes = format!(
            "No hypothesis: the query was checked as usual and answers {}, with {before_loop_count} matching loop(s). {note}",
            result_name(before_result)
        );
        outcome.elapsed_ms = start.elapsed().as_millis();
        return Ok(Ok(outcome));
    };

    let (after_result, after_ms, after_reply) =
        speculation_check(air, query, lowered.clone(), loop_threshold, set_rlimit)?;
    if let Some(error) = &after_reply.error {
        outcome.status = Some("could_not_lower".to_owned());
        outcome.reason = Some(error_message(error));
        outcome.notes = "cvc5 could not read the hypothesis in the query's scope, so the query was not checked with it.".to_owned();
        outcome.elapsed_ms = start.elapsed().as_millis();
        return Ok(Ok(outcome));
    }
    let report =
        after_reply.hypotheses.iter().find(|h| h.kind != "observe").cloned().unwrap_or_default();
    outcome.status = Some(report.status.replace('-', "_"));
    outcome.reason = report.reason.clone();
    let after = speculation_run(after_result, after_ms, &after_reply, symbols);
    outcome.new_loops =
        after.loops.iter().filter(|l| !before_loops.contains(&l.qid)).cloned().collect();
    outcome.introduced_loop = Some(!outcome.new_loops.is_empty());
    let after_loop_count = after.loops.len();
    outcome.after = Some(after);
    // A query near its resource limit can flip between two checks of its
    // own, so a close counts only if the query still fails right after.
    let mut closed = before_result != QueryResult::Valid && after_result == QueryResult::Valid;
    if closed {
        let (result, elapsed_ms, reply) =
            speculation_check(air, query, Hypothesis::Observe, loop_threshold, set_rlimit)?;
        closed = result != QueryResult::Valid;
        outcome.recheck = Some(speculation_run(result, elapsed_ms, &reply, symbols));
    }
    outcome.closed = closed;

    // Source for the check's terms, SSA versions included.
    let names = QueryNames::new(symbols, &after_reply.variable_versions, &empty);
    if !matches!(lowered, Hypothesis::Block { .. }) {
        outcome.new_provenance = Some(NewProvenance {
            closing_instantiations: report
                .instances
                .iter()
                .map(|terms| DirectedInstance {
                    qid: quantifier.qid.clone(),
                    terms: terms.iter().map(|term| names.show(term)).collect(),
                    smt_terms: terms.clone(),
                    inference_id: "LLM_DIRECTED",
                })
                .collect(),
            extra_inst_count: report.added,
        });
    }
    let at = symbols
        .and_then(|symbols| symbols.quantifier_site(&quantifier.qid))
        .and_then(|(_, span)| span)
        .map(|span| format!(" at {span}"))
        .unwrap_or_default();
    match &lowered {
        Hypothesis::Instantiate { .. } => {
            if closed {
                outcome.verus_snippet = instance_assert(&quantifier, &subst, &names);
            }
        }
        Hypothesis::Trigger { pattern, .. } => {
            let refs: Vec<&str> = pattern.iter().map(String::as_str).collect();
            if closed && names.pasteable(&refs) {
                let rendered: Vec<String> = refs.iter().map(|p| names.render_plain(p)).collect();
                let annotation = format!("#![trigger {}]", rendered.join(", "));
                outcome.suggestion = Some(format!("add {annotation} to the quantifier{at}"));
                outcome.verus_snippet = Some(annotation);
            }
            if closed {
                // an instance the trigger made, asserted, which needs no
                // change to the quantifier
                outcome.fallback_snippet = report.instances.first().and_then(|terms| {
                    let parsed: Option<Vec<TreeNode>> =
                        terms.iter().map(|term| parse_term(term)).collect();
                    let subst: HashMap<String, TreeNode> = quantifier
                        .binders
                        .iter()
                        .map(|(smt, _)| smt.clone())
                        .zip(parsed?)
                        .collect();
                    instance_assert(&quantifier, &subst, &names)
                });
            }
        }
        Hypothesis::Block { fingerprint, .. } => {
            outcome.blocked = Some(report.blocked);
            outcome.blocked_examples = report
                .instances
                .iter()
                .map(|terms| terms.iter().map(|term| names.show(term)).collect())
                .collect();
            if closed {
                outcome.suggestion = Some(format!(
                    "the quantifier{at} stops looping once its instantiations matching {} are refused: give it a trigger that cannot match that shape",
                    names.show(fingerprint)
                ));
            }
        }
        Hypothesis::Observe => {}
    }

    let mut notes = Vec::new();
    let (with, without) = (result_name(after_result), result_name(before_result));
    match (report.status.as_str(), &lowered) {
        ("applied", Hypothesis::Instantiate { .. }) => notes.push(format!(
            "The directed instance was added; the query answers {with} with it and {without} without it."
        )),
        ("applied", Hypothesis::Trigger { .. }) => notes.push(format!(
            "The speculative trigger matched {} instantiation(s); the query answers {with} with it and {without} without it.",
            report.added
        )),
        ("applied", Hypothesis::Block { .. }) => notes.push(format!(
            "{} instantiation(s) matching the fingerprint were refused; the query answers {with} with the block and {without} without it.",
            report.blocked
        )),
        (status, _) => notes.push(format!(
            "The hypothesis did not apply ({}{}); the query answers {with}.",
            status.replace('-', "_"),
            report.reason.as_deref().map(|r| format!(": {r}")).unwrap_or_default()
        )),
    }
    match &outcome.recheck {
        Some(recheck) if recheck.result == QueryResult::Valid => notes.push(
            "Checked again without the hypothesis, the query passed: it is near its resource limit, so the close is not the hypothesis's and is not reported.".to_owned(),
        ),
        Some(_) => notes.push(
            "Checked again without the hypothesis, the query still fails, so the close is the hypothesis's.".to_owned(),
        ),
        None => {}
    }
    if !outcome.new_loops.is_empty() {
        let qids: Vec<&str> = outcome.new_loops.iter().map(|l| l.qid.as_str()).collect();
        notes.push(format!(
            "It introduced a matching loop: {} kept being instantiated on deeper terms.",
            qids.join(", ")
        ));
    } else if after_loop_count > 0 {
        notes.push(
            "It introduced no matching loop; the check without it had the same ones.".to_owned(),
        );
    } else {
        notes.push("No quantifier kept being instantiated on deeper terms.".to_owned());
    }
    outcome.notes = notes.join(" ");
    outcome.elapsed_ms = start.elapsed().as_millis();
    Ok(Ok(outcome))
}

/// What a scaffold request asks.
struct ScaffoldRequest {
    assert: String,
    assert_id: Option<Vec<u64>>,
    goal: Option<usize>,
    goal_only: bool,
}

/// What one check cost, as cvc5's `(get-info :check-effort)` reported it.
#[derive(Clone, Copy, Serialize)]
struct CheckCost {
    /// Resource units: the units of the query's rlimit budget. Not comparable
    /// unit for unit between consecutive checks on one solver: cvc5's
    /// rewriter and term caches survive `pop`, so a check after another of
    /// like work spends fewer.
    resource_units: u64,
    instantiations: u64,
    inst_rounds: u64,
}

/// One check of a scaffold request.
#[derive(Serialize)]
struct ScaffoldRun {
    result: QueryResult,
    /// The solver's reason for giving up (`incomplete`, `resourceout`, ...).
    #[serde(skip_serializing_if = "Option::is_none")]
    reason: Option<String>,
    elapsed_ms: u128,
    /// None from a cvc5 that does not report `:check-effort`.
    cost: Option<CheckCost>,
    /// For the query's own check: how many checks followed it to find the
    /// earliest failing goal, as Verus does before reporting one. Their
    /// time and cost are not in this run's.
    #[serde(skip_serializing_if = "Option::is_none")]
    rechecks: Option<usize>,
}

/// The goal a scaffold request placed `P` before.
#[derive(Serialize)]
struct ScaffoldTarget {
    /// Empty for a goal Verus emits without an assert id (a loop invariant
    /// at the end of the loop body, `decreases`); `goal` addresses it.
    assert_id: Vec<u64>,
    /// Its index among the query's asserts, which a request's `goal` names.
    goal: usize,
    /// `requested`; `first_failure`, the earliest goal the query's check
    /// fails at, found as Verus finds the error it reports first; or
    /// after a resource limit, which names no goal, `first_failing_alone`,
    /// the first goal whose check alone failed.
    chosen: &'static str,
    /// How many goals were checked alone to find it.
    #[serde(skip_serializing_if = "Option::is_none")]
    goals_probed: Option<usize>,
    /// The goal's error message, such as `assertion failed`.
    description: String,
    span: Option<String>,
    labels: Vec<SourceLabel>,
    /// How often the goal occurs; `P` is placed before each occurrence.
    occurrences: usize,
    /// The span `placement` refers to, when it refers to one: the goal's own,
    /// or for a postcondition the "end of the function body" label's.
    insert_before: Option<String>,
    /// Where `assert(P);` goes in the source: `before_span`, right before
    /// `insert_before`; `end_of_body`, at the end of the function body (a
    /// postcondition); `end_of_loop_body` or `before_loop` (a loop
    /// invariant, checked there, which no span names); `end_of_proof_block`
    /// (the claim of `assert ... by`, checked after that block's steps; a
    /// goal among the steps is `before_span`).
    placement: &'static str,
}

/// The goal's check with `P` assumed, less its check alone, run in that
/// order on the same solver. Instantiations are the steadier comparator:
/// resource units are not comparable between consecutive checks, since
/// cvc5's rewriter and term caches survive `pop`, so the later check of
/// like work spends fewer units and `rlimit_delta` reads low.
#[derive(Serialize)]
struct MarginalCost {
    instantiations_delta: i64,
    /// In resource units, the units of the query's rlimit budget; biased low
    /// by the caches the earlier checks warmed.
    rlimit_delta: i64,
}

/// What the goal's check under `P` drew on, from provenance: the hypotheses
/// that reached the solver in that check, and the quantifiers it
/// instantiated. Not an unsat core: the refutation need not have used every
/// one of them.
#[derive(Serialize)]
struct ScaffoldWhy {
    /// The hypotheses (`requires`, type invariants, ...) in the check.
    explains_goal: Vec<crate::provenance::ResolvedTag>,
    /// The quantifiers instantiated, those with a source span or defining a
    /// function first, at most 12.
    closing_quantifiers: Vec<crate::provenance::ResolvedInstantiation>,
    closing_quantifiers_omitted: usize,
}

#[derive(Serialize)]
struct ScaffoldReport {
    target: ScaffoldTarget,
    /// `P` as it was checked, rendered back from AIR as source.
    lowered_as: String,
    /// Names with more than one reading, and the reading taken.
    choices: Vec<String>,
    /// The query's own check, run to find the goal when none was named.
    #[serde(skip_serializing_if = "Option::is_none")]
    query_check: Option<ScaffoldRun>,
    /// The goal alone: every other goal assumed, nothing added.
    baseline: ScaffoldRun,
    /// `P` asserted in place of the goal. Absent under `goal_only`.
    p_provable: Option<ScaffoldRun>,
    /// The goal with `P` assumed right before it.
    goal_given_p: ScaffoldRun,
    /// `scaffold`, `true_but_unhelpful`, `helpful_but_unprovable`,
    /// `dead_end`, `goal_already_holds`, or under `goal_only`
    /// `goal_closes_given_p` / `goal_open_given_p`. When a check the case
    /// turns on runs out of budget, which proves nothing either way:
    /// `helpful_but_undecided` (the goal closes under `P`; `P`'s check ran
    /// out), `unhelpful_and_undecided` (the goal stays open under `P`; `P`'s
    /// check ran out), `undecided` (the goal's check under `P` ran out), or
    /// under `goal_only` `goal_undecided_given_p`.
    case: &'static str,
    marginal_cost: Option<MarginalCost>,
    /// When the goal closed under `P` in a provenance session: what that
    /// check had and instantiated, not a core.
    why: Option<ScaffoldWhy>,
    /// Why the goal stayed open under `P`, when the solver gave up.
    residual: Option<crate::provenance::ResolvedUnknownReason>,
    /// `assert(P);` to add before `target.insert_before`, when the goal
    /// closes under `P` (and `P` is provable, unless `goal_only`).
    verus_snippet: Option<String>,
    /// The solver's assertion stack before and after every check: equal, or
    /// the session would have ended.
    stack_levels: Option<u64>,
    elapsed_ms: u128,
    restore_ms: u128,
}

struct ArmOutcome {
    run: ScaffoldRun,
    assert_id: Option<Vec<u64>>,
    /// The failing goal's error message, which names a goal without an id.
    error: Option<air::messages::ArcDynMessage>,
    provenance: Option<air::context::ProvenanceInfo>,
    unknown: Option<air::context::UnknownReason>,
}

/// Check `query` once in the retained query's scope and finish it. With
/// `earliest`, a failure is followed by checks for a failing goal before it,
/// as Verus runs them before reporting, until none is left: the goal named
/// is then the earliest failing one, not whichever the model showed first.
/// `Ok(Err)` is a refusal (the query did not type-check, so no scope was
/// opened).
fn scaffold_check(
    air: &mut Context,
    query: &Query,
    rlimit: f32,
    set_rlimit: &impl Fn(&mut Context, f32),
    earliest: bool,
) -> io::Result<Result<ArmOutcome, String>> {
    set_rlimit(air, rlimit);
    let start = Instant::now();
    let outcome = air.check_valid(
        &VirMessageInterface {},
        &QueryDiagnostics::default(),
        query,
        QueryContext::default(),
    );
    let elapsed_ms = start.elapsed().as_millis();
    let provenance = air.take_provenance();
    let unknown = air.take_unknown_reason();
    let effort = air.take_check_effort();
    drop(air.take_matching_loops());
    drop(air.take_difficulty());
    drop(air.take_inst_pressure());
    drop(air.take_nl_frontier());
    let (result, mut assert_id, mut error, has_model) = match outcome {
        ValidityResult::Valid(_) => (QueryResult::Valid, None, None, false),
        ValidityResult::Invalid(model, error, id) => {
            (QueryResult::Invalid, id.map(|id| (*id).clone()), error, model.is_some())
        }
        ValidityResult::Canceled => (QueryResult::ResourceLimit, None, None, false),
        // A query that fails to type-check opens no scope to finish.
        ValidityResult::TypeError(error) => {
            return Ok(Err(format!("AIR rejected the assertion as lowered: {error}")));
        }
        ValidityResult::UnexpectedOutput(error) => return Err(io::Error::other(error)),
    };
    let mut rechecks = None;
    // A recheck needs the model of the failure before it.
    if earliest && has_model {
        let mut count = 0;
        loop {
            count += 1;
            let again =
                air.check_valid_again(&QueryDiagnostics::default(), true, QueryContext::default());
            drop(air.take_provenance());
            drop(air.take_unknown_reason());
            drop(air.take_check_effort());
            drop(air.take_matching_loops());
            drop(air.take_difficulty());
            drop(air.take_inst_pressure());
            drop(air.take_nl_frontier());
            match again {
                ValidityResult::Invalid(model, again_error, id) => {
                    if again_error.is_some() || id.is_some() {
                        assert_id = id.map(|id| (*id).clone());
                        error = again_error;
                    }
                    if model.is_none() {
                        break;
                    }
                }
                ValidityResult::UnexpectedOutput(error) => return Err(io::Error::other(error)),
                // no failing goal before the last one found, or out of budget
                _ => break,
            }
        }
        rechecks = Some(count);
    }
    air.finish_query();
    let reason = unknown.as_ref().map(|u| u.reason.clone()).filter(|r| !r.is_empty());
    let cost = effort.filter(|e| e.unparsed.is_none()).map(|e| CheckCost {
        resource_units: e.resource_units,
        instantiations: e.instantiations,
        inst_rounds: e.inst_rounds,
    });
    Ok(Ok(ArmOutcome {
        run: ScaffoldRun { result, reason, elapsed_ms, cost, rechecks },
        assert_id,
        error,
        provenance,
        unknown,
    }))
}

/// Whether two goal error messages describe the same goal: the same note at
/// the same primary span. A failure's message is the goal's with labels
/// appended, so this is how a failure names a goal without an assert id.
fn same_goal(a: &air::messages::ArcDynMessage, b: &air::messages::ArcDynMessage) -> bool {
    match (a.downcast_ref::<MessageX>(), b.downcast_ref::<MessageX>()) {
        (Some(a), Some(b)) => {
            a.note == b.note
                && a.spans.first().map(|s| &s.as_string) == b.spans.first().map(|s| &s.as_string)
        }
        _ => false,
    }
}

/// One line about a goal, for a refusal that lists them: its index, its
/// assert id, its message and where it is.
fn describe_goal(goal: &air::scaffold::Goal) -> String {
    let message = goal.error.downcast_ref::<MessageX>();
    let note = message.map(|m| m.note.as_str()).unwrap_or("goal");
    let at = message
        .and_then(|m| m.spans.first())
        .map(|s| {
            let s = s.as_string.rsplit('/').next().unwrap_or(&s.as_string);
            format!(" at {}", s.split(" (#").next().unwrap_or(s))
        })
        .unwrap_or_default();
    let id = match &goal.id {
        Some(id) => format!("assert_id {:?}", **id),
        None => "no assert id".to_owned(),
    };
    format!("goal {} ({id}) {note}{at}", goal.index)
}

/// `assert(P);` for the source, from `P` as the request wrote it.
fn assertion_snippet(text: &str) -> String {
    let text = text.trim().trim_end_matches(';').trim();
    let inner = text
        .strip_prefix("assert")
        .map(str::trim_start)
        .and_then(|rest| rest.strip_prefix('('))
        .and_then(|rest| rest.strip_suffix(')'))
        .unwrap_or(text);
    format!("assert({});", inner.trim())
}

/// Whether the source right after `span` (`path:line:col: line:col (#n)`,
/// columns counted in characters from 1, the end just past the span) reads
/// `by`, after the `)` of `assert(` if there is one: the span is then the
/// claim of `assert ... by` or `assert forall ... by`. None when the span or
/// its file cannot be read.
fn followed_by_by(span: &str) -> Option<bool> {
    let span = span.split(" (#").next()?;
    let (start, end) = span.rsplit_once(": ")?;
    let mut start = start.rsplitn(3, ':');
    let (_, _, path) = (start.next()?, start.next()?, start.next()?);
    let (line, col) = end.split_once(':')?;
    let line: usize = line.trim().parse().ok()?;
    let col: usize = col.trim().parse().ok()?;
    let text = std::fs::read_to_string(path).ok()?;
    let mut lines = text.split_inclusive('\n');
    let mut offset = 0;
    for _ in 1..line {
        offset += lines.next()?.len();
    }
    let current = lines.next()?;
    let within = current.char_indices().nth(col.checked_sub(1)?).map_or(current.len(), |(i, _)| i);
    let rest = text[offset + within..].trim_start();
    let rest = rest.strip_prefix(')').unwrap_or(rest).trim_start();
    Some(
        rest.strip_prefix("by")
            .is_some_and(|after| !after.starts_with(|c: char| c.is_alphanumeric() || c == '_')),
    )
}

/// Serve a scaffold request for one query of `bucket`, whose address the
/// caller has checked: read `P`, find the goal, and check the goal alone, `P`
/// in its place, and the goal with `P` assumed. Every check runs in the
/// query's own scope. If the solver's assertion stack is not exactly as
/// before afterwards, `P` or its negation could reach later checks, so that
/// ends the session (`Err`). `Ok(Err(_))` is a refusal to report.
fn serve_scaffold(
    bucket: &RetainedBucket,
    id: QueryId,
    request: ScaffoldRequest,
    set_rlimit: &impl Fn(&mut Context, f32),
) -> io::Result<Result<ScaffoldReport, String>> {
    let mut state =
        bucket.state.lock().map_err(|_| io::Error::other("resident bucket poisoned"))?;
    let (solver, local) = bucket.addresses[id.0];
    let SolverState { air, journal } = &mut state[solver];
    if !matches!(air.get_solver(), SmtSolver::Cvc5) {
        return Ok(Err("scaffold requests need cvc5".to_owned()));
    }
    let Some(symbols) = bucket.symbols.as_ref() else {
        return Ok(Err("this bucket kept no source names to read the assertion with".to_owned()));
    };
    if matches!(
        journal.queries[local].prover,
        vir::def::ProverChoice::BitVector | vir::def::ProverChoice::Singular
    ) {
        return Ok(Err(
            "a bit-vector or Singular query has no spec terms to read the assertion over"
                .to_owned(),
        ));
    }
    let prefix = journal.queries[local].prefix;
    let restore_start = Instant::now();
    journal.restore_prefix(air, prefix)?;
    let restore_ms = restore_start.elapsed().as_millis();
    let query = &journal.queries[local];
    let levels = air.solver_stack_levels();
    let depth = air.scope_depth();
    let start = Instant::now();
    air.set_check_effort(true);
    let report = scaffold_arms(air, query, symbols, &bucket.quantifiers, request, set_rlimit);
    air.set_check_effort(false);
    let report = report?;
    let (levels_after, depth_after) = (air.solver_stack_levels(), air.scope_depth());
    if levels_after != levels || depth_after != depth {
        return Err(io::Error::other(format!(
            "a scaffold check left the solver at {levels_after:?} assertion levels and AIR at \
             {depth_after} scopes, instead of {levels:?} and {depth}"
        )));
    }
    Ok(report.map(|mut report| {
        report.elapsed_ms = start.elapsed().as_millis();
        report.restore_ms = restore_ms;
        report.stack_levels = levels;
        report
    }))
}

fn scaffold_arms(
    air: &mut Context,
    query: &RetainedQuery,
    symbols: &crate::provenance::Symbols,
    quantifiers: &crate::provenance::Quantifiers,
    request: ScaffoldRequest,
    set_rlimit: &impl Fn(&mut Context, f32),
) -> io::Result<Result<ScaffoldReport, String>> {
    use air::scaffold::Arm;
    macro_rules! check {
        ($query:expr) => {
            check!($query, false)
        };
        ($query:expr, $earliest:expr) => {
            match scaffold_check(air, $query, query.rlimit, set_rlimit, $earliest)? {
                Ok(outcome) => outcome,
                Err(refusal) => return Ok(Err(refusal)),
            }
        };
    }
    // Read P before any check, so a refusal costs no solver time.
    let occurrences = air::scaffold::occurrences(&query.query);
    let locals: Vec<_> = query
        .query
        .local
        .iter()
        .filter_map(|decl| match &**decl {
            air::ast::DeclX::Const(x, typ) | air::ast::DeclX::Var(x, typ) => {
                Some((x.clone(), typ.clone()))
            }
            _ => None,
        })
        .collect();
    let lowered = {
        let context: &Context = air;
        let declared = |name: &str| context.declared(name);
        let env = crate::scaffold::Env {
            names: symbols.source_names(),
            crate_name: symbols.crate_name(),
            locals,
            declared: &declared,
            occurrences: &occurrences,
        };
        match crate::scaffold::lower(&request.assert, &env) {
            Ok(lowered) => lowered,
            Err(error) => return Ok(Err(format!("cannot read the assertion: {error}"))),
        }
    };
    let printer = air::printer::Printer::new(
        std::sync::Arc::new(VirMessageInterface {}),
        true,
        SmtSolver::Cvc5,
    );
    let smt = air::printer::node_to_string(&printer.expr_to_node(&lowered.expr));
    let lowered_as = vir::air_names::render_term(&symbols.paste_names(&HashMap::new()), &smt);

    let goals = air::scaffold::goals(&query.query);
    // The goals, for a refusal that asks the caller to name one.
    let listed = || -> String {
        const GOALS_LISTED: usize = 40;
        let listed: Vec<String> = goals.iter().take(GOALS_LISTED).map(describe_goal).collect();
        let more = goals.len().saturating_sub(GOALS_LISTED);
        let more = if more > 0 { format!("; and {more} more") } else { String::new() };
        format!("{}{more}", listed.join("; "))
    };
    let by_id = |id: &[u64]| goals.iter().find(|g| g.id.as_ref().is_some_and(|gid| **gid == id));
    let (goal, chosen, query_check, goals_probed) = match (request.assert_id, request.goal) {
        (Some(id), _) => match by_id(&id) {
            Some(goal) => (goal.clone(), "requested", None, None),
            None => {
                return Ok(Err(format!(
                    "no goal of this query has assert id {id:?}; its goals are {}",
                    listed()
                )));
            }
        },
        (None, Some(index)) => match goals.iter().find(|g| g.index == index) {
            Some(goal) => (goal.clone(), "requested", None, None),
            None => {
                return Ok(Err(format!(
                    "no goal of this query has index {index}; its goals are {}",
                    listed()
                )));
            }
        },
        (None, None) => {
            let outcome = check!(&query.query, true);
            // By id, or by message for a goal without one: a failure's
            // message is the goal's, with labels appended.
            let failed = outcome.assert_id.as_ref().and_then(|id| by_id(id)).or_else(|| {
                let error = outcome.error.as_ref()?;
                goals.iter().find(|g| same_goal(&g.error, error))
            });
            match (failed, outcome.run.result) {
                (Some(goal), _) => (goal.clone(), "first_failure", Some(outcome.run), None),
                (None, QueryResult::Valid) => {
                    return Ok(Err("the query verifies; name a goal with assert_id or goal to \
                                   scaffold it anyway"
                        .to_owned()));
                }
                (None, result) => 'found: {
                    // A resource limit names no goal. Check each goal alone,
                    // in order, every other goal assumed, and take the first
                    // that fails, as the earliest error is the one Verus
                    // reports. Past the budget, list them instead.
                    const GOALS_PROBED: usize = 64;
                    let truth = air::ast_util::mk_true();
                    for (probes, goal) in goals.iter().take(GOALS_PROBED).enumerate() {
                        let alone = air::scaffold::scaffold_query(
                            &query.query,
                            goal.target(),
                            &truth,
                            Arm::GoalGiven,
                        )
                        .expect("a goal of this query");
                        if check!(&alone.query).run.result != QueryResult::Valid {
                            break 'found (
                                goal.clone(),
                                "first_failing_alone",
                                Some(outcome.run),
                                Some(probes + 1),
                            );
                        }
                    }
                    let why = match result {
                        QueryResult::ResourceLimit if goals.len() <= GOALS_PROBED => format!(
                            "the query ran out of budget, yet each of its {} goals holds alone \
                             with the others assumed: the budget goes on the query as a whole, \
                             not on one goal",
                            goals.len()
                        ),
                        QueryResult::ResourceLimit => format!(
                            "the query's check named no failing goal (a resource limit names \
                             none), and of its first {GOALS_PROBED} goals each holds alone"
                        ),
                        _ => format!(
                            "the query's check failed at a goal this worker could not match to \
                             one of its {} asserts, and each of the first {GOALS_PROBED} holds \
                             alone",
                            goals.len()
                        ),
                    };
                    return Ok(Err(format!(
                        "{why}; name one with assert_id or goal to scaffold it: {}",
                        listed()
                    )));
                }
            }
        }
    };
    let rewrite = |arm, p: &air::ast::Expr| {
        air::scaffold::scaffold_query(&query.query, goal.target(), p, arm)
            .expect("a goal of this query")
    };
    let alone = rewrite(Arm::GoalGiven, &air::ast_util::mk_true());
    let given = rewrite(Arm::GoalGiven, &lowered.expr);
    let provable = rewrite(Arm::Provable, &lowered.expr);

    let baseline = check!(&alone.query);
    let p_provable = if request.goal_only { None } else { Some(check!(&provable.query)) };
    let goal_given_p = check!(&given.query);

    let holds = |run: &ScaffoldRun| run.result == QueryResult::Valid;
    // A check that ran out of budget proves nothing either way, so a case
    // turning on one says so rather than calling P unprovable.
    #[derive(Clone, Copy)]
    enum Verdict {
        Holds,
        Fails,
        OutOfBudget,
    }
    let verdict = |run: &ScaffoldRun| match run.result {
        QueryResult::Valid => Verdict::Holds,
        QueryResult::ResourceLimit => Verdict::OutOfBudget,
        _ => Verdict::Fails,
    };
    let case = {
        use Verdict::*;
        match (
            verdict(&baseline.run),
            p_provable.as_ref().map(|p| verdict(&p.run)),
            verdict(&goal_given_p.run),
        ) {
            (Holds, _, _) => "goal_already_holds",
            (_, Some(_), OutOfBudget) => "undecided",
            (_, Some(Holds), Holds) => "scaffold",
            (_, Some(Holds), Fails) => "true_but_unhelpful",
            (_, Some(Fails), Holds) => "helpful_but_unprovable",
            (_, Some(Fails), Fails) => "dead_end",
            (_, Some(OutOfBudget), Holds) => "helpful_but_undecided",
            (_, Some(OutOfBudget), Fails) => "unhelpful_and_undecided",
            (_, None, Holds) => "goal_closes_given_p",
            (_, None, Fails) => "goal_open_given_p",
            (_, None, OutOfBudget) => "goal_undecided_given_p",
        }
    };
    let marginal_cost = match (baseline.run.cost, goal_given_p.run.cost) {
        (Some(before), Some(after)) => Some(MarginalCost {
            instantiations_delta: after.instantiations as i64 - before.instantiations as i64,
            rlimit_delta: after.resource_units as i64 - before.resource_units as i64,
        }),
        _ => None,
    };
    let desc = &query.context.desc;
    let span = &query.context.span.as_string;
    let why = goal_given_p.provenance.filter(|_| holds(&goal_given_p.run)).map(|info| {
        let resolved = symbols.resolve(
            &query.context.fun,
            crate::provenance::QueryProvenance {
                desc: desc.clone(),
                span: span.clone(),
                focus: None,
                round: 0,
                result: "valid".to_owned(),
                sources: info.sources,
                instantiations: info.instantiations,
                variable_versions: info.variable_versions,
                unparsed: info.unparsed,
            },
        );
        let mut closing = resolved.instantiations;
        // user quantifiers and function definitions first, the prelude last
        closing.sort_by_key(|q| match (&q.span, q.role, q.fun.as_deref()) {
            (Some(_), _, _) => 0,
            (None, Some("definition" | "definition_unfold" | "definition_base"), _) => 1,
            (None, _, Some("prelude")) => 3,
            _ => 2,
        });
        const CLOSING_SHOWN: usize = 12;
        let omitted = closing.len().saturating_sub(CLOSING_SHOWN);
        closing.truncate(CLOSING_SHOWN);
        ScaffoldWhy {
            explains_goal: resolved.hypotheses,
            closing_quantifiers: closing,
            closing_quantifiers_omitted: omitted,
        }
    });
    let residual = goal_given_p
        .unknown
        .filter(|u| {
            !holds(&goal_given_p.run) && (u.incomplete_id.is_some() || !u.culprit_qids.is_empty())
        })
        .map(|reason| {
            let mut resolved = quantifiers.resolve_unknown(desc, span, reason);
            resolved.culprits.truncate(20);
            resolved
        });
    let message = given.error.downcast_ref::<MessageX>();
    let labels: Vec<SourceLabel> = message
        .map(|m| {
            m.labels
                .iter()
                .map(|l| SourceLabel { message: l.note.clone(), span: l.span.as_string.clone() })
                .collect()
        })
        .unwrap_or_default();
    let primary = message.and_then(|m| m.spans.first()).map(|s| s.as_string.clone());
    let description = message.map(|m| m.note.clone()).unwrap_or_default();
    // Where the snippet goes. The claim of `assert ... by` is checked after
    // that block's steps: it ends its dead end, and `by` follows its span. A
    // closure body's last assert ends one too, with no `by`; when the source
    // cannot be read, the dead end decides. A postcondition goes at the end
    // of the body, which its label names; a loop invariant at the end of the
    // loop body or before the loop, which no span names, or at the break or
    // continue its span is; anything else, a step of a proof block included,
    // at its own span.
    let claim_of_assert_by =
        given.ends_dead_end && primary.as_deref().and_then(followed_by_by).unwrap_or(true);
    let (insert_before, placement) = if claim_of_assert_by {
        (None, "end_of_proof_block")
    } else if description.contains("postcondition") {
        let end = labels
            .iter()
            .find(|l| l.message.contains("end of the function body"))
            .map(|l| l.span.clone());
        (end.or_else(|| primary.clone()), "end_of_body")
    } else if description == vir::def::INV_FAIL_LOOP_END {
        (None, "end_of_loop_body")
    } else if description == vir::def::INV_FAIL_LOOP_FRONT {
        (None, "before_loop")
    } else {
        // a loop invariant at a break or continue has that statement's span
        (primary.clone(), "before_span")
    };
    let verus_snippet = matches!(case, "scaffold" | "goal_closes_given_p")
        .then(|| assertion_snippet(&request.assert));
    Ok(Ok(ScaffoldReport {
        target: ScaffoldTarget {
            assert_id: goal.id.as_ref().map(|id| (**id).clone()).unwrap_or_default(),
            goal: goal.index,
            chosen,
            goals_probed,
            description,
            span: primary,
            labels,
            occurrences: given.occurrences,
            insert_before,
            placement,
        },
        lowered_as,
        choices: lowered.choices,
        query_check,
        baseline: baseline.run,
        p_provable: p_provable.map(|p| p.run),
        goal_given_p: goal_given_p.run,
        case,
        marginal_cost,
        why,
        residual,
        verus_snippet,
        stack_levels: None,
        elapsed_ms: 0,
        restore_ms: 0,
    }))
}

impl QueryJournal {
    pub(crate) fn new() -> Self {
        Self {
            contexts: Vec::new(),
            queries: Vec::new(),
            applied: 0,
            recorded_in_scope: false,
            base: Vec::new(),
        }
    }

    /// Keep a batch the solver already holds below the journal's scopes, for
    /// requests that read the declarations a query stands on.
    pub(crate) fn record_base(&mut self, commands: Commands) {
        self.base.push(commands);
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
        Self { buckets, info, graphs: KeptGraphs::new(MAX_KEPT_INSTANTIATIONS) }
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
                commands: COMMANDS,
                session,
                process_id: std::process::id(),
                invocation_succeeded,
                provenance: self.info.provenance,
                matching_loops: self.info.matching_loops,
                difficulty: self.info.difficulty,
                spinoff_all: self.info.spinoff_all,
                smt_options: &self.info.smt_options,
                instantiation_replay: self.info.instantiation_replay,
                inst_graph: self.info.inst_graph,
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
                | Request::Bisect { session: requested, .. }
                | Request::Egraph { session: requested, .. }
                | Request::Speculate { session: requested, .. }
                | Request::Scaffold { session: requested, .. }
                | Request::Close { session: requested }
                | Request::InstGraph { session: requested, .. }
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
                Request::Bisect {
                    bucket: bucket_id,
                    query: id,
                    mode,
                    target,
                    budget_checks,
                    kinds,
                    under,
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
                    let budget = budget_checks.unwrap_or(DEFAULT_BISECT_CHECKS);
                    if budget == 0 || budget > MAX_BISECT_CHECKS {
                        send(
                            &mut output,
                            &Response::Error { message: "budget_checks must be between 1 and 256" },
                        )?;
                        continue;
                    }
                    if matches!(mode, BisectMode::Core) && target.is_some() {
                        send(
                            &mut output,
                            &Response::Error { message: "target applies to flip mode only" },
                        )?;
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
                    let restore_start = Instant::now();
                    if let Err(error) = journal.restore_prefix(air, prefix) {
                        return fatal(&mut output, error);
                    }
                    let restore_ms = restore_start.elapsed().as_millis();
                    let query = &journal.queries[local];
                    set_rlimit(air, query.rlimit);
                    let request = BisectRequest { mode, target, budget, kinds, under };
                    let start = Instant::now();
                    let report = match bisect(air, query, bucket.symbols.as_ref(), request) {
                        Ok(mut report) => {
                            report.elapsed_ms = start.elapsed().as_millis();
                            report.restore_ms = restore_ms;
                            report
                        }
                        Err(error) => return fatal(&mut output, error),
                    };
                    send(
                        &mut output,
                        &Response::Bisected { session, bucket: bucket_id, query: id, report },
                    )?;
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
                Request::Speculate {
                    bucket: bucket_id,
                    query: id,
                    hypothesis,
                    loop_threshold,
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
                    if loop_threshold.is_some_and(|n| n == 0 || n > MAX_LOOP_THRESHOLD) {
                        send(
                            &mut output,
                            &Response::Error {
                                message: "loop_threshold must be between 1 and 1000",
                            },
                        )?;
                        continue;
                    }
                    match serve_speculate(bucket, id, hypothesis, loop_threshold, &set_rlimit) {
                        Ok(Ok(outcome)) => send(
                            &mut output,
                            &Response::Speculated {
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
                Request::Scaffold {
                    bucket: bucket_id,
                    query: id,
                    assert,
                    assert_id,
                    goal,
                    goal_only,
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
                    let request = ScaffoldRequest { assert, assert_id, goal, goal_only };
                    match serve_scaffold(bucket, id, request, &set_rlimit) {
                        Ok(Ok(report)) => send(
                            &mut output,
                            &Response::Scaffold {
                                session,
                                bucket: bucket_id,
                                query: id,
                                report: Box::new(report),
                            },
                        )?,
                        Ok(Err(message)) => {
                            send(&mut output, &Response::Error { message: &message })?
                        }
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
                        drop(air.take_difficulty());
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
                    // The graph of the check that decided the verdict: the
                    // certificate attempt's when it closed the query, else
                    // the search's. Later error rounds search again, which
                    // replaces the solver's record, so it is read now. A
                    // query with nothing to instantiate (bit-vector,
                    // nonlinear) gets an empty graph; an error comes only
                    // when cvc5 cannot answer.
                    let graph = air
                        .inst_graph()
                        .then(|| InstantiationGraph::from_live(&air.instantiation_graph()));
                    let (graph_summary, graph_error) = match graph {
                        Some(Ok(graph)) => {
                            let mut summary = graph.summary();
                            let certified = attempted.as_ref().is_some_and(|a| a.closed);
                            summary.check = Some(if certified { "certificate" } else { "search" });
                            self.graphs.insert((bucket_id.0, id.0), graph);
                            (Some(summary), None)
                        }
                        Some(Err(error)) => {
                            self.graphs.remove(&(bucket_id.0, id.0));
                            (None, Some(error))
                        }
                        None => (None, None),
                    };
                    let first_unknown_reason = air.take_unknown_reason();
                    let first_matching_loops = air.take_matching_loops();
                    let first_difficulty = air.take_difficulty();
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
                                drop(air.take_difficulty());
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
                                    // resident rechecks never expand an error
                                    focus: None,
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
                                    // resident rechecks never expand an error
                                    focus: None,
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
                    let difficulty = first_difficulty.and_then(|gradient| {
                        bucket.symbols.as_ref().map(|symbols| {
                            symbols.resolve_difficulty(
                                &query.context.fun,
                                crate::provenance::QueryDifficulty {
                                    desc: query.context.desc.clone(),
                                    span: query.context.span.as_string.clone(),
                                    kind: query.kind.name(),
                                    // resident rechecks never expand an error
                                    focus: None,
                                    round: 0,
                                    result: match result {
                                        QueryResult::Valid => "valid",
                                        QueryResult::Invalid => "invalid",
                                        QueryResult::ResourceLimit => "canceled",
                                    }
                                    .to_owned(),
                                    gradient,
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
                            difficulty: difficulty.as_ref(),
                            certificate: attempted,
                            inst_graph: graph_summary,
                            inst_graph_error: graph_error,
                        },
                    )?;
                }
                Request::InstGraph {
                    bucket: bucket_id,
                    query: id,
                    op,
                    filter,
                    from_qid,
                    to_inst,
                    limit,
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
                    let Some(graph) = self.graphs.get(&(bucket_id.0, id.0)) else {
                        let message = format!(
                            "no instantiation graph for this query; check it in a session that records them. Past {MAX_KEPT_INSTANTIATIONS} instantiations in all, a session drops its least recently used graphs"
                        );
                        send(&mut output, &Response::Error { message: &message })?;
                        continue;
                    };
                    let op = match (op, to_inst) {
                        (GraphOpName::Cycles, _) => GraphOp::Cycles,
                        (GraphOpName::TopCost, _) => GraphOp::TopCost,
                        (GraphOpName::Subgraph, _) => GraphOp::Subgraph,
                        (GraphOpName::Growth, _) => GraphOp::Growth,
                        (GraphOpName::Path, Some(to_inst)) => GraphOp::Path { from_qid, to_inst },
                        (GraphOpName::Path, None) => {
                            send(
                                &mut output,
                                &Response::Error { message: "path requires to_inst" },
                            )?;
                            continue;
                        }
                    };
                    // A filter that stands for nothing would select nothing, and
                    // an op that found nothing reads exactly like a graph that
                    // holds nothing. Refuse it instead, as `path` refuses a
                    // `from_qid` no instantiation belongs to.
                    if let Some(qid) = &filter.quantifier {
                        if !graph.has_quantifier(qid) {
                            let message = format!("no instantiation of {qid} in the graph");
                            send(&mut output, &Response::Error { message: &message })?;
                            continue;
                        }
                    }
                    let mut quantifiers = filter.quantifier.map(|qid| HashSet::from([qid]));
                    if let Some(prefix) = &filter.source_fn {
                        let Some(symbols) = &bucket.symbols else {
                            send(
                                &mut output,
                                &Response::Error {
                                    message: "source_fn needs the bucket's symbols",
                                },
                            )?;
                            continue;
                        };
                        let owned = symbols.quantifiers_of(prefix);
                        quantifiers = Some(match quantifiers {
                            Some(named) => named.intersection(&owned).cloned().collect(),
                            None => owned,
                        });
                    }
                    let filter = GraphFilter { quantifiers, min_depth: filter.min_depth };
                    match graph.query(&op, &filter, limit.unwrap_or(20).clamp(1, 1000)) {
                        Ok(mut reply) => {
                            if let Some(symbols) = &bucket.symbols {
                                reply.answer.annotate(|qid| {
                                    symbols.quantifier_site(qid).map(|(function, span)| Site {
                                        function: function.to_owned(),
                                        span: span.map(str::to_owned),
                                    })
                                });
                            }
                            let response = Response::InstGraph {
                                session,
                                bucket: bucket_id,
                                query: id,
                                result: &reply,
                            };
                            let text =
                                serde_json::to_string(&response).map_err(io::Error::other)?;
                            if text.len() > MAX_GRAPH_REPLY_BYTES {
                                let message = format!(
                                    "the {}-byte answer is over the {MAX_GRAPH_REPLY_BYTES}-byte limit; lower limit or narrow the filter",
                                    text.len()
                                );
                                send(&mut output, &Response::Error { message: &message })?;
                            } else {
                                writeln!(output, "{text}")?;
                                output.flush()?;
                            }
                        }
                        Err(message) => send(&mut output, &Response::Error { message: &message })?,
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kind_names_match_the_batch_run() {
        // A session's records name a check exactly as the batch run does, so
        // a caller reading both cannot see two names for one kind of query.
        for op in [
            QueryOp::SpecTermination,
            QueryOp::Body(Style::Normal),
            QueryOp::Body(Style::RecommendsFollowupFromError),
            QueryOp::Body(Style::RecommendsChecked),
            QueryOp::Body(Style::Expanded),
            QueryOp::Body(Style::CheckApiSafety),
        ] {
            assert_eq!(QueryKind::from_op(&op).name(), op.kind());
        }
    }
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

    /// `COMMANDS` names every request, so a client that reads `ready` and
    /// skips what it does not list never skips one this worker serves. serde
    /// names the variants it knows when it meets one it does not, which keeps
    /// this honest without writing the list out a second time.
    #[test]
    fn commands_names_every_request() {
        let refused = serde_json::from_str::<Request>(r#"{"command": "no_such_request"}"#);
        let Err(error) = refused else { panic!("an unknown command is refused") };
        let error = error.to_string();
        // unknown variant `no_such_request`, expected one of `list`, `check`, ...
        let names: BTreeSet<&str> = error.split('`').skip(3).step_by(2).collect();
        assert!(names.contains("list"), "unexpected serde message: {error}");
        assert_eq!(names, COMMANDS.iter().copied().collect::<BTreeSet<_>>(), "{error}");
    }

    #[test]
    fn kept_graphs_drop_the_least_recently_used_past_the_budget() {
        let graph = |n: usize| {
            let mut lines = vec!["(instantiation-graph".to_owned(), "(quantifier 0 q)".to_owned()];
            lines.extend((0..n).map(|i| format!("(node {i} 0 X 1 0 0 ())")));
            lines.extend(["(dropped 0)".to_owned(), ")".to_owned()]);
            InstantiationGraph::from_live(&lines).unwrap()
        };
        let mut kept = KeptGraphs::new(10);
        kept.insert((0, 0), graph(4));
        kept.insert((0, 1), graph(4));
        // Reading (0, 0) leaves (0, 1) the least recently used.
        assert!(kept.get(&(0, 0)).is_some());
        kept.insert((0, 2), graph(4));
        assert!(kept.get(&(0, 1)).is_none());
        assert!(kept.get(&(0, 0)).is_some() && kept.get(&(0, 2)).is_some());
        assert_eq!(kept.total, 8);
        // A recheck replaces its query's graph, and the graph just kept stays
        // even when it alone is over the budget.
        kept.insert((0, 2), graph(12));
        assert_eq!((kept.graphs.len(), kept.total), (1, 12));
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

    /// A hypothesis's terms may be Verus expressions; they become the SMT
    /// terms the solver reads, names still as written.
    #[test]
    fn surface_expressions_become_smt_terms() {
        let smt = |text: &str| flat(&surface_term(text).unwrap());
        assert_eq!(smt("decode(encode(k))"), "(decode (encode k))");
        assert_eq!(
            smt("f(a + 1, b) == 2 && !g(x) || h(-y) % 3 != 0"),
            "(or (and (= (f (+ a 1) b) 2) (not (g x))) (not (= (mod (h (- y)) 3) 0)))"
        );
        assert_eq!(smt("x ==> y ==> z"), "(=> x (=> y z))");
        assert_eq!(smt("a - b - c"), "(- (- a b) c)");
        assert_eq!(smt("crate::m::f(x@1, #0, _)"), "(crate::m::f x@1 #0 _)");
        assert_eq!(smt("(a * (b / c))"), "(* a (div b c))");
        for bad in ["f(a", "f(a,)", "a +", "a $ b", "(a) b"] {
            assert!(surface_term(bad).is_err(), "{bad}");
        }
    }

    /// Verus boxes a quantifier's variables and a spec function's arguments
    /// into `Poly`, so a term for one is boxed when its sort is concrete, and
    /// a source name is looked up among the scope's declarations.
    #[test]
    fn lowering_boxes_values_where_poly_is_taken() {
        let tree = |text: &str| parse_term(text).unwrap();
        let quantifier = QuantifierSmt {
            qid: "user_q_0".to_owned(),
            binders: vec![("i$".to_owned(), tree("Poly"))],
            triggers: vec![vec![tree("(m!f.? i$)")]],
            body: tree("(> (%I (m!f.? i$)) 0)"),
            in_query: true,
        };
        let mut declared = Declarations::default();
        declared.constants.insert("a!".to_owned(), "Int".to_owned());
        for (f, args, result) in [
            ("m!f.?", vec![POLY], "Int"),
            ("m!s.?", vec![POLY], "Int"),
            (vir::def::BOX_INT, vec!["Int"], POLY),
            (vir::def::UNBOX_INT, vec![POLY], "Int"),
        ] {
            let args = args.into_iter().map(str::to_owned).collect();
            declared.functions.insert(f.to_owned(), (args, result.to_owned()));
        }
        let mut names = SourceNames::new();
        for (symbol, name) in [("a!", "a"), ("i$", "i"), ("m!f.", "m::f"), ("m!s.", "m::s")] {
            names.insert(symbol.to_owned(), vir::air_names::SourceName::Symbol(name.to_owned()));
        }
        let lowering = Lowering::new(&quantifier, declared, &[&names]);
        let lower = |text: &str, want: Option<&str>| flat(&lowering.term_as(text, want).unwrap());
        assert_eq!(lower("a", Some(POLY)), "(I a!)");
        assert_eq!(lower("a + 1", Some(POLY)), "(I (+ a! 1))");
        assert_eq!(lower("f(i)", None), "(m!f.? i$)");
        assert_eq!(lower("s(s(a))", Some(POLY)), "(I (m!s.? (I (m!s.? (I a!)))))");
        assert_eq!(lower("f(i) > 0", None), "(> (m!f.? i$) 0)");
        // a hole has no sort, so it is left as it is
        assert_eq!(lower("f(s(_))", None), "(m!f.? (I (m!s.? _)))");
        assert_eq!(lower("(m!f.? (I a!))", Some("Int")), "(m!f.? (I a!))");
    }

    #[test]
    fn type_guards_are_dropped_from_an_instance() {
        let node = |text: &str| parse_term(text).unwrap();
        let guard = format!("({} x T)", vir::def::HAS_TYPE);
        assert_eq!(
            flat(&without_type_guards(&node(&format!("(=> {guard} (> (f x) 0))")))),
            "(> (f x) 0)"
        );
        assert_eq!(
            flat(&without_type_guards(&node(&format!("(=> (and {guard} (p x)) (q x))")))),
            "(=> (p x) (q x))"
        );
        assert_eq!(flat(&without_type_guards(&node("(or a b)"))), "(or a b)");
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
                difficulty: false,
                spinoff_all: false,
                multiple_errors: 2,
                input_files: Vec::new(),
                smt_options: Vec::new(),
                instantiation_replay: false,
                inst_graph: false,
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
