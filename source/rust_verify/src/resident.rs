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
//!
//! An `ablate` request delta-debugs a retained query's axioms and hypotheses
//! (see `air::bisect`). Its declaration-prefix axioms are asserted below the
//! query's scope, so the solver's journal is popped back to the prelude and
//! the prefix asserted again in a scope of the ablation's own, each axiom a
//! function or broadcast group owns guarded by that group's switch. After the
//! search, vacuity probes ask goal by goal, last goal first, whether the
//! assumptions are contradictory where that goal is checked, and for a
//! vacuous goal whether every goal is, with the contradiction already there
//! before the first goal of every path. The witness is checked once more the
//! ordinary way, with
//! its removed axioms never asserted. Every scope is popped before the reply;
//! the next request restores its own prefix.
//!
//! The catalogue names each query's `fingerprint` (see `Fingerprint`): what
//! a caller compares the query by across compilations of edited source, to
//! tell the queries an edit left alone from those it changed. Under
//! `VERUS_RESIDENT_RETAIN_ONLY` the invocation retains every selected query
//! and checks none (`ready.retain_only`), which is what such a caller opens a
//! session on the edited source with; it then carries what it knew about the
//! unchanged queries over, a pinned rung with a `pin` request. Since no check
//! decides which recommends follow-ups to retain, such a session retains
//! every one a check could have added, including those for functions whose
//! checks pass (a caller checks a follow-up when its function's body fails,
//! as the batch run does), and none of the `--expand-errors` queries, which
//! only a failed check can name.

mod twin;

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
    /// The prelude the solver started from, which a bit-vector solver does
    /// not get. Hashed into fingerprints only: it is not fixed text, since it
    /// reads the crate's word size (`global size_of usize`).
    prelude: Option<Commands>,
    /// The bucket's context from before the journal began (fuel constants,
    /// datatypes, function declarations, module-level broadcast groups).
    /// Never replayed: it lives below every scope. Kept so a twin or a
    /// speculative probe can find what it declares.
    base: Vec<Commands>,
    contexts: Vec<Vec<Commands>>,
    queries: Vec<RetainedQuery>,
    applied: usize,
    /// Whether a query has been recorded since the open scope began.
    recorded_in_scope: bool,
}

/// The requests this worker serves, as `ready` reports them. A client reads
/// the list rather than guessing from `protocol`: requests reach releases in
/// their own order, and a worker that does not know a request answers exactly
/// as it does a malformed one. Every `Request` variant belongs here, in the
/// protocol's snake case, which `resident_ready_lists_the_requests_it_serves`
/// checks by sending each one.
const COMMANDS: &[&str] = &[
    "list",
    "check",
    "bisect",
    "ablate",
    "egraph",
    "scaffold",
    "close",
    "inst_graph",
    "ladder",
    "twin",
    "speculate",
    "pin",
];

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
    /// Switch the query's declaration-prefix axioms (grouped by the function
    /// or broadcast group that owns them) and its hypotheses on and off to
    /// find a witness: what to remove for the query to be proved, or what
    /// its proof cannot lose (see `air::bisect`, ablation).
    Ablate {
        session: String,
        bucket: BucketIndex,
        query: QueryId,
        mode: AblateMode,
        /// At most this many search probes, 1..=`MAX_BISECT_CHECKS`. The
        /// vacuity and absence checks that follow the search are extra.
        budget_checks: Option<usize>,
        /// Also switch the query's own hypotheses (requires, type invariants,
        /// fuel, trait bounds). Default true.
        hypotheses: Option<bool>,
        /// Units (by index, as `candidate_units` of an earlier reply about
        /// this query lists them) to leave switched on: they are no
        /// candidates. Lets a caller search past a witness the absence
        /// check disowned.
        exclude: Option<Vec<usize>>,
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
    /// Check the query and a copy of it with one edit, and compare the two
    /// checks (see `twin`).
    Twin {
        session: String,
        bucket: BucketIndex,
        query: QueryId,
        edit: twin::TwinEdit,
        /// How many quantifiers and assertions the reply lists at most:
        /// 1 to 200, default 20.
        limit: Option<usize>,
        /// Check the query once more after the twin and compare it with the
        /// first check.
        #[serde(default)]
        recheck_base: bool,
    },
    /// Check the query once per instantiation strategy, each alone or
    /// alongside the default schedule (see `serve_ladder`), and pin the
    /// first that proves it.
    Ladder {
        session: String,
        bucket: BucketIndex,
        query: QueryId,
        /// The rungs to try, in order, each at most once. Default: every
        /// rung, in `Rung::LADDER` order, or `Rung::ALONGSIDE` alongside. An
        /// empty list runs nothing. `ematch` or `pool` named alongside runs
        /// the default schedule itself, and is allowed as a baseline.
        rungs: Option<Vec<Rung>>,
        /// A rung's rlimit, in `#[verifier::rlimit]` units, above 0 and at
        /// most `MAX_RUNG_RLIMIT`. Default: the query's own, or
        /// `DEFAULT_RUNG_RLIMIT` for a query without one.
        #[serde(default)]
        budgets: HashMap<Rung, f32>,
        /// Try the rungs after the first that proves the query too.
        #[serde(default)]
        run_all: bool,
        /// Run each rung's strategy alongside the default schedule rather
        /// than alone.
        #[serde(default)]
        alongside: bool,
        /// Pin the first rung that proved the query, or remove the pin when
        /// none did. Default true; false leaves the pin as it was.
        pin: Option<bool>,
    },
    /// Give the query the rung its checks try first, as a ladder request
    /// pins one: what a caller carries over from a session on the source
    /// before an edit for a query the edit left unchanged. Refused, as a
    /// ladder would skip it, when the solver cannot run the rung (see
    /// `check_pin`).
    Pin {
        session: String,
        bucket: BucketIndex,
        query: QueryId,
        rung: Rung,
        #[serde(default)]
        alongside: bool,
        /// The pin's budget in `#[verifier::rlimit]` units, above 0, at
        /// most `MAX_RUNG_RLIMIT`, and at least one cvc5 resource unit.
        rlimit: f32,
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
            air::bisect::UnitKind::Axiom => unreachable!("bisect probers switch no prefix axioms"),
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
    fingerprint: Fingerprint,
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
        } else {
            // Dropping the context pops nothing, so pop its journal first:
            // the solver, and its log, end at the prelude. A complaint from
            // a solver about to be closed is of no use.
            let (mut air, mut journal) = (air, journal);
            let _ = journal.restore_prefix(&mut air, 0);
        }
        states.append(&mut spinoffs);
        let mut queries = Vec::new();
        let mut addresses = Vec::new();
        let mut cert_keys = Vec::new();
        let mut repeats = std::collections::HashMap::new();
        for (solver, state) in states.iter().enumerate() {
            let fingerprints = state.journal.fingerprints();
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
                    fingerprint: fingerprints[local],
                });
                addresses.push((solver, local));
            }
        }
        Self { id, queries, addresses, cert_keys, state: Mutex::new(states), symbols, quantifiers }
    }
}

/// What a caller compares a retained query by across compilations: FNV-1a
/// over the AIR of the declarations asserted below it (its prefix: the
/// prelude, which reads the crate's word size, the bucket's base context and
/// the journal scopes up to the query's own, none of which a bit-vector
/// query's solver gets) and
/// over the query itself, each printed as AIR. The printer writes an
/// assertion's labels as their notes and never a span, so a query that only
/// moved to other lines prints the same, and generated local names carry
/// per-function counters, not line numbers. A quantifier's triggers are
/// hashed sorted and once each (see `sort_patterns`), and its `:qid` and
/// `:skolemid` without the counter they end in, which is the bucket's, not
/// the function's (see `forget_quantifier_counters`). The body hash also
/// covers the query's rlimit, since the budget a query checks at can change
/// its verdict. Two queries with the same function, kind and description and
/// the same fingerprint are, to the solver, the same query up to the names of
/// their quantifiers: what a caller carries over by fingerprint must not name
/// a quantifier by its `:qid`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize)]
pub(crate) struct Fingerprint {
    prefix: u64,
    body: u64,
}

/// FNV-1a over printed AIR.
struct Fnv(u64);

impl Fnv {
    fn new() -> Self {
        Self(0xcbf2_9ce4_8422_2325)
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 ^= u64::from(*byte);
            self.0 = self.0.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }

    fn node(&mut self, node: &TreeNode) {
        let mut node = node.clone();
        sort_patterns(&mut node);
        forget_quantifier_counters(&mut node);
        self.write(air::printer::node_to_string(&node).as_bytes());
        self.write(b"\n");
    }

    fn commands(&mut self, printer: &air::printer::Printer, commands: &Commands) {
        for command in commands.iter() {
            match &**command {
                CommandX::Global(decl) => self.node(&printer.decl_to_node(decl)),
                CommandX::CheckValid(query) => self.node(&printer.query_to_node(query)),
                CommandX::Push => self.write(b"push\n"),
                CommandX::Pop => self.write(b"pop\n"),
                CommandX::SetOption(name, value) => {
                    self.write(name.as_bytes());
                    self.write(b"=");
                    self.write(value.as_bytes());
                    self.write(b"\n");
                }
                #[cfg(feature = "singular")]
                CommandX::CheckSingular(_) => self.write(b"singular\n"),
            }
        }
    }
}

/// Put every annotated term's `:pattern` groups in the order of their text,
/// once each, in place: `(! e :pattern (p) :pattern (q) :qid ...)` keeps its
/// other annotations where they are, and the patterns take the place of the
/// first. Automatic trigger selection lists a quantifier's triggers in an
/// order that varies from one compilation to the next, and sometimes lists
/// one twice; neither changes the query.
fn sort_patterns(node: &mut TreeNode) {
    let TreeNode::List(items) = node else { return };
    for item in items.iter_mut() {
        sort_patterns(item);
    }
    if !matches!(items.first(), Some(TreeNode::Atom(bang)) if bang == "!") {
        return;
    }
    let mut rest = Vec::with_capacity(items.len());
    let mut patterns: Vec<(String, TreeNode)> = Vec::new();
    let mut first = None;
    let mut i = 0;
    while i < items.len() {
        if matches!(&items[i], TreeNode::Atom(key) if key == ":pattern") && i + 1 < items.len() {
            first.get_or_insert(rest.len());
            patterns.push((air::printer::node_to_string(&items[i + 1]), items[i + 1].clone()));
            i += 2;
        } else {
            rest.push(items[i].clone());
            i += 1;
        }
    }
    let Some(first) = first else { return };
    patterns.sort_by(|a, b| a.0.cmp(&b.0));
    patterns.dedup_by(|a, b| a.0 == b.0);
    let tail = rest.split_off(first);
    for (_, pattern) in patterns {
        rest.push(TreeNode::Atom(":pattern".to_owned()));
        rest.push(pattern);
    }
    rest.extend(tail);
    *items = rest;
}

/// Drop the counter from every user quantifier's `:qid` and `:skolemid`, in
/// place: `user_f_12` becomes `user_f_`. The counter is kept per bucket, not
/// per function (`new_user_qid`), so it moves with every quantifier lowered
/// before this one in the bucket: one added to an earlier function, or a
/// recommends query lowered for an earlier function, as a retain-only session
/// lowers some a checked session does not and a check that starts or stops
/// failing adds or drops one. None of those changes this quantifier, whose
/// own text is hashed with its name.
fn forget_quantifier_counters(node: &mut TreeNode) {
    let TreeNode::List(items) = node else { return };
    for item in items.iter_mut() {
        forget_quantifier_counters(item);
    }
    if !matches!(items.first(), Some(TreeNode::Atom(bang)) if bang == "!") {
        return;
    }
    let skolem_prefix = air::def::mk_skolem_id(air::profiler::USER_QUANT_PREFIX);
    for i in 1..items.len() {
        if !matches!(&items[i - 1], TreeNode::Atom(key) if key == ":qid" || key == ":skolemid") {
            continue;
        }
        let TreeNode::Atom(name) = &mut items[i] else { continue };
        if !name.starts_with(air::profiler::USER_QUANT_PREFIX) && !name.starts_with(&skolem_prefix)
        {
            continue;
        }
        let without = name.trim_end_matches(|c: char| c.is_ascii_digit()).len();
        if without < name.len() && name[..without].ends_with('_') {
            name.truncate(without);
        }
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
    /// (bucket, query) -> the rung its checks try first, as its last ladder
    /// request found.
    pins: HashMap<(usize, usize), Pin>,
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
    /// Whether cvc5 solvers were launched with every instantiation strategy a
    /// ladder request can run (`VERUS_RESIDENT_STRATEGY_LADDER`).
    pub(crate) strategy_ladder: bool,
    /// Whether the invocation retained its queries without checking any of
    /// them (`VERUS_RESIDENT_RETAIN_ONLY`): its `invocation_succeeded` says
    /// nothing about them, and no verdict is on record.
    pub(crate) retain_only: bool,
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
        strategy_ladder: bool,
        retain_only: bool,
        input_files: &'a [String],
        buckets: &'a [BucketDescription],
    },
    Queries {
        session: &'a str,
        buckets: &'a [BucketDescription],
    },
    Pinned {
        session: &'a str,
        bucket: BucketIndex,
        query: QueryId,
        pin: Pin,
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
        /// Present when this check tried the query's pinned rung first. When
        /// that attempt closed the query, `provenance` and `difficulty` are
        /// its own, the check that decided.
        pinned: Option<PinnedAttempt>,
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
    Ablated {
        session: &'a str,
        bucket: BucketIndex,
        query: QueryId,
        #[serde(flatten)]
        report: Box<AblateReport>,
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
    Twin {
        session: &'a str,
        bucket: BucketIndex,
        query: QueryId,
        #[serde(flatten)]
        report: Box<twin::TwinReport>,
    },
    Scaffold {
        session: &'a str,
        bucket: BucketIndex,
        query: QueryId,
        #[serde(flatten)]
        report: Box<ScaffoldReport>,
    },
    Laddered {
        session: &'a str,
        bucket: BucketIndex,
        query: QueryId,
        #[serde(flatten)]
        report: LadderReport,
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

/// One of cvc5's quantifier instantiation strategies, which a ladder request
/// runs alone or alongside the default schedule (`:quant-strategy`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
enum Rung {
    Ematch,
    Conflict,
    Pool,
    Enum,
    Mbqi,
}

impl Rung {
    /// E-matching first, as the default schedule runs it, then the
    /// strategies Verus's schedule leaves off or has nothing for, roughly by
    /// the effort each spends.
    const LADDER: [Rung; 5] = [Rung::Ematch, Rung::Conflict, Rung::Pool, Rung::Enum, Rung::Mbqi];

    /// Alongside the default schedule, E-matching and pools are the schedule
    /// itself, so only these add anything.
    const ALONGSIDE: [Rung; 3] = [Rung::Conflict, Rung::Enum, Rung::Mbqi];

    /// The `:quant-strategy` value, which cvc5's replies also name it by.
    fn name(self) -> &'static str {
        match self {
            Rung::Ematch => "ematch",
            Rung::Conflict => "conflict",
            Rung::Pool => "pool",
            Rung::Enum => "enum",
            Rung::Mbqi => "mbqi",
        }
    }
}

/// The most rlimit a ladder request may give one rung, in
/// `#[verifier::rlimit]` units.
const MAX_RUNG_RLIMIT: f32 = 1000.0;

/// The rlimit a rung runs at when the request gives it no budget and the
/// query has none (`#[verifier::rlimit(infinity)]`): a strategy that makes
/// new terms with each instance, as enumerative instantiation can, would
/// otherwise never answer, and the session with it.
const DEFAULT_RUNG_RLIMIT: f32 = crate::config::DEFAULT_RLIMIT_SECS;

/// The rung a query's checks try first, run as the ladder that found it ran
/// it: alone, or alongside the default schedule, at the budget it proved the
/// query at (`#[verifier::rlimit]` units, always finite).
#[derive(Clone, Copy, Serialize)]
struct Pin {
    rung: Rung,
    alongside: bool,
    rlimit: f32,
}

/// A pinned rung's attempt: `closed` when that strategy, run as pinned,
/// proved the query, otherwise the verdict comes from the ordinary check that
/// followed. `rlimit` is the pin's budget or the query's, whichever is
/// smaller. `elapsed_ms` is the attempt alone and is part of the check's.
#[derive(Clone, Copy, Serialize)]
struct PinnedAttempt {
    rung: Rung,
    alongside: bool,
    rlimit: f32,
    closed: bool,
    elapsed_ms: u128,
    /// cvc5 resource units the attempt spent, when cvc5 said.
    resource_units: Option<u64>,
}

/// The reply to a ladder request.
#[derive(Serialize)]
struct LadderReport {
    /// Whether each rung ran alongside the default schedule, not alone.
    alongside: bool,
    /// The first rung, in the order tried, whose strategy proved the query.
    solved_by: Option<Rung>,
    /// One per requested rung, in the order requested.
    rungs: Vec<RungReport>,
    /// The strategies the solver has a module for. A session launched
    /// without the strategy ladder has E-matching and pools only.
    available: Vec<String>,
    /// The rung this query's checks try first, after this request.
    pinned: Option<Pin>,
    elapsed_ms: u128,
    restore_ms: u128,
}

/// What one rung's check answered. Alone, the rung ran its strategy without
/// the others, so this says what that strategy does by itself, not what it
/// adds to the default schedule; alongside, it says the latter.
#[derive(Serialize)]
struct RungReport {
    rung: Rung,
    /// `valid`, `invalid` (a counterexample), `unknown` (the strategy gave
    /// up), `resource_limit`, `unavailable` (the solver has no module for
    /// it; not run) or `not_run` (an earlier rung proved the query).
    verdict: &'static str,
    /// The rlimit it ran at, in `#[verifier::rlimit]` units; absent for a
    /// rung that did not run.
    #[serde(skip_serializing_if = "Option::is_none")]
    rlimit: Option<f32>,
    /// cvc5's resource budget for the check, null for none.
    resource_limit: Option<u64>,
    /// cvc5 resource units the check spent, preprocessing included.
    resource_units: Option<u64>,
    /// Instantiations the rung's strategy added.
    instantiations: Option<u64>,
    /// Instantiations added outside the ladder's strategies (modules the
    /// options enable besides them).
    other_instantiations: Option<u64>,
    /// Instantiation rounds that sent lemmas.
    rounds: Option<u64>,
    /// For `unknown` and `resource_limit`: the solver's reason.
    reason_unknown: Option<String>,
    /// For `unknown`: cvc5's `IncompleteId`, as `why_unknown` reports it.
    incomplete_id: Option<String>,
    /// For `invalid` and `unknown`: the first assertion the answer failed.
    assert_id: Option<Vec<u64>>,
    elapsed_ms: u128,
}

impl RungReport {
    fn skipped(rung: Rung, verdict: &'static str) -> Self {
        RungReport {
            rung,
            verdict,
            rlimit: None,
            resource_limit: None,
            resource_units: None,
            instantiations: None,
            other_instantiations: None,
            rounds: None,
            reason_unknown: None,
            incomplete_id: None,
            assert_id: None,
            elapsed_ms: 0,
        }
    }
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
            UnitKind::Axiom => unreachable!("bisect probers switch no prefix axioms"),
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

#[derive(Clone, Copy, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum AblateMode {
    /// `load_bearing` when the probe with nothing removed is valid, else
    /// `minimal_removal`.
    Auto,
    /// The smallest set whose removal makes the query valid.
    MinimalRemoval,
    /// For a valid query, the smallest set its proof cannot lose.
    LoadBearing,
}

const DEFAULT_ABLATE_CHECKS: usize = 32;
/// At most this many members of a vacuous load-bearing set are probed for
/// their part in the contradiction.
const MAX_PARTICIPATION_CHECKS: usize = 16;
/// At most this many goals are probed for vacuity per configuration.
const MAX_VACUITY_GOAL_CHECKS: usize = 8;

/// One switchable part an ablation names: a group of declaration-prefix
/// axioms, or one of the query's hypotheses.
#[derive(Serialize)]
struct AblationUnit {
    /// Position among the query's units; probes name units by it.
    index: usize,
    /// `axiom_group` or `hypothesis`.
    kind: &'static str,
    /// An axiom group's owner (a function or broadcast group), or a
    /// hypothesis's kind (`requires`, `type_invariant`, `fuel`, `trait_bound`).
    name: String,
    /// `broadcast` for a broadcast lemma's or group's axioms; otherwise the
    /// roles the encoder recorded for the group's quantifiers (`definition`,
    /// `definition_unfold`, `definition_base`, `return_type_invariant`, and
    /// `contract` for the requires and ensures a call of the function uses).
    #[serde(skip_serializing_if = "Vec::is_empty")]
    roles: Vec<&'static str>,
    #[serde(skip_serializing_if = "Option::is_none")]
    span: Option<String>,
    /// How many prefix axioms an axiom group switches.
    #[serde(skip_serializing_if = "Option::is_none")]
    axioms: Option<usize>,
    /// The `:qid`s of the unit's quantifiers.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    qids: Vec<String>,
    /// Instances of those quantifiers during the probe with nothing removed,
    /// when the solver reports them (cvc5). Zero: no part in that search.
    #[serde(skip_serializing_if = "Option::is_none")]
    instantiations_before: Option<u64>,
    /// The same during the probe of the witness, for a unit it keeps.
    #[serde(skip_serializing_if = "Option::is_none")]
    instantiations_with_witness: Option<u64>,
}

/// A probe's answer, with cvc5's `IncompleteId` for an incomplete one.
#[derive(Serialize)]
struct AblationVerdict {
    #[serde(flatten)]
    verdict: ProbeVerdict,
    #[serde(skip_serializing_if = "Option::is_none")]
    incomplete_id: Option<String>,
}

/// Whether the assumptions are contradictory where a goal is checked:
/// probes with one goal replaced by `false` and the other goals switched
/// off, where `valid` means no path reaches that goal consistently, so the
/// goal is proved vacuously. Goals are probed last first, up to
/// `MAX_VACUITY_GOAL_CHECKS` per configuration, and the scan stops at the
/// first probe that runs out of resources. With quantifiers in the context
/// the solver can rarely show assumptions consistent, so `unknown` is the
/// usual answer when no contradiction was found.
#[derive(Serialize)]
struct Vacuity {
    /// Nothing removed: `valid` when some goal's assumptions are
    /// contradictory, `invalid` when every goal's were shown consistent, else
    /// `unknown`.
    before: ProbeVerdict,
    /// The same for the witness configuration; absent without a witness.
    #[serde(skip_serializing_if = "Option::is_none")]
    witness: Option<ProbeVerdict>,
    /// Either configuration has a goal with contradictory assumptions.
    vacuous: bool,
    /// That goal: the witness configuration's when it is vacuous (the one
    /// `participated` is about), else the one found with nothing removed.
    #[serde(skip_serializing_if = "Option::is_none")]
    goal: Option<AblationGoal>,
    /// With a vacuous `goal`, the same configuration with every goal `false`
    /// at once, which counts only the first goal on each path: `valid` when
    /// the assumptions before the first goal of every path contradict, so
    /// every goal is vacuous, as when the requires or the broadcast lemmas
    /// in use contradict each other. Otherwise the contradiction was not
    /// found without what the vacuous goal's path adds: a branch condition
    /// that cannot hold (as in a proof by contradiction), an `assume`, or a
    /// called lemma's `ensures`.
    #[serde(skip_serializing_if = "Option::is_none")]
    every_goal: Option<ProbeVerdict>,
    /// Goals in the query.
    goals: usize,
    /// Goals no vacuity probe reached when none was found vacuous: past the
    /// cap, or after a probe that ran out of resources.
    #[serde(skip_serializing_if = "is_zero")]
    goals_unchecked: u64,
    /// For a vacuous load-bearing set, the members whose removal alone makes
    /// the assumptions at `goal` consistent again: the ones the
    /// contradiction needs.
    participated: Vec<usize>,
    /// Members not probed for participation, past `MAX_PARTICIPATION_CHECKS`.
    #[serde(skip_serializing_if = "is_zero")]
    participation_unchecked: u64,
}

/// The witness configuration checked the ordinary way, with the removed
/// axioms and hypotheses never asserted rather than switched off.
#[derive(Serialize)]
struct AbsenceCheck {
    result: QueryResult,
    /// Whether it agrees with the witness probe about validity.
    agrees: bool,
    elapsed_ms: u128,
}

/// The reply to an ablate request. Every verdict after `verdict_before` is
/// about a query with fewer axioms or hypotheses than the original, never
/// about the original itself.
#[derive(Serialize)]
struct AblateReport {
    requested: AblateMode,
    /// The mode searched, after `auto`.
    mode: AblateMode,
    /// `found`, `already_at_target`, `unreachable`, `not_valid`,
    /// `no_candidates` or `budget_exhausted`, as for bisect.
    status: &'static str,
    /// `minimal_removal_that_proves`, `load_bearing_set`, or `none`.
    result: &'static str,
    /// The probe with nothing removed. Axioms and hypotheses are guarded, so
    /// near the resource limit it can differ from an ordinary check.
    verdict_before: Option<AblationVerdict>,
    /// minimal_removal: the units whose removal makes the query valid.
    /// load_bearing: the units that must stay, every other candidate removed.
    witness: Vec<AblationUnit>,
    /// Every candidate, by the index `probes` and `participated` use, so a
    /// reply without a witness still says what was tried, and a caller can
    /// name units to `exclude`.
    candidate_units: Vec<AblationUnit>,
    /// The request's `exclude`: units left switched on.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    excluded: Vec<usize>,
    /// The probe of the witness configuration; null without a witness.
    verdict_with_witness: Option<AblationVerdict>,
    verdict_all_removed: Option<ProbeVerdict>,
    /// Restoring (minimal_removal) or removing (load_bearing) any one member
    /// was probed and loses the result. False when the budget ran out first.
    minimal: bool,
    non_monotone: bool,
    /// load_bearing only: the search started from the units the probe with
    /// nothing removed instantiated (and those with no quantifier), because
    /// they alone kept the query valid.
    started_from_instantiated: bool,
    vacuity: Vacuity,
    #[serde(skip_serializing_if = "Option::is_none")]
    absence_check: Option<AbsenceCheck>,
    /// Search probes, counted against `budget_checks`.
    checks_used: usize,
    /// Vacuity probes and the absence check, not counted against it.
    extra_checks: usize,
    budget_checks: usize,
    candidates: usize,
    axiom_groups: usize,
    /// Axioms in the query's declaration prefix, and how many of them the
    /// axiom groups switch; the rest (datatypes, the encoding's own axioms)
    /// stay asserted.
    prefix_axioms: usize,
    switched_axioms: usize,
    probes: Vec<BisectProbe>,
    elapsed_ms: u128,
    restore_ms: u128,
}

struct AblateRequest {
    mode: AblateMode,
    budget: usize,
    hypotheses: bool,
    exclude: Vec<usize>,
}

/// A goal the vacuity probes name.
#[derive(Serialize)]
struct AblationGoal {
    /// Position among the query's units.
    index: usize,
    /// The goal's error message (`assertion failed`, ...).
    description: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    span: Option<String>,
}

/// What the vacuity probes found in one configuration.
struct VacuityScan {
    /// `valid` when some goal's assumptions are contradictory (that goal's
    /// probe), `invalid` when every goal's were shown consistent, else
    /// `unknown`.
    answer: air::bisect::Answer,
    /// The goal whose assumptions are contradictory.
    goal: Option<usize>,
    /// Goals not probed, past `MAX_VACUITY_GOAL_CHECKS` or after a probe
    /// that ran out of resources.
    unchecked: usize,
}

/// Ask goal by goal whether the assumptions left under `removed` are
/// contradictory where the goal is checked: that goal replaced by `false`,
/// every other goal switched off, so an earlier goal reaches it only as the
/// fact it leaves. `goals` is the order to probe in, last goal first:
/// assumptions accumulate along a path, so a later goal is the likelier to
/// see a contradiction. Stops at the first goal whose probe is `valid`, and
/// at the first that runs out of resources: the goals before it rarely fare
/// better under the same budget, and each probe can cost the whole budget.
/// Without goals, one probe asks about the assumptions alone.
fn scan_vacuity(
    prober: &mut air::bisect::Prober<'_>,
    goals: &[usize],
    removed: &[usize],
    checks: &mut usize,
) -> Result<VacuityScan, String> {
    use air::bisect::Answer;
    let count = prober.units().len();
    let mask = |off: &[usize]| {
        let mut mask = vec![false; count];
        for &i in off {
            mask[i] = true;
        }
        mask
    };
    if goals.is_empty() {
        let answer = prober.probe_vacuity(&mask(removed))?;
        *checks += 1;
        return Ok(VacuityScan { answer, goal: None, unchecked: 0 });
    }
    let mut unknown = None;
    for (n, &goal) in goals.iter().enumerate() {
        if n >= MAX_VACUITY_GOAL_CHECKS {
            let unchecked = goals.len() - n;
            let answer =
                unknown.unwrap_or_else(|| Answer::Unknown(format!("{unchecked} goals unchecked")));
            return Ok(VacuityScan { answer, goal: None, unchecked });
        }
        let mut off = removed.to_vec();
        off.extend(goals.iter().copied().filter(|&g| g != goal));
        let answer = prober.probe_vacuity(&mask(&off))?;
        *checks += 1;
        if answer == Answer::Valid {
            return Ok(VacuityScan { answer, goal: Some(goal), unchecked: 0 });
        }
        if answer.class() == "resource_limit" {
            let unchecked = goals.len() - n - 1;
            return Ok(VacuityScan { answer, goal: None, unchecked });
        }
        if answer != Answer::Invalid && unknown.is_none() {
            unknown = Some(answer);
        }
    }
    Ok(VacuityScan { answer: unknown.unwrap_or(Answer::Invalid), goal: None, unchecked: 0 })
}

/// The sorted indices a probe mask switches off.
fn switched_off(disabled: &[bool]) -> Vec<usize> {
    disabled.iter().enumerate().filter(|(_, off)| **off).map(|(i, _)| i).collect()
}

/// Run one ablation over `query` in `air`, whose journal must be popped back
/// to the prelude, given the declarations of the query's prefix. Every scope
/// it opens is popped before it returns.
fn ablate(
    air: &mut Context,
    prefix: &[air::ast::Decl],
    query: &RetainedQuery,
    symbols: Option<&crate::provenance::Symbols>,
    request: AblateRequest,
) -> io::Result<AblateReport> {
    use air::bisect::{Answer, Mode, ProbeDetail, Status, Target, UnitKind};
    let group_of = |axiom: &air::ast::Axiom| -> Option<String> {
        symbols.and_then(|symbols| symbols.axiom_group(axiom)).map(str::to_owned)
    };
    let mut prober = air
        .ablate_query(prefix, &mut |axiom| group_of(axiom), &query.query)
        .map_err(|error| io::Error::other(error.to_string()))?;
    let units = prober.units().to_vec();
    let count = units.len();
    let no_candidate = |&&i: &&usize| {
        i >= count
            || match units[i].kind {
                UnitKind::Axiom => false,
                UnitKind::Hypothesis => !request.hypotheses,
                UnitKind::Goal | UnitKind::Fact => true,
            }
    };
    if let Some(index) = request.exclude.iter().find(no_candidate) {
        // A bad request, not a failure of the session.
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "exclude names unit {index}, which is no candidate: the query has {count} \
                 units, its goals and facts are never switched, and its hypotheses are not \
                 with hypotheses: false"
            ),
        ));
    }
    let mask = |removed: &[usize]| {
        let mut mask = vec![false; count];
        for &i in removed {
            mask[i] = true;
        }
        mask
    };
    let mut details: HashMap<Vec<usize>, ProbeDetail> = HashMap::new();
    let (before, detail) = prober.probe_detailed(&mask(&[])).map_err(io::Error::other)?;
    details.insert(Vec::new(), detail);
    let mode = match request.mode {
        AblateMode::Auto if before == Answer::Valid => AblateMode::LoadBearing,
        AblateMode::Auto => AblateMode::MinimalRemoval,
        mode => mode,
    };
    let candidates: Vec<usize> = (0..count)
        .filter(|&i| match units[i].kind {
            UnitKind::Axiom => true,
            UnitKind::Hypothesis => request.hypotheses,
            UnitKind::Goal | UnitKind::Fact => false,
        })
        .filter(|i| !request.exclude.contains(i))
        .collect();
    let search_mode = match mode {
        AblateMode::LoadBearing => Mode::Core,
        _ => Mode::Flip(Target::Valid),
    };
    // Should removing everything overshoot, single units are tried most
    // instantiated first: a matching loop's lemma leads. A core search first
    // tries keeping only what the probe with nothing removed instantiated,
    // with the units that have no quantifier to instantiate: a proof's
    // instantiation stream names what it used, and ddmin then shrinks a set
    // of a few dozen rather than every group in the prefix.
    let mut order = candidates.clone();
    let mut core_start = Vec::new();
    if let Some(counts) = details.get(&Vec::new()).and_then(|d| d.instantiations.as_ref()) {
        let weight = |i: usize| -> u64 {
            units[i].qids.iter().map(|qid| counts.get(qid).copied().unwrap_or(0)).sum()
        };
        order.sort_by_key(|&i| std::cmp::Reverse(weight(i)));
        core_start = candidates
            .iter()
            .copied()
            .filter(|&i| units[i].qids.is_empty() || weight(i) > 0)
            .collect();
    }
    let outcome = air::bisect::search_ordered(
        search_mode,
        count,
        &candidates,
        &order,
        &core_start,
        request.budget,
        Some(before),
        &mut |disabled| -> Result<Answer, String> {
            let (answer, detail) = prober.probe_detailed(disabled)?;
            details.insert(switched_off(disabled), detail);
            Ok(answer)
        },
    )
    .map_err(io::Error::other)?;
    // The witness configuration: the units it switches off.
    let witness_removed = (outcome.status == Status::Found).then(|| match mode {
        AblateMode::LoadBearing => {
            candidates.iter().copied().filter(|i| !outcome.set.contains(i)).collect::<Vec<_>>()
        }
        _ => outcome.set.clone(),
    });

    // Goal units, last goal first.
    let goals: Vec<usize> = (0..count).filter(|&i| units[i].kind == UnitKind::Goal).rev().collect();
    let mut extra_checks = 0;
    let vacuity_before =
        scan_vacuity(&mut prober, &goals, &[], &mut extra_checks).map_err(io::Error::other)?;
    let mut vacuity_witness = None;
    let mut participated = Vec::new();
    let mut participation_unchecked = 0;
    if let Some(removed) = &witness_removed {
        let scan = scan_vacuity(&mut prober, &goals, removed, &mut extra_checks)
            .map_err(io::Error::other)?;
        // A removal leaves its members out of the contradiction by
        // definition; only kept members can take part in it. Each is tried
        // at the goal the scan found contradictory.
        if scan.answer == Answer::Valid && mode == AblateMode::LoadBearing {
            let others: Vec<usize> =
                goals.iter().copied().filter(|&g| Some(g) != scan.goal).collect();
            for (n, &member) in outcome.set.iter().enumerate() {
                if n >= MAX_PARTICIPATION_CHECKS {
                    participation_unchecked = (outcome.set.len() - n) as u64;
                    break;
                }
                let mut without = removed.clone();
                without.extend(&others);
                without.push(member);
                let answer = prober.probe_vacuity(&mask(&without)).map_err(io::Error::other)?;
                extra_checks += 1;
                if answer != Answer::Valid {
                    participated.push(member);
                }
            }
        }
        vacuity_witness = Some(scan);
    }
    // Where a goal is vacuous, whether every goal is: every goal false at
    // once counts only the first goal on each path, so this is valid only
    // when the contradiction is there before any path's first goal.
    let vacuous_config = match &vacuity_witness {
        Some(scan) if scan.answer == Answer::Valid => witness_removed.clone(),
        _ if vacuity_before.answer == Answer::Valid => Some(Vec::new()),
        _ => None,
    };
    let every_goal = match vacuous_config {
        // with one goal, the scan's probe was this one
        Some(_) if goals.len() == 1 => Some(Answer::Valid),
        Some(removed) => {
            let answer = prober.probe_vacuity(&mask(&removed)).map_err(io::Error::other)?;
            extra_checks += 1;
            Some(answer)
        }
        None => None,
    };
    drop(prober);

    let absence_check = match &witness_removed {
        Some(removed) => {
            let probed_valid = outcome.after == Some(Answer::Valid);
            let check =
                absence_check(air, prefix, query, &group_of, &units, removed, probed_valid)?;
            extra_checks += 1;
            Some(check)
        }
        None => None,
    };

    let fun = &query.context.fun;
    let instantiations = |index: usize, removed: &[usize]| -> Option<u64> {
        let unit = &units[index];
        if unit.qids.is_empty() {
            return None;
        }
        let counts = details.get(removed)?.instantiations.as_ref()?;
        Some(unit.qids.iter().map(|qid| counts.get(qid).copied().unwrap_or(0)).sum())
    };
    let describe = |index: usize| {
        let unit = &units[index];
        let (kind, name, span) = match unit.kind {
            UnitKind::Axiom => {
                let name = unit.group.clone().unwrap_or_default();
                let span = symbols.and_then(|s| s.function_span(&name)).map(str::to_owned);
                ("axiom_group", name, span)
            }
            _ => {
                let found = match &unit.tag {
                    Some(air::def::ProvenanceTag::Hyp(air::def::HypId(k))) => {
                        symbols.and_then(|symbols| symbols.hypothesis(fun, *k))
                    }
                    _ => None,
                };
                match found {
                    Some((kind, span)) => ("hypothesis", kind.to_owned(), Some(span.to_owned())),
                    None => ("hypothesis", "hypothesis".to_owned(), None),
                }
            }
        };
        let mut roles: Vec<&'static str> = Vec::new();
        let broadcast = unit.tag.as_ref().is_some_and(|tag| {
            symbols.is_some_and(|symbols| symbols.broadcast_owner(tag).is_some())
        });
        if unit.kind == UnitKind::Axiom && broadcast {
            // A lemma's group also defines its `ens%` predicate, a
            // `definition` that is not what the lemma is.
            roles.push("broadcast");
        } else if unit.kind == UnitKind::Axiom {
            for qid in &unit.qids {
                if let Some(role) = symbols.and_then(|s| s.quantifier_role(qid)) {
                    if !roles.contains(&role) {
                        roles.push(role);
                    }
                }
            }
        }
        let kept_by_witness = mode == AblateMode::LoadBearing && outcome.set.contains(&index);
        AblationUnit {
            index,
            kind,
            name,
            roles,
            span,
            axioms: (unit.kind == UnitKind::Axiom).then_some(unit.axioms),
            qids: unit.qids.clone(),
            instantiations_before: instantiations(index, &[]),
            instantiations_with_witness: match (&witness_removed, kept_by_witness) {
                (Some(removed), true) => instantiations(index, removed),
                _ => None,
            },
        }
    };
    let verdict = |answer: &Answer, removed: &[usize]| AblationVerdict {
        verdict: answer.into(),
        incomplete_id: details.get(removed).and_then(|d| d.incomplete_id.clone()),
    };
    let describe_goal = |index: usize| {
        let message = units[index].error.as_ref().and_then(|e| e.downcast_ref::<MessageX>());
        AblationGoal {
            index,
            description: message.map(|m| m.note.clone()).unwrap_or_default(),
            span: message.and_then(|m| m.spans.first()).map(|s| s.as_string.clone()),
        }
    };
    let vacuity = {
        let witness_vacuous =
            vacuity_witness.as_ref().is_some_and(|scan| scan.answer == Answer::Valid);
        let vacuous = vacuity_before.answer == Answer::Valid || witness_vacuous;
        let goal = match (&vacuity_witness, witness_vacuous) {
            (Some(scan), true) => scan.goal,
            _ => vacuity_before.goal,
        };
        let unchecked = vacuity_witness.as_ref().map_or(0, |scan| scan.unchecked);
        Vacuity {
            before: (&vacuity_before.answer).into(),
            witness: vacuity_witness.as_ref().map(|scan| (&scan.answer).into()),
            vacuous,
            goal: goal.map(describe_goal),
            every_goal: every_goal.as_ref().map(ProbeVerdict::from),
            goals: goals.len(),
            goals_unchecked: if vacuous {
                0
            } else {
                vacuity_before.unchecked.max(unchecked) as u64
            },
            participated,
            participation_unchecked,
        }
    };
    let prefix_axioms =
        prefix.iter().filter(|decl| matches!(&***decl, air::ast::DeclX::Axiom(_))).count();
    Ok(AblateReport {
        requested: request.mode,
        mode,
        status: match outcome.status {
            Status::Found => "found",
            Status::AlreadyAtTarget => "already_at_target",
            Status::Unreachable => "unreachable",
            Status::NotValid => "not_valid",
            Status::NoCandidates => "no_candidates",
            Status::BudgetExhausted => "budget_exhausted",
        },
        result: match (outcome.status, mode) {
            (Status::Found, AblateMode::LoadBearing) => "load_bearing_set",
            (Status::Found, _) => "minimal_removal_that_proves",
            _ => "none",
        },
        verdict_before: outcome.before.as_ref().map(|answer| verdict(answer, &[])),
        witness: outcome.set.iter().map(|&i| describe(i)).collect(),
        candidate_units: candidates.iter().map(|&i| describe(i)).collect(),
        excluded: request.exclude.clone(),
        verdict_with_witness: match (&outcome.after, &witness_removed) {
            (Some(answer), Some(removed)) => Some(verdict(answer, removed)),
            _ => None,
        },
        verdict_all_removed: outcome.all_removed.as_ref().map(ProbeVerdict::from),
        minimal: outcome.minimal,
        non_monotone: outcome.non_monotone,
        started_from_instantiated: outcome.hint_accepted,
        vacuity,
        absence_check,
        checks_used: outcome.probes.len(),
        extra_checks,
        budget_checks: request.budget,
        candidates: candidates.len(),
        axiom_groups: units.iter().filter(|u| u.kind == UnitKind::Axiom).count(),
        prefix_axioms,
        switched_axioms: units.iter().map(|u| u.axioms).sum(),
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

/// Check `query` the ordinary way in a scope of its own, with its prefix
/// asserted except the axiom groups `removed` names, and without the
/// hypotheses it names: the differential against switching them off. The
/// scope is popped before this returns.
fn absence_check(
    air: &mut Context,
    prefix: &[air::ast::Decl],
    query: &RetainedQuery,
    group_of: &dyn Fn(&air::ast::Axiom) -> Option<String>,
    units: &[air::bisect::Unit],
    removed: &[usize],
    probed_valid: bool,
) -> io::Result<AbsenceCheck> {
    use air::ast::DeclX;
    let groups: HashSet<&str> = removed.iter().filter_map(|&i| units[i].group.as_deref()).collect();
    let hypotheses: Vec<&air::def::ProvenanceTag> = removed
        .iter()
        .filter(|&&i| units[i].kind == air::bisect::UnitKind::Hypothesis)
        .filter_map(|&i| units[i].tag.as_ref())
        .collect();
    // As the prober switches them: prefix axioms by group, the query's own
    // axioms by hypothesis tag only.
    let kept_prefix = |decl: &air::ast::Decl| match &**decl {
        DeclX::Axiom(axiom) => {
            !group_of(axiom).is_some_and(|group| groups.contains(group.as_str()))
        }
        _ => true,
    };
    let kept_local = |decl: &air::ast::Decl| match &**decl {
        DeclX::Axiom(axiom) => !axiom.tag.as_ref().is_some_and(|tag| hypotheses.contains(&tag)),
        _ => true,
    };
    let local: Vec<air::ast::Decl> =
        query.query.local.iter().filter(|d| kept_local(d)).cloned().collect();
    let stripped = std::sync::Arc::new(air::ast::QueryX {
        local: std::sync::Arc::new(local),
        assertion: query.query.assertion.clone(),
    });
    let start = Instant::now();
    air.push();
    let mut asserted = Ok(());
    for decl in prefix.iter().filter(|d| kept_prefix(d)) {
        if let Err(error) = air.global(decl) {
            asserted = Err(error);
            break;
        }
    }
    let outcome = match asserted {
        Ok(()) => air.check_valid(
            &VirMessageInterface {},
            &QueryDiagnostics::default(),
            &stripped,
            QueryContext::default(),
        ),
        Err(error) => ValidityResult::TypeError(error),
    };
    drop(air.take_provenance());
    drop(air.take_unknown_reason());
    drop(air.take_matching_loops());
    drop(air.take_difficulty());
    drop(air.take_inst_pressure());
    let result = match outcome {
        ValidityResult::Valid(_) => Ok(QueryResult::Valid),
        ValidityResult::Canceled => Ok(QueryResult::ResourceLimit),
        ValidityResult::Invalid(..) => Ok(QueryResult::Invalid),
        ValidityResult::TypeError(error) => Err(io::Error::other(error.to_string())),
        ValidityResult::UnexpectedOutput(error) => Err(io::Error::other(error)),
    };
    // Every answer, `valid` included, leaves the query open until finished,
    // as the check request does. The errors end the session.
    if result.is_ok() {
        air.finish_query();
    }
    air.pop();
    let result = result?;
    Ok(AbsenceCheck {
        agrees: (result == QueryResult::Valid) == probed_valid,
        result,
        elapsed_ms: start.elapsed().as_millis(),
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
    /// Each variable's SSA symbol where a snippet goes, by its AIR name. A
    /// snippet naming another version of it would read as this one there.
    live: Option<&'a HashMap<String, String>>,
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
                live: None,
            },
            None => Self {
                symbols: None,
                shown: Cow::Borrowed(empty),
                plain: Cow::Borrowed(empty),
                versions,
                live: None,
            },
        }
    }

    /// These names, for snippets pasted where each variable is `live`'s.
    fn at(self, live: &'a HashMap<String, String>) -> Self {
        Self { live: Some(live), ..self }
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

    /// Whether `terms` paste as source together: each renders as source, no
    /// variable appears in them at two assignment versions, which would read
    /// alike, and none at a version other than the one where the snippet
    /// goes, which it would read as.
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
                if self.live.and_then(|live| live.get(base)).is_some_and(|here| here != atom) {
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
    // An assert goes before the goal the check failed at (the query's last
    // goal when it names none), where each variable holds the version then.
    let goal = before.assert_id.clone().map(std::sync::Arc::new);
    let live = air::GoalScope::of(&query.query, goal.as_ref()).live();
    let names =
        QueryNames::new(bucket.symbols.as_ref(), &reading.variable_versions, &empty).at(&live);
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

/// How cvc5 begins the `mismatch` reason for a variable its formula no
/// longer binds.
const UNBOUND_VARIABLE: &str = "the formula binds no variable named ";

/// The variable an instantiation named that cvc5's formula no longer binds,
/// when cvc5 refused the instance for that.
fn unbound_variable(reply: &SpeculationReply) -> Option<String> {
    reply
        .hypotheses
        .iter()
        .find(|h| h.kind == "instantiate" && h.status == "mismatch")
        .and_then(|h| h.reason.as_deref()?.strip_prefix(UNBOUND_VARIABLE))
        .map(str::to_owned)
}

/// The most rounds of rising depth a probe may ask to make a matching loop.
const MAX_LOOP_THRESHOLD: u32 = 1000;
/// The most quantifiers a probe lists as candidates.
const MAX_CANDIDATES: usize = 40;

const SPECULATION_CAVEAT: &str = "The hypothesis was sent in the query's own scope and popped right after the check, so the session's solver state is unchanged. A closed verdict is not a verification result: paste the snippet into the source and verify it normally.";

/// A hypothesis as a `speculate` request names it. A term is a Verus
/// expression, read as a scaffold request reads an assertion (see
/// `crate::scaffold`) at the goal the query's check fails at, so a mutable
/// local reads as its value there; or an SMT term in the solver's spelling,
/// as the `smt_*` fields of other replies give them. An instantiation's
/// terms stand where the quantifier is instantiated, so they never name its
/// variables; a trigger's are over its variables, which shadow locals of the
/// same name. A variable of the quantifier may be named by its source name
/// or its own.
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
#[derive(Clone, Debug, Deserialize)]
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
    /// `applied`; `rejected` (the instantiation funnel refused the directed
    /// instance: it was made already, it is a lemma already sent, it
    /// simplifies to true, or the instantiation level limit refused a term;
    /// `reason` says which); `mismatch` (the terms do not fit the
    /// variables); `unusable` (the pattern cannot be a trigger);
    /// `no_quantifier` (cvc5 holds no formula with the qid, see `notes`);
    /// `could_not_lower` (a term that cannot be read in the query's scope,
    /// or that the solver cannot read); `pending` (no instantiation round
    /// reached e-matching, for instance because conflict-based
    /// instantiation closed every check first)
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
    /// How names in the hypothesis's Verus terms were read, where more than
    /// one reading was possible.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    readings: Vec<String>,
    /// Variables of the quantifier that cvc5 eliminated before the search
    /// (an equality in its body fixes each), so the formula it holds no
    /// longer binds them; the directed instance was sent without them.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    eliminated: Vec<String>,
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
            readings: Vec::new(),
            eliminated: Vec::new(),
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

/// What the query's scope declares, with sorts: constants and variables
/// (each version of a variable too), and functions (datatype constructors
/// and fields included) with their argument and result sorts. The prelude
/// reaches each solver outside the journal; `Lowering` asks the AIR
/// context about its names.
#[derive(Default)]
struct Declarations {
    constants: HashMap<String, String>,
    functions: HashMap<String, (Vec<String>, String)>,
    /// Each variable's SSA symbol at the goal, by its AIR name.
    live: HashMap<String, String>,
}

impl Declarations {
    fn of(
        decls: &[&Decl],
        query: &Query,
        live: HashMap<String, String>,
        versions: &VariableVersions,
    ) -> Self {
        let mut out = Self { live, ..Self::default() };
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
        for (ssa, (variable, _)) in versions {
            if let Some(sort) = out.constants.get(variable).cloned() {
                out.constants.insert(ssa.clone(), sort);
            }
        }
        out
    }

    fn declares(&self, symbol: &str) -> bool {
        self.constants.contains_key(symbol) || self.functions.contains_key(symbol)
    }
}

/// Each of `binders`, by its own name and by its source name: its own name.
fn binder_names(binders: &[(String, TreeNode)], names: &[&SourceNames]) -> HashMap<String, String> {
    let mut out: HashMap<String, String> =
        binders.iter().map(|(smt, _)| (smt.clone(), smt.clone())).collect();
    for names in names {
        for (smt, _) in binders {
            if let Some(source) = vir::air_names::source_symbol(names, smt) {
                out.entry(source).or_insert_with(|| smt.clone());
            }
        }
    }
    out
}

/// SMT-LIB's own operators, which head an SMT term rather than a call.
const SMT_OPERATORS: &[&str] = &[
    "+", "-", "*", "/", "div", "mod", "<", "<=", ">", ">=", "=", "distinct", "and", "or", "not",
    "=>", "ite", "_",
];

/// Turns the terms of a hypothesis written in the solver's spelling, and its
/// fingerprints, into terms the solver reads: names resolved, and values
/// boxed into `Poly` or unboxed out of it where a function, operator or
/// variable takes the other, as Verus's encoding does.
struct Lowering<'a> {
    /// A variable of the quantifier, by its own name and by its source
    /// name: its own name. Empty for terms that stand outside it.
    binders: HashMap<String, String>,
    /// Each variable's sort, by its own name.
    binder_sorts: HashMap<String, String>,
    declared: Declarations,
    /// A declared symbol by its source name, whole and by its last path
    /// segment. Only symbols an encoder minted for the name itself count,
    /// not the helpers named after it (a function's `req%`, `ens%`). A
    /// variable counts as its symbol at the goal.
    by_source: HashMap<String, BTreeSet<String>>,
    /// What the AIR context declares a name as: the prelude's names.
    context: &'a dyn Fn(&str) -> Option<air::context::Declared>,
}

impl<'a> Lowering<'a> {
    /// `binders` are the quantifier's variables when the terms are over
    /// them (a trigger), and none when they stand outside it.
    fn new(
        binders: &[(String, TreeNode)],
        declared: Declarations,
        names: &[&SourceNames],
        context: &'a dyn Fn(&str) -> Option<air::context::Declared>,
    ) -> Self {
        let binder_sorts = binders.iter().map(|(smt, sort)| (smt.clone(), flat(sort))).collect();
        let mut by_source: HashMap<String, BTreeSet<String>> = HashMap::new();
        let symbols: Vec<&String> =
            declared.constants.keys().chain(declared.functions.keys()).collect();
        for names in names {
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
                let target = declared.live.get(symbol).unwrap_or(symbol).clone();
                let last = source.rsplit("::").next().unwrap_or(&source).to_string();
                by_source.entry(last).or_default().insert(target.clone());
                by_source.entry(source).or_default().insert(target);
            }
        }
        Self { binders: binder_names(binders, names), binder_sorts, declared, by_source, context }
    }

    /// A function's argument and result sorts, the journal's declarations
    /// first, then the AIR context's.
    fn function(&self, head: &str) -> Option<(Vec<String>, String)> {
        self.declared.functions.get(head).cloned().or_else(|| match (self.context)(head) {
            Some(air::context::Declared::Fun(params, ret)) => {
                Some((params.iter().map(sort_name).collect(), sort_name(&ret)))
            }
            _ => None,
        })
    }

    /// A symbol's sort, when it is a variable or constant.
    fn constant(&self, atom: &str) -> Option<String> {
        self.binder_sorts.get(atom).or_else(|| self.declared.constants.get(atom)).cloned().or_else(
            || match (self.context)(atom) {
                Some(air::context::Declared::Var(typ)) => Some(sort_name(&typ)),
                _ => None,
            },
        )
    }

    fn known(&self, atom: &str) -> bool {
        self.binder_sorts.contains_key(atom)
            || self.declared.declares(atom)
            || self.declared.live.contains_key(atom)
            || (self.context)(atom).is_some()
    }

    /// Whether `text` is a Verus expression rather than an SMT term. An SMT
    /// term is a symbol the scope or the solver declares, or one no Rust
    /// name could be (`$`, `a!`); or an application headed by an SMT
    /// operator or a declared function.
    fn reads_as_verus(&self, text: &str) -> bool {
        let text = text.trim();
        match parse_term(text) {
            Some(TreeNode::Atom(atom)) => {
                !self.known(&atom)
                    && atom.chars().all(|c| c.is_ascii_alphanumeric() || "_:@".contains(c))
            }
            Some(TreeNode::List(items)) if text.starts_with('(') => match items.first() {
                Some(TreeNode::Atom(head)) => {
                    !(self.known(head) || SMT_OPERATORS.contains(&head.as_str()))
                }
                _ => true,
            },
            _ => true,
        }
    }

    fn atom(&self, atom: &str) -> Result<String, String> {
        if let Some(binder) = self.binders.get(atom) {
            return Ok(binder.clone());
        }
        // a variable, spelled as AIR declares it, is its symbol at the goal
        if let Some(live) = self.declared.live.get(atom) {
            return Ok(live.clone());
        }
        if self.known(atom) || is_literal(atom) {
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
        self.function(&head).is_some().then_some(head)
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
                let sort = self.constant(atom).or_else(|| match atom.as_str() {
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
        let (wants, sort): (Vec<Option<String>>, Option<String>) = match self.function(head) {
            Some((params, result)) if params.len() == typed.len() => {
                (params.into_iter().map(Some).collect(), Some(result))
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

/// The AIR type of a sort as the solver is sent it.
fn typ_of_sort(sort: &str) -> air::ast::Typ {
    use air::ast::TypX;
    std::sync::Arc::new(match sort {
        "Int" => TypX::Int,
        "Bool" => TypX::Bool,
        "Real" => TypX::Real,
        other => TypX::Named(std::sync::Arc::new(other.to_owned())),
    })
}

/// A query's local constants and variables, with their types.
fn query_locals(query: &Query) -> Vec<(air::ast::Ident, air::ast::Typ)> {
    query
        .local
        .iter()
        .filter_map(|decl| match &**decl {
            DeclX::Const(x, typ) | DeclX::Var(x, typ) => Some((x.clone(), typ.clone())),
            _ => None,
        })
        .collect()
}

/// Reads a hypothesis's Verus terms as a scaffold request reads an assertion,
/// then as the lowered query reads them at the goal: each mutable local at
/// its version there.
struct VerusReader<'e> {
    env: crate::scaffold::Env<'e>,
    goal: &'e air::GoalScope,
    printer: air::printer::Printer,
}

impl VerusReader<'_> {
    fn read(
        &self,
        text: &str,
        want: Option<&str>,
        readings: &mut Vec<String>,
    ) -> Result<TreeNode, String> {
        let want = want.map(typ_of_sort);
        let lowered = crate::scaffold::lower_term(text, &self.env, want.as_ref())?;
        readings.extend(lowered.choices);
        Ok(self.printer.expr_to_node(&self.goal.lower_expr(&lowered.expr)))
    }
}

/// A term of a hypothesis, of sort `want` when given, in the solver's
/// spelling: a Verus expression through `reader` (when source names were
/// recorded), else as `lowering` reads SMT terms.
fn read_term(
    text: &str,
    want: Option<&str>,
    lowering: &Lowering,
    reader: Option<&VerusReader>,
    readings: &mut Vec<String>,
) -> Result<TreeNode, String> {
    match reader {
        Some(reader) if lowering.reads_as_verus(text) => reader.read(text, want, readings),
        _ => lowering.term_as(text, want),
    }
}

/// Whether `request` fits `quantifier`, checked before any solver time is
/// spent: an instantiation names each variable once, by its own name or its
/// source name, and a trigger has terms. For an instantiation, the variable
/// each name means.
fn check_hypothesis(
    request: &HypothesisRequest,
    quantifier: &QuantifierSmt,
    names: &[&SourceNames],
) -> Result<HashMap<String, String>, (&'static str, String)> {
    let qid = &quantifier.qid;
    match request {
        HypothesisRequest::Instantiation { subst, .. } => {
            let binders = binder_names(&quantifier.binders, names);
            let mut meant: HashMap<String, String> = HashMap::new();
            let mut seen: HashSet<&str> = HashSet::new();
            for name in subst.keys() {
                let Some(smt) = binders.get(name.as_str()) else {
                    let binders: Vec<&str> =
                        quantifier.binders.iter().map(|(smt, _)| smt.as_str()).collect();
                    return Err((
                        "mismatch",
                        format!("{qid} binds no variable {name}; it binds {}", binders.join(", ")),
                    ));
                };
                if !seen.insert(smt.as_str()) {
                    return Err(("mismatch", format!("two terms for the variable {smt}")));
                }
                meant.insert(name.clone(), smt.clone());
            }
            let missing: Vec<String> = quantifier
                .binders
                .iter()
                .filter(|(smt, _)| !seen.contains(smt.as_str()))
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
            Ok(meant)
        }
        HypothesisRequest::TriggerPattern { pattern, .. } if pattern.terms().is_empty() => {
            Err(("mismatch", "the pattern has no terms".to_string()))
        }
        HypothesisRequest::TriggerPattern { .. } | HypothesisRequest::BlockCycle { .. } => {
            Ok(HashMap::new())
        }
    }
}

/// The hypothesis in the solver's spelling, for an instantiation its term
/// for each variable, and how names were read where several readings were
/// possible; or why it cannot be sent. `meant` is `check_hypothesis`'s.
fn lower_hypothesis(
    request: &HypothesisRequest,
    quantifier: &QuantifierSmt,
    meant: &HashMap<String, String>,
    lowering: &Lowering,
    reader: Option<&VerusReader>,
) -> Result<(Hypothesis, HashMap<String, TreeNode>, Vec<String>), (&'static str, String)> {
    let qid = quantifier.qid.clone();
    let mut readings = Vec::new();
    match request {
        HypothesisRequest::Instantiation { subst, .. } => {
            let mut terms: HashMap<String, TreeNode> = HashMap::new();
            for (name, text) in subst {
                let smt = &meant[name];
                let sort = quantifier.binders.iter().find(|(v, _)| v == smt).map(|(_, s)| flat(s));
                let term = read_term(text, sort.as_deref(), lowering, reader, &mut readings)
                    .map_err(|e| ("could_not_lower", e))?;
                terms.insert(smt.clone(), term);
            }
            let subst = quantifier
                .binders
                .iter()
                .map(|(smt, _)| (smt.clone(), flat(&terms[smt])))
                .collect();
            Ok((Hypothesis::Instantiate { qid, subst }, terms, readings))
        }
        HypothesisRequest::TriggerPattern { pattern, .. } => {
            let pattern: Vec<String> = pattern
                .terms()
                .into_iter()
                .map(|term| {
                    read_term(term, None, lowering, reader, &mut readings).map(|node| flat(&node))
                })
                .collect::<Result<_, _>>()
                .map_err(|e| ("could_not_lower", e))?;
            Ok((
                Hypothesis::Trigger { qid, vars: quantifier.binders.clone(), pattern },
                HashMap::new(),
                readings,
            ))
        }
        HypothesisRequest::BlockCycle { fingerprint, .. } => {
            // A fingerprint's holes are no Verus, so it is read as SMT or in
            // the small surface syntax `surface_term` reads.
            let fingerprint =
                flat(&lowering.term_as(fingerprint, None).map_err(|e| ("could_not_lower", e))?);
            Ok((Hypothesis::Block { qid, fingerprint }, HashMap::new(), readings))
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
/// reported about it, and the goal it failed at, if it names one. Rounds for
/// further errors are not run, and nothing is saved as a certificate. The
/// caller has restored the query's prefix.
fn speculation_check(
    air: &mut Context,
    query: &RetainedQuery,
    hypothesis: Hypothesis,
    loop_threshold: Option<u32>,
    set_rlimit: &impl Fn(&mut Context, f32),
) -> io::Result<(QueryResult, u128, SpeculationReply, Option<air::ast::AssertId>)> {
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
    let (result, failed_at) = match outcome {
        ValidityResult::Valid(_) => (QueryResult::Valid, None),
        ValidityResult::Invalid(_, _, id) => (QueryResult::Invalid, id),
        ValidityResult::Canceled => (QueryResult::ResourceLimit, None),
        ValidityResult::TypeError(error) => return Err(io::Error::other(error.to_string())),
        ValidityResult::UnexpectedOutput(error) => return Err(io::Error::other(error)),
    };
    air.finish_query();
    let reply = reply.unwrap_or_else(|| SpeculationReply {
        unparsed: Some("the check did not reach check-sat".to_owned()),
        ..SpeculationReply::default()
    });
    Ok((result, elapsed_ms, reply, failed_at))
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

    // The quantifier the hypothesis names, and what its names mean, or why
    // nothing will be checked.
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
        match check_hypothesis(request, &quantifier, &[&unversioned.shown, &unversioned.plain]) {
            Ok(meant) => target = Some((request, quantifier, meant)),
            Err((status, reason)) => {
                outcome.status = Some(status.to_owned());
                outcome.notes = format!("Nothing was checked: {reason}.");
                outcome.reason = Some(reason);
                outcome.elapsed_ms = start.elapsed().as_millis();
                return Ok(Ok(outcome));
            }
        }
    }

    let (before_result, before_ms, before_reply, failed_at) =
        speculation_check(air, query, Hypothesis::Observe, loop_threshold, set_rlimit)?;
    let before = speculation_run(before_result, before_ms, &before_reply, symbols);
    let before_loops: HashSet<String> = before.loops.iter().map(|l| l.qid.clone()).collect();
    let before_loop_count = before.loops.len();
    outcome.before = Some(before);
    let Some((request, quantifier, meant)) = target else {
        let (listed, note) = candidates(air);
        outcome.candidates = listed;
        outcome.notes = format!(
            "No hypothesis: the query was checked as usual and answers {}, with {before_loop_count} matching loop(s). {note}",
            result_name(before_result)
        );
        outcome.elapsed_ms = start.elapsed().as_millis();
        return Ok(Ok(outcome));
    };

    // The terms are read at the goal the check failed at (the query's last
    // goal when it names none), where each mutable local holds the version
    // a pasted snippet will see.
    let goal = air::GoalScope::of(&query.query, failed_at.as_ref());
    let live = goal.live();
    let lowered = {
        let context: &Context = air;
        let declared = |name: &str| context.declared(name);
        // A trigger's terms are over the quantifier's variables; the other
        // hypotheses' terms stand outside it.
        let binders: &[(String, TreeNode)] = match request {
            HypothesisRequest::TriggerPattern { .. } => &quantifier.binders,
            _ => &[],
        };
        let lowering = Lowering::new(
            binders,
            Declarations::of(&decls, &query.query, live.clone(), &before_reply.variable_versions),
            &[&unversioned.shown, &unversioned.plain],
            &declared,
        );
        let occurrences = air::scaffold::occurrences(&query.query);
        let reader = symbols.map(|symbols| VerusReader {
            env: crate::scaffold::Env {
                names: symbols.source_names(),
                crate_name: symbols.crate_name(),
                locals: query_locals(&query.query),
                bound: binders
                    .iter()
                    .map(|(smt, sort)| (std::sync::Arc::new(smt.clone()), typ_of_sort(&flat(sort))))
                    .collect(),
                declared: &declared,
                occurrences: &occurrences,
            },
            goal: &goal,
            printer: air::printer::Printer::new(
                std::sync::Arc::new(VirMessageInterface {}),
                true,
                SmtSolver::Cvc5,
            ),
        });
        lower_hypothesis(request, &quantifier, &meant, &lowering, reader.as_ref())
    };
    let (lowered, subst) = match lowered {
        Ok((lowered, subst, readings)) => {
            outcome.readings = readings;
            (lowered, subst)
        }
        Err((status, reason)) => {
            outcome.status = Some(status.to_owned());
            outcome.notes = format!(
                "The query was checked as usual and answers {}, but not with the hypothesis: {reason}.",
                result_name(before_result)
            );
            outcome.reason = Some(reason);
            outcome.elapsed_ms = start.elapsed().as_millis();
            return Ok(Ok(outcome));
        }
    };

    // cvc5 eliminates a variable an equality in the formula's body fixes
    // (`x == y ==> ...`), and the formula it holds then no longer binds it.
    // An instantiation that names one is sent again without it: the
    // instance cvc5 makes is the rest's, with the equality's term for it.
    let mut lowered = lowered;
    let mut eliminated_smt: Vec<String> = Vec::new();
    let (after_result, after_ms, after_reply) = loop {
        let (result, ms, reply, _) =
            speculation_check(air, query, lowered.clone(), loop_threshold, set_rlimit)?;
        match (&mut lowered, unbound_variable(&reply)) {
            (Hypothesis::Instantiate { subst, .. }, Some(name))
                if subst.len() > 1 && subst.iter().any(|(v, _)| *v == name) =>
            {
                subst.retain(|(v, _)| *v != name);
                eliminated_smt.push(name);
            }
            _ => break (result, ms, reply),
        }
    };
    outcome.eliminated = eliminated_smt
        .iter()
        .map(|smt| vir::air_names::source_symbol(&unversioned.shown, smt).unwrap_or(smt.clone()))
        .collect();
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
        let (result, elapsed_ms, reply, _) =
            speculation_check(air, query, Hypothesis::Observe, loop_threshold, set_rlimit)?;
        closed = result != QueryResult::Valid;
        outcome.recheck = Some(speculation_run(result, elapsed_ms, &reply, symbols));
    }
    outcome.closed = closed;

    // Source for the check's terms, SSA versions included, to paste at the
    // goal the terms were read at.
    let names = QueryNames::new(symbols, &after_reply.variable_versions, &empty).at(&live);
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
            if closed && eliminated_smt.is_empty() {
                outcome.verus_snippet = instance_assert(&quantifier, &subst, &names);
            } else if closed {
                // The requested term for an eliminated variable may not be
                // the one its equality fixes, so the snippet is the instance
                // cvc5 made, when that pastes.
                outcome.verus_snippet = report.bodies.first().and_then(|body| {
                    let body = flat(&without_type_guards(&parse_term(body)?));
                    names
                        .pasteable(&[&body])
                        .then(|| format!("assert({});", names.render_plain(&body)))
                });
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
                    // after cvc5 eliminated a variable, the terms no longer
                    // line up with the quantifier's variables
                    if terms.len() != quantifier.binders.len() {
                        return None;
                    }
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
        ("no-quantifier", _) => notes.push(format!(
            "cvc5 holds no formula with this qid, though the query's scope asserts it: cvc5 registers alpha-equivalent formulas once, under the first one's qid, and drops a formula that rewrites away. The query answers {with}."
        )),
        (status, _) => notes.push(format!(
            "The hypothesis did not apply ({}{}); the query answers {with}.",
            status.replace('-', "_"),
            report.reason.as_deref().map(|r| format!(": {r}")).unwrap_or_default()
        )),
    }
    if !outcome.eliminated.is_empty() {
        notes.push(format!(
            "cvc5 eliminated {} from the formula (an equality in its body fixes it), so the instance was sent without it{}.",
            outcome.eliminated.join(", "),
            if closed { "; the snippet asserts the instance cvc5 made" } else { "" }
        ));
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
    /// The span `placement` refers to, when it refers to one: the goal's own;
    /// for a postcondition at an early `return`, the return's ("at this
    /// exit"); for one at the end of the body, the "end of the function body"
    /// label's (the body's final expression, or with none the function).
    insert_before: Option<String>,
    /// Where `assert(P);` goes in the source: `before_span`, right before
    /// `insert_before` (a postcondition at an early `return` included);
    /// `end_of_body`, at the end of the function body (a postcondition
    /// checked there); `end_of_loop_body` or `before_loop` (a loop
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
    let locals = query_locals(&query.query);
    let lowered = {
        let context: &Context = air;
        let declared = |name: &str| context.declared(name);
        let env = crate::scaffold::Env {
            names: symbols.source_names(),
            crate_name: symbols.crate_name(),
            locals,
            bound: Vec::new(),
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
        // user quantifiers and function definitions (and contracts) first,
        // the prelude last
        closing.sort_by_key(|q| match (&q.span, q.role, q.fun.as_deref()) {
            (Some(_), _, _) => 0,
            (
                None,
                Some("definition" | "definition_unfold" | "definition_base" | "contract"),
                _,
            ) => 1,
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
    // cannot be read, the dead end decides. A postcondition is checked at
    // each exit, which a label names (its primary span is the `ensures`
    // clause): at an early `return`, right before it; at the end of the body
    // (the body's final expression, or with none the function), there. A
    // loop invariant goes at the end of the loop body or before the loop,
    // which no span names, or at the break or continue its span is; anything
    // else, a step of a proof block included, at its own span.
    let claim_of_assert_by =
        given.ends_dead_end && primary.as_deref().and_then(followed_by_by).unwrap_or(true);
    let label =
        |text: &str| labels.iter().find(|l| l.message.contains(text)).map(|l| l.span.clone());
    let (insert_before, placement) = if claim_of_assert_by {
        (None, "end_of_proof_block")
    } else if description.contains("postcondition") {
        match label("at this exit") {
            Some(exit) => (Some(exit), "before_span"),
            None => (label("end of the function body").or_else(|| primary.clone()), "end_of_body"),
        }
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

/// Check `query` once with `rung`'s strategy, `alone` or alongside the
/// default schedule, at `rlimit`, and pop its scope. The options are set back
/// right after the check-sat, whatever it answered (see
/// `Context::set_quant_strategy`).
fn ladder_rung(
    air: &mut Context,
    query: &RetainedQuery,
    rung: Rung,
    alone: bool,
    rlimit: f32,
    set_rlimit: &impl Fn(&mut Context, f32),
) -> io::Result<RungReport> {
    set_rlimit(air, rlimit);
    let resource_limit = match air.cvc5_query_budget() {
        0 => None,
        budget => Some(u64::from(budget)),
    };
    air.set_quant_strategy(Some(rung.name()), alone);
    let start = Instant::now();
    let outcome = air.check_valid(
        &VirMessageInterface {},
        &QueryDiagnostics::default(),
        &query.query,
        QueryContext::default(),
    );
    let elapsed_ms = start.elapsed().as_millis();
    let info = air.take_strategy_rung();
    let unknown = air.take_unknown_reason();
    drop(air.take_provenance());
    drop(air.take_matching_loops());
    drop(air.take_difficulty());
    drop(air.take_inst_pressure());
    let (verdict, assert_id) = match outcome {
        ValidityResult::Valid(_) => ("valid", None),
        // An incomplete answer comes back as invalid with a reason; a
        // counterexample has none.
        ValidityResult::Invalid(_, _, id) => {
            (if unknown.is_some() { "unknown" } else { "invalid" }, id.map(|id| (*id).clone()))
        }
        ValidityResult::Canceled => ("resource_limit", None),
        ValidityResult::TypeError(error) => return Err(io::Error::other(error.to_string())),
        ValidityResult::UnexpectedOutput(error) => return Err(io::Error::other(error)),
    };
    air.finish_query();
    let counts = info.as_ref().map(|info| &info.instantiations);
    let count = |own: bool| {
        counts.map(|counts| {
            counts.iter().filter(|(name, _)| (name == rung.name()) == own).map(|(_, n)| n).sum()
        })
    };
    Ok(RungReport {
        rung,
        verdict,
        rlimit: Some(rlimit),
        resource_limit,
        resource_units: info.as_ref().map(|info| info.resource_units),
        instantiations: count(true),
        other_instantiations: count(false),
        rounds: info.as_ref().map(|info| info.rounds),
        reason_unknown: unknown.as_ref().map(|reason| reason.reason.clone()),
        incomplete_id: unknown.and_then(|reason| reason.incomplete_id),
        assert_id,
        elapsed_ms,
    })
}

/// Whether `rlimit`, in `#[verifier::rlimit]` units, is too small for a
/// single cvc5 resource unit: `set_rlimit` converts such a budget to 0, which
/// cvc5 takes as no limit at all. Leaves the solver at `restore`.
fn below_one_resource_unit(
    air: &mut Context,
    rlimit: f32,
    restore: f32,
    set_rlimit: &impl Fn(&mut Context, f32),
) -> bool {
    set_rlimit(air, rlimit);
    let below = air.cvc5_query_budget() == 0;
    set_rlimit(air, restore);
    below
}

/// Refuse a pin request that the query's checks could not follow, for a
/// query of `bucket` whose address the caller has checked. A check tries a
/// pinned rung by setting `:quant-strategy` without asking first, so a pin on
/// a cvc5 without that option would fail that check and end the session; a
/// rung the solver has no module for would run nothing, at every check; and
/// a budget below one cvc5 resource unit would run the attempt with no limit
/// at all. A ladder pins only a rung it ran, so it has made these checks
/// already.
/// `Ok(Err(_))` is a refusal to report; `Err` ends the session.
fn check_pin(
    bucket: &RetainedBucket,
    id: QueryId,
    rung: Rung,
    rlimit: f32,
    set_rlimit: &impl Fn(&mut Context, f32),
) -> io::Result<Result<(), &'static str>> {
    let mut state =
        bucket.state.lock().map_err(|_| io::Error::other("resident bucket poisoned"))?;
    let (solver, local) = bucket.addresses[id.0];
    let SolverState { air, journal } = &mut state[solver];
    if !matches!(air.get_solver(), SmtSolver::Cvc5) {
        return Ok(Err("pin requests need cvc5"));
    }
    let query_rlimit = journal.queries[local].rlimit;
    if below_one_resource_unit(air, rlimit, query_rlimit, set_rlimit) {
        return Ok(Err("the pin's budget is below one cvc5 resource unit"));
    }
    // The first probe of a solver that has not checked anything yet, as in a
    // retain-only session, starts it and sends the context it was given, so
    // the modules it has are known by the time it answers.
    let Some(probe) = air.probe_strategy_rung() else {
        return Ok(Err(
            "this cvc5 cannot run one instantiation strategy alone; it needs :quant-strategy",
        ));
    };
    if !probe.available.iter().any(|name| name == rung.name()) {
        return Ok(Err("the solver has no module for this rung"));
    }
    Ok(Ok(()))
}

/// Serve a ladder request for one query of `bucket`, whose address the
/// caller has checked. Each rung checks the query with its strategy alone or,
/// with `alongside`, together with the default schedule, at its own budget,
/// in the order given, until one proves the query or, with `run_all`,
/// through every rung. Each check runs in the query's own scope and resets
/// the strategy after itself, so the session's later checks are unchanged.
/// `Ok(Err(_))` is a refusal to report; `Err` ends the session.
fn serve_ladder(
    bucket: &RetainedBucket,
    id: QueryId,
    rungs: &[Rung],
    budgets: &HashMap<Rung, f32>,
    run_all: bool,
    alongside: bool,
    set_rlimit: &impl Fn(&mut Context, f32),
) -> io::Result<Result<LadderReport, &'static str>> {
    let mut state =
        bucket.state.lock().map_err(|_| io::Error::other("resident bucket poisoned"))?;
    let (solver, local) = bucket.addresses[id.0];
    let SolverState { air, journal } = &mut state[solver];
    if !matches!(air.get_solver(), SmtSolver::Cvc5) {
        return Ok(Err("ladder requests need cvc5"));
    }
    let prefix = journal.queries[local].prefix;
    let query_rlimit = journal.queries[local].rlimit;
    // Refused before any rung runs.
    if budgets
        .values()
        .any(|&rlimit| below_one_resource_unit(air, rlimit, query_rlimit, set_rlimit))
    {
        return Ok(Err("a rung's budget is below one cvc5 resource unit"));
    }
    let restore_start = Instant::now();
    journal.restore_prefix(air, prefix)?;
    let restore_ms = restore_start.elapsed().as_millis();
    // Asked before any option is set: a cvc5 without `:quant-strategy`
    // would answer the set-option with an error the check cannot survive.
    let Some(probe) = air.probe_strategy_rung() else {
        return Ok(Err(
            "this cvc5 cannot run one instantiation strategy alone; it needs :quant-strategy",
        ));
    };
    let query = &journal.queries[local];
    // A rung without a budget gets the query's own, or, for a query without
    // one, `DEFAULT_RUNG_RLIMIT`: every rung runs bounded.
    let default_budget = if query.rlimit.is_finite() { query.rlimit } else { DEFAULT_RUNG_RLIMIT };
    let start = Instant::now();
    let mut solved_by = None;
    let mut reports = Vec::new();
    for &rung in rungs {
        if solved_by.is_some() && !run_all {
            reports.push(RungReport::skipped(rung, "not_run"));
        } else if !probe.available.iter().any(|name| name == rung.name()) {
            reports.push(RungReport::skipped(rung, "unavailable"));
        } else {
            let rlimit = budgets.get(&rung).copied().unwrap_or(default_budget);
            let report = ladder_rung(air, query, rung, !alongside, rlimit, set_rlimit)?;
            if report.verdict == "valid" && solved_by.is_none() {
                solved_by = Some(rung);
            }
            reports.push(report);
        }
    }
    set_rlimit(air, query.rlimit);
    Ok(Ok(LadderReport {
        alongside,
        solved_by,
        rungs: reports,
        available: probe.available,
        pinned: None,
        elapsed_ms: start.elapsed().as_millis(),
        restore_ms,
    }))
}

impl QueryJournal {
    pub(crate) fn new() -> Self {
        Self {
            prelude: None,
            base: Vec::new(),
            contexts: Vec::new(),
            queries: Vec::new(),
            applied: 0,
            recorded_in_scope: false,
        }
    }

    /// Keep the prelude the solver started from, for fingerprints only.
    pub(crate) fn record_prelude(&mut self, prelude: Commands) {
        self.prelude = Some(prelude);
    }

    /// Keep the context the solver already holds below the journal's first
    /// scope, for lookups only.
    pub(crate) fn record_base(&mut self, batches: impl Iterator<Item = Commands>) {
        self.base.extend(batches);
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

    /// Every retained query's fingerprint, in journal order: the running
    /// hash of the prelude, the base context and the scopes below the query's
    /// prefix,
    /// and the hash of the query itself and its rlimit.
    fn fingerprints(&self) -> Vec<Fingerprint> {
        let printer = air::printer::Printer::new(
            std::sync::Arc::new(VirMessageInterface {}),
            false,
            SmtSolver::Cvc5,
        );
        let mut hash = Fnv::new();
        for batch in self.prelude.iter().chain(&self.base) {
            hash.commands(&printer, batch);
        }
        let mut prefixes = vec![hash.0];
        for scope in &self.contexts {
            for batch in scope {
                hash.commands(&printer, batch);
            }
            prefixes.push(hash.0);
        }
        self.queries
            .iter()
            .map(|query| {
                let mut body = Fnv::new();
                body.node(&printer.query_to_node(&query.query));
                // The budget a query checks at is part of what it is: raising
                // or lowering it can change its verdict.
                body.write(&query.rlimit.to_bits().to_le_bytes());
                Fingerprint { prefix: prefixes[query.prefix], body: body.0 }
            })
            .collect()
    }

    /// The declarations of the scopes below `prefix`, in the order they were
    /// asserted.
    fn prefix_decls(&self, prefix: usize) -> Vec<air::ast::Decl> {
        self.contexts[..prefix]
            .iter()
            .flatten()
            .flat_map(|batch| batch.iter())
            .filter_map(|command| match &**command {
                CommandX::Global(decl) => Some(decl.clone()),
                _ => None,
            })
            .collect()
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
        Self {
            buckets,
            info,
            graphs: KeptGraphs::new(MAX_KEPT_INSTANTIATIONS),
            pins: HashMap::new(),
        }
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
                strategy_ladder: self.info.strategy_ladder,
                retain_only: self.info.retain_only,
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
                | Request::Ablate { session: requested, .. }
                | Request::Egraph { session: requested, .. }
                | Request::Speculate { session: requested, .. }
                | Request::Scaffold { session: requested, .. }
                | Request::Close { session: requested }
                | Request::InstGraph { session: requested, .. }
                | Request::Twin { session: requested, .. }
                | Request::Ladder { session: requested, .. }
                | Request::Pin { session: requested, .. }
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
                Request::Pin { bucket: bucket_id, query: id, rung, alongside, rlimit, .. } => {
                    let Some(bucket) = self.buckets.get(bucket_id.0) else {
                        send(&mut output, &Response::Error { message: "unknown bucket" })?;
                        continue;
                    };
                    if bucket.queries.get(id.0).is_none() {
                        send(&mut output, &Response::Error { message: "unknown query" })?;
                        continue;
                    }
                    // Bounded as a ladder bounds a rung's budget, so a check
                    // that tries the pin first is bounded even for a query
                    // without an rlimit.
                    if !(rlimit > 0.0 && rlimit <= MAX_RUNG_RLIMIT) {
                        send(
                            &mut output,
                            &Response::Error { message: "rlimit must be above 0 and at most 1000" },
                        )?;
                        continue;
                    }
                    match check_pin(bucket, id, rung, rlimit, &set_rlimit) {
                        Ok(Ok(())) => {}
                        Ok(Err(message)) => {
                            send(&mut output, &Response::Error { message })?;
                            continue;
                        }
                        Err(error) => return fatal(&mut output, error),
                    }
                    let pin = Pin { rung, alongside, rlimit };
                    self.pins.insert((bucket_id.0, id.0), pin);
                    send(
                        &mut output,
                        &Response::Pinned { session, bucket: bucket_id, query: id, pin },
                    )?;
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
                Request::Ablate {
                    bucket: bucket_id,
                    query: id,
                    mode,
                    budget_checks,
                    hypotheses,
                    exclude,
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
                    let budget = budget_checks.unwrap_or(DEFAULT_ABLATE_CHECKS);
                    if budget == 0 || budget > MAX_BISECT_CHECKS {
                        send(
                            &mut output,
                            &Response::Error { message: "budget_checks must be between 1 and 256" },
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
                    // Prefix axioms are asserted below the query's scope, so
                    // the ablation asserts them again, switchable, above the
                    // prelude. The next check restores the prefix as usual.
                    let restore_start = Instant::now();
                    if let Err(error) = journal.restore_prefix(air, 0) {
                        return fatal(&mut output, error);
                    }
                    let restore_ms = restore_start.elapsed().as_millis();
                    let query = &journal.queries[local];
                    let prefix = journal.prefix_decls(query.prefix);
                    set_rlimit(air, query.rlimit);
                    let request = AblateRequest {
                        mode,
                        budget,
                        hypotheses: hypotheses.unwrap_or(true),
                        exclude: exclude.unwrap_or_default(),
                    };
                    let start = Instant::now();
                    let report = match ablate(air, &prefix, query, bucket.symbols.as_ref(), request)
                    {
                        Ok(mut report) => {
                            report.elapsed_ms = start.elapsed().as_millis();
                            report.restore_ms = restore_ms;
                            report
                        }
                        Err(error) if error.kind() == io::ErrorKind::InvalidInput => {
                            send(&mut output, &Response::Error { message: &error.to_string() })?;
                            continue;
                        }
                        Err(error) => return fatal(&mut output, error),
                    };
                    send(
                        &mut output,
                        &Response::Ablated {
                            session,
                            bucket: bucket_id,
                            query: id,
                            report: Box::new(report),
                        },
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
                Request::Twin {
                    bucket: bucket_id, query: id, edit, limit, recheck_base, ..
                } => {
                    let Some(bucket) = self.buckets.get(bucket_id.0) else {
                        send(&mut output, &Response::Error { message: "unknown bucket" })?;
                        continue;
                    };
                    if bucket.queries.get(id.0).is_none() {
                        send(&mut output, &Response::Error { message: "unknown query" })?;
                        continue;
                    }
                    let limit = limit.unwrap_or(twin::DEFAULT_TWIN_LIMIT);
                    if limit == 0 || limit > twin::MAX_TWIN_LIMIT {
                        send(
                            &mut output,
                            &Response::Error { message: "limit must be between 1 and 200" },
                        )?;
                        continue;
                    }
                    // Reported, not followed: a twin predicts ordinary
                    // verification, which has no pin.
                    let pin = self.pins.get(&(bucket_id.0, id.0)).copied();
                    let request = twin::TwinRequest { edit, limit, recheck_base, pin };
                    match twin::serve(bucket, id, request, &set_rlimit) {
                        Ok(Ok(report)) => send(
                            &mut output,
                            &Response::Twin {
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
                Request::Ladder {
                    bucket: bucket_id,
                    query: id,
                    rungs,
                    budgets,
                    run_all,
                    alongside,
                    pin,
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
                    let rungs = rungs.unwrap_or_else(|| {
                        if alongside { Rung::ALONGSIDE.to_vec() } else { Rung::LADDER.to_vec() }
                    });
                    if rungs.iter().enumerate().any(|(i, rung)| rungs[..i].contains(rung)) {
                        send(
                            &mut output,
                            &Response::Error { message: "each rung may be named once" },
                        )?;
                        continue;
                    }
                    if budgets.values().any(|&rlimit| !(rlimit > 0.0 && rlimit <= MAX_RUNG_RLIMIT))
                    {
                        send(
                            &mut output,
                            &Response::Error {
                                message: "a rung's budget must be above 0 and at most 1000",
                            },
                        )?;
                        continue;
                    }
                    match serve_ladder(
                        bucket,
                        id,
                        &rungs,
                        &budgets,
                        run_all,
                        alongside,
                        &set_rlimit,
                    ) {
                        Ok(Ok(mut report)) => {
                            let key = (bucket_id.0, id.0);
                            if pin.unwrap_or(true) {
                                match report.solved_by {
                                    Some(rung) => {
                                        // The budget it proved the query at.
                                        let rlimit = report
                                            .rungs
                                            .iter()
                                            .find(|report| report.rung == rung)
                                            .and_then(|report| report.rlimit)
                                            .expect("the rung that proved the query ran");
                                        self.pins.insert(key, Pin { rung, alongside, rlimit });
                                    }
                                    None => {
                                        self.pins.remove(&key);
                                    }
                                }
                            }
                            report.pinned = self.pins.get(&key).copied();
                            send(
                                &mut output,
                                &Response::Laddered {
                                    session,
                                    bucket: bucket_id,
                                    query: id,
                                    report,
                                },
                            )?
                        }
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
                    // Then the pinned rung, when a ladder or pin request set
                    // one: its strategy, alone or alongside as pinned, at the
                    // budget it was pinned at or the query's own, whichever
                    // is smaller, so it is bounded even for a
                    // query without an rlimit. It changes which instances
                    // are tried, never what is asserted, so a valid answer
                    // is sound, and that answer's diagnostics (provenance,
                    // difficulty) describe the check that decided, so the
                    // reply keeps them, as it keeps its graph. Any other
                    // answer is discarded, with its diagnostics, before the
                    // ordinary check, which runs the full schedule.
                    let mut pinned = None;
                    if let Some(&pin) =
                        self.pins.get(&(bucket_id.0, id.0)).filter(|_| certified.is_none())
                    {
                        let attempt_start = Instant::now();
                        let rlimit = pin.rlimit.min(query.rlimit);
                        set_rlimit(air, rlimit);
                        air.set_quant_strategy(Some(pin.rung.name()), !pin.alongside);
                        let attempt = air.check_valid(
                            &VirMessageInterface {},
                            &QueryDiagnostics::default(),
                            &query.query,
                            QueryContext::default(),
                        );
                        set_rlimit(air, query.rlimit);
                        let resource_units =
                            air.take_strategy_rung().map(|info| info.resource_units);
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
                            _ => {
                                drop(air.take_provenance());
                                drop(air.take_unknown_reason());
                                drop(air.take_matching_loops());
                                drop(air.take_difficulty());
                                drop(air.take_inst_pressure());
                                air.finish_query();
                            }
                        }
                        pinned = Some(PinnedAttempt {
                            rung: pin.rung,
                            alongside: pin.alongside,
                            rlimit,
                            closed: certified.is_some(),
                            elapsed_ms: attempt_start.elapsed().as_millis(),
                            resource_units,
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
                            summary.check = Some(if attempted.as_ref().is_some_and(|a| a.closed) {
                                "certificate"
                            } else if pinned.as_ref().is_some_and(|a| a.closed) {
                                "pinned"
                            } else {
                                "search"
                            });
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
                            pinned,
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
            live: None,
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
            live: None,
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

    /// Pasted where `z` holds its second version, an assert naming the first
    /// would read as the second.
    #[test]
    fn pasted_asserts_name_variables_at_their_version_where_pasted() {
        let (plain, shown, versions) = versioned_names();
        let live = HashMap::from([("z".to_string(), "z@1".to_string())]);
        let names = QueryNames {
            symbols: None,
            shown: Cow::Borrowed(&shown),
            plain: Cow::Borrowed(&plain),
            versions: &versions,
            live: None,
        }
        .at(&live);
        assert_eq!(
            names.verus_assert(&equality("z@1", "(+ x 1)", "entailed", &[])).as_deref(),
            Some("assert(z == (x + 1));")
        );
        assert_eq!(names.verus_assert(&equality("z@0", "(+ x 1)", "entailed", &[])), None);
    }

    #[test]
    fn differently_spelled_duplicates_merge_whichever_comes_first() {
        let (plain, shown, versions) = versioned_names();
        let names = QueryNames {
            symbols: None,
            shown: Cow::Borrowed(&shown),
            plain: Cow::Borrowed(&plain),
            versions: &versions,
            live: None,
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
        let nothing = |_: &str| None;
        let lowering = Lowering::new(&quantifier.binders, declared, &[&names], &nothing);
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

    /// cvc5's refusal of an instance for a variable its formula no longer
    /// binds names the variable to send the instance again without; no
    /// other refusal does.
    #[test]
    fn an_eliminated_variable_is_read_from_the_refusal() {
        let reply = |kind: &str, status: &str, reason: &str| SpeculationReply {
            hypotheses: vec![
                air::speculate::HypothesisReport { kind: "observe".into(), ..Default::default() },
                air::speculate::HypothesisReport {
                    kind: kind.into(),
                    status: status.into(),
                    reason: Some(reason.into()),
                    ..Default::default()
                },
            ],
            ..Default::default()
        };
        let unbound = format!("{UNBOUND_VARIABLE}y$");
        assert_eq!(
            unbound_variable(&reply("instantiate", "mismatch", &unbound)).as_deref(),
            Some("y$")
        );
        assert_eq!(
            unbound_variable(&reply("instantiate", "mismatch", "no term for the variable x$")),
            None
        );
        assert_eq!(unbound_variable(&reply("instantiate", "rejected", &unbound)), None);
        assert_eq!(unbound_variable(&reply("trigger", "mismatch", &unbound)), None);
    }

    /// Terms that stand outside the quantifier never name its variables; a
    /// mutable local reads as its symbol at the goal; the prelude's
    /// functions come from the AIR context; and SMT spelling is told apart
    /// from Verus.
    #[test]
    fn lowering_reads_ground_terms_at_the_goal() {
        let int = || std::sync::Arc::new(air::ast::TypX::Int);
        let quantifier_binders = vec![("i$".to_owned(), parse_term("Poly").unwrap())];
        let mut declared = Declarations {
            live: HashMap::from([("y@".to_owned(), "y@1".to_owned())]),
            ..Declarations::default()
        };
        for (constant, sort) in [("i!", "Int"), ("a!", "Int"), ("y@", "Int"), ("y@1", "Int")] {
            declared.constants.insert(constant.to_owned(), sort.to_owned());
        }
        let mut names = SourceNames::new();
        for (symbol, name) in [("i!", "i"), ("i$", "i"), ("a!", "a"), ("y@", "y")] {
            names.insert(symbol.to_owned(), vir::air_names::SourceName::Symbol(name.to_owned()));
        }
        let context = |name: &str| match name {
            "Add" => {
                Some(air::context::Declared::Fun(std::sync::Arc::new(vec![int(), int()]), int()))
            }
            "I" => Some(air::context::Declared::Fun(
                std::sync::Arc::new(vec![int()]),
                typ_of_sort(POLY),
            )),
            _ => None,
        };
        // an instantiation's terms: `i` is the parameter, not the variable
        let ground = Lowering::new(&[], declared, &[&names], &context);
        let lower = |text: &str| flat(&ground.term_as(text, Some(POLY)).unwrap());
        assert_eq!(lower("i"), "(I i!)");
        assert_eq!(lower("y"), "(I y@1)");
        assert_eq!(lower("y@"), "(I y@1)");
        assert_eq!(lower("(Add a! 1)"), "(I (Add a! 1))");
        // SMT spelling or Verus
        for (text, verus) in [
            ("a + 1", true),
            ("(a + 1)", true),
            ("s.len() - 1", true),
            ("i", true),
            ("(Add a! 1)", false),
            ("i!", false),
            ("y@1", false),
            ("$", false),
            ("(= a! 1)", false),
        ] {
            assert_eq!(ground.reads_as_verus(text), verus, "{text}");
        }
        // a trigger's terms: `i` is the variable
        let mut declared = Declarations::default();
        declared.constants.insert("i!".to_owned(), "Int".to_owned());
        let over = Lowering::new(&quantifier_binders, declared, &[&names], &context);
        assert_eq!(flat(&over.term_as("i", None).unwrap()), "i$");
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
                strategy_ladder: false,
                retain_only: false,
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

    /// A retained query's fingerprint reads its AIR, not where it came from:
    /// spans on the query's context and on its assertions leave it alone,
    /// a declaration added below it or another prelude changes its prefix and
    /// nothing else, and
    /// an edit to the query or to its rlimit changes its body and nothing
    /// else.
    #[test]
    fn fingerprints_ignore_spans_and_tell_the_prefix_from_the_body() {
        use air::ast::{QueryX, StmtX};
        use vir::messages::ToAny;
        let span = |text: &str| vir::messages::Span {
            raw_span: Arc::new(()),
            id: 0,
            data: Vec::new(),
            as_string: text.to_owned(),
        };
        let fun = Arc::new(vir::ast::FunX {
            path: Arc::new(vir::ast::PathX {
                krate: vir::ast::CrateId::Internal,
                segments: Arc::new(vec![Arc::new("f".to_owned())]),
            }),
        });
        // A query over `x` whose one assertion, labelled at `at`, checks `text`.
        let query = |at: &str, text: &str| {
            let parsed = commands(&format!("(check-valid (declare-const x Int) (assert {text}))"));
            let CommandX::CheckValid(parsed) = &*parsed[0] else { panic!("a query") };
            let StmtX::Assert(_, _, _, expr) = &*parsed.assertion else { panic!("an assert") };
            let assertion = Arc::new(StmtX::Assert(
                None,
                vir::messages::error(&span(at), "assertion failed").to_any(),
                None,
                expr.clone(),
            ));
            Arc::new(QueryX { local: parsed.local.clone(), assertion })
        };
        // The journal of one compilation: a base, a scope of declarations,
        // then the query at `rlimit`, and after it one more declaration.
        let journal_on = |prelude: &str, at: &str, extra_below: &str, text: &str, rlimit: f32| {
            let mut air = Context::new(Arc::new(VirMessageInterface {}), SmtSolver::Cvc5);
            let mut journal = QueryJournal::new();
            journal.record_prelude(commands(prelude));
            let base = commands("(declare-fun g (Int) Bool)");
            for command in base.iter() {
                if let CommandX::Global(decl) = &**command {
                    air.global(decl).unwrap();
                }
            }
            journal.record_base(std::iter::once(base));
            apply(&mut journal, &mut air, &commands(&format!("(axiom (g 1)) {extra_below}")));
            journal
                .record_query(
                    vir::def::CommandsWithContextX::new(
                        fun.clone(),
                        span(at),
                        "body".to_owned(),
                        Arc::new(vec![Arc::new(CommandX::CheckValid(query(at, text)))]),
                        vir::def::ProverChoice::DefaultProver,
                        false,
                    ),
                    &QueryOp::Body(Style::Normal),
                    rlimit,
                )
                .unwrap();
            apply(&mut journal, &mut air, &commands("(axiom (g 2))"));
            journal.fingerprints()
        };
        let prelude = "(declare-const SZ Int)";
        let journal_at = |at: &str, extra_below: &str, text: &str, rlimit: f32| {
            journal_on(prelude, at, extra_below, text, rlimit)
        };
        let journal =
            |at: &str, extra_below: &str, text: &str| journal_at(at, extra_below, text, 1.0);
        let before = journal("a.rs:3:5", "", "(> x 0)");
        assert_eq!(before.len(), 1);
        // Moved to other lines: the same fingerprint.
        assert_eq!(journal("a.rs:9:5", "", "(> x 0)"), before);
        // A declaration added below the query: its prefix changed, its body did not.
        let below = journal("a.rs:3:5", "(axiom (g 3))", "(> x 0)");
        assert_ne!(below[0].prefix, before[0].prefix);
        assert_eq!(below[0].body, before[0].body);
        // Another prelude: its prefix changed, its body did not.
        let word =
            journal_on("(declare-const SZ Int) (axiom (= SZ 64))", "a.rs:3:5", "", "(> x 0)", 1.0);
        assert_ne!(word[0].prefix, before[0].prefix);
        assert_eq!(word[0].body, before[0].body);
        // The query itself edited: its body changed, its prefix did not.
        let edited = journal("a.rs:3:5", "", "(>= x 0)");
        assert_eq!(edited[0].prefix, before[0].prefix);
        assert_ne!(edited[0].body, before[0].body);
        // The same query at another rlimit: its body changed, its prefix did not.
        let budget = journal_at("a.rs:3:5", "", "(> x 0)", 5.0);
        assert_eq!(budget[0].prefix, before[0].prefix);
        assert_ne!(budget[0].body, before[0].body);
        // Triggers listed in another order: the same query, so the same body.
        let quantified = |patterns: &str| {
            journal(
                "a.rs:3:5",
                "",
                &format!(
                    "(forall ((y Int)) (! (=> (g y) (> x y)) {patterns} :qid q :skolemid skolem_q))"
                ),
            )
        };
        let one = quantified(":pattern ((g y)) :pattern ((> x y))");
        assert_eq!(one, quantified(":pattern ((> x y)) :pattern ((g y))"));
        // A trigger listed twice: the same query too.
        assert_eq!(one, quantified(":pattern ((g y)) :pattern ((> x y)) :pattern ((g y))"));
        assert_ne!(one[0].body, quantified(":pattern ((g y))")[0].body);
        // A user quantifier numbered otherwise by the bucket's counter: the
        // same query. One named for another function is not.
        let named = |qid: &str| {
            journal(
                "a.rs:3:5",
                "",
                &format!(
                    "(forall ((y Int)) (! (=> (g y) (> x y)) :pattern ((g y)) :qid {qid} :skolemid skolem_{qid}))"
                ),
            )
        };
        let numbered = named("user_crate__f_3");
        assert_eq!(numbered, named("user_crate__f_17"));
        assert_ne!(numbered[0].body, named("user_crate__g_3")[0].body);
    }
}
