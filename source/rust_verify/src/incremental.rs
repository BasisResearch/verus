//! An on-disk cache of per-query verdicts, so that a repeated `verus`
//! invocation over edited source re-solves only the queries the edit changed.
//!
//! Design. `VERUS_INCREMENTAL_CACHE=<dir>` enables it. The verifier asks the
//! solver one query per proof obligation (a function's body check, its
//! termination check, a recommends follow-up, ...), each over the declarations
//! asserted below it in its bucket. Before a query is sent, this module gives
//! it a fingerprint (`relevance::Fingerprint`): FNV-1a over the AIR of the
//! declarations the query can reach among those below it, and over the query
//! itself with its budget, printed without spans. A query that only moved,
//! or whose module gained a lemma it does not use, keeps its fingerprint; an
//! edit to its body, its contract, a callee's contract or a definition it
//! unfolds changes it. One record per query is kept under `<dir>/<verus
//! build>-<solver>/<key>.json`, keyed by the function, the kind of check and
//! its description (not by position: a function that moves keeps its key),
//! holding the fingerprint and what the solver answered, round by round as
//! `--multiple-errors` asked (a record of a query that never came back
//! invalid serves every value of it): valid, out of resources, or invalid
//! with the failed assertion named by its index among the query's labeled
//! assertions and the labeled axiom whose labels the error carried named by
//! the hash of its AIR (`air::context::FailedAssertion`).
//!
//! A hit replays those rounds through the verifier's ordinary reporting path:
//! the error is rebuilt from the current query's own labels, so its spans are
//! the current source's, and the counts, the "verification results" line and
//! the exit code are what a fresh run gives. A hit sends nothing to the
//! solver, and a spun-off query whose every check hits starts no solver at
//! all. A miss is solved and recorded. Nothing is cached under the modes that
//! read more from a solver run than its verdict (`--profile`, `--debugger`,
//! `--expand-errors` queries, `-V axiom-usage-info`), nor for a function's
//! profile rerun. Each run appends a line to `<dir>/runs.jsonl` saying how
//! many queries it looked up, how many it replayed and how many it solved.
//!
//! What a fingerprint does not cover is the solver's search itself: a
//! declaration the query cannot reach still costs resource units, so a
//! verdict decided at the edge of the budget can in principle differ between
//! a fresh run and the run that recorded it. The record is the earlier run's
//! answer; the fresh run's would be the same query at the same budget.

pub(crate) mod relevance;

pub(crate) use relevance::BatchOwner;

use crate::commands::{QueryOp, Style};
use crate::config::Args;
use crate::verifier::CommandBatch;
use air::ast::{AssertId, CommandX, Commands, DeclX, Expr, ExprX, Query};
use air::context::{FailedAssertion, SmtSolver, UsageInfo, ValidityResult};
use air::messages::ArcDynMessage;
use relevance::{Fingerprint, Fnv, Prefix};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use vir::def::CommandsWithContextX;
use vir::messages::VirMessageInterface;

pub(crate) const ENV_VAR: &str = "VERUS_INCREMENTAL_CACHE";

/// The cache of one run, shared by the threads verifying its buckets.
pub(crate) struct Cache {
    dir: PathBuf,
    solver: SmtSolver,
    looked_up: AtomicU64,
    replayed: AtomicU64,
}

/// What the solver answered for one query, round by round.
#[derive(Clone, Serialize, Deserialize)]
pub(crate) enum Round {
    Valid,
    Canceled,
    /// Invalid without a model or an error (a bit-vector query).
    InvalidBare,
    Invalid {
        assertion: usize,
        assert_id: Option<Vec<u64>>,
        axiom: Option<u64>,
    },
}

#[derive(Serialize, Deserialize)]
struct Record {
    prefix: u64,
    body: u64,
    /// The `--multiple-errors` the rounds were recorded under: how many
    /// rounds an invalid query gets, and which assertions the later ones
    /// check. A query that never came back invalid answered the same under
    /// any value, so its record serves every run.
    multiple_errors: u32,
    rounds: Vec<Round>,
}

impl Record {
    fn serves(&self, fingerprint: &Fingerprint, multiple_errors: u32) -> bool {
        self.prefix == fingerprint.prefix
            && self.body == fingerprint.body
            && (self.multiple_errors == multiple_errors
                || !self.rounds.iter().any(|round| matches!(round, Round::Invalid { .. })))
    }
}

/// A recorded round resolved against the current query: what the verifier
/// consumes in place of a solver result.
pub(crate) enum Replay {
    Valid,
    Canceled,
    InvalidBare,
    Invalid { error: ArcDynMessage, assert_id: Option<AssertId> },
}

impl Replay {
    pub(crate) fn into_result(self) -> ValidityResult {
        match self {
            Replay::Valid => ValidityResult::Valid(UsageInfo::None),
            Replay::Canceled => ValidityResult::Canceled,
            Replay::InvalidBare => ValidityResult::Invalid(None, None, None),
            Replay::Invalid { error, assert_id } => ValidityResult::Invalid(
                Some(air::model::Model::new(HashMap::new(), vec![])),
                Some(error),
                assert_id,
            ),
        }
    }
}

/// One query's cache entry, looked up before the query runs.
pub(crate) struct Plan {
    path: PathBuf,
    fingerprint: Fingerprint,
    multiple_errors: u32,
    /// The recorded rounds when the record's fingerprint is the query's and
    /// every round could be resolved; `None` is a miss.
    pub(crate) replay: Option<Vec<Replay>>,
}

impl Cache {
    /// The cache the environment names, unless the run's options read more
    /// from the solver than a verdict.
    pub(crate) fn from_env(args: &Args) -> Option<Arc<Cache>> {
        let dir = std::env::var_os(ENV_VAR)?;
        if dir.is_empty()
            || args.no_verify
            || args.profile
            || args.profile_all
            || args.capture_profiles
            || args.debugger
            || args.axiom_usage_info
        {
            return None;
        }
        let build = crate::util::verus_build_info();
        let solver = match args.solver {
            SmtSolver::Z3 => "z3",
            SmtSolver::Cvc5 => "cvc5",
        };
        let dir = PathBuf::from(dir).join(format!(
            "{}-{}",
            build.sha.chars().take(12).collect::<String>(),
            solver
        ));
        if let Err(err) = std::fs::create_dir_all(&dir) {
            eprintln!("warning: {ENV_VAR}: cannot create {}: {err}", dir.display());
            return None;
        }
        Some(Arc::new(Cache {
            dir,
            solver: args.solver,
            looked_up: AtomicU64::new(0),
            replayed: AtomicU64::new(0),
        }))
    }

    /// Append this run's counts to `<dir>/runs.jsonl` (the parent of the
    /// build's directory): what was looked up, replayed and solved.
    pub(crate) fn finish(&self, args: &Args) {
        let looked_up = self.looked_up.load(Ordering::Relaxed);
        let replayed = self.replayed.load(Ordering::Relaxed);
        let line = serde_json::json!({
            "time": std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_secs_f64())
                .unwrap_or(0.0),
            "verify_module": args.verify_module,
            "verify_function": args.verify_function,
            "rlimit": args.rlimit,
            "queries": looked_up,
            "replayed": replayed,
            "solved": looked_up - replayed,
        });
        let path = self.dir.parent().unwrap_or(&self.dir).join("runs.jsonl");
        let appended = std::fs::OpenOptions::new().append(true).create(true).open(&path).and_then(
            |mut file| {
                use std::io::Write;
                writeln!(file, "{line}")
            },
        );
        if let Err(err) = appended {
            eprintln!("warning: {ENV_VAR}: cannot write {}: {err}", path.display());
        }
    }

    fn read(&self, path: &PathBuf) -> Option<Record> {
        let text = std::fs::read(path).ok()?;
        serde_json::from_slice(&text).ok()
    }

    fn write(&self, path: &PathBuf, record: &Record) {
        let text = serde_json::to_vec(record).expect("serialize cache record");
        let tmp = path.with_extension(format!(
            "tmp-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let written = std::fs::write(&tmp, text).and_then(|()| std::fs::rename(&tmp, path));
        if let Err(err) = written {
            let _ = std::fs::remove_file(&tmp);
            eprintln!("warning: {ENV_VAR}: cannot write {}: {err}", path.display());
        }
    }
}

/// The cache as one bucket's verification sees it: the declarations below
/// its queries, indexed as they are asserted, and the labeled axioms among
/// them a recorded failure can name.
pub(crate) struct BucketCache {
    cache: Arc<Cache>,
    prefix: Prefix,
    /// The labeled axioms of the indexed batches by the hash of their AIR,
    /// with their labels.
    axioms: HashMap<u64, Vec<ArcDynMessage>>,
    /// How many queries of each function, kind and description came before,
    /// so that two with the same three are told apart.
    repeats: HashMap<(String, &'static str, String), usize>,
}

/// What the diagnostic records call a kind of check.
pub(crate) fn kind_name(op: &QueryOp) -> &'static str {
    match op {
        QueryOp::SpecTermination => "termination",
        QueryOp::Body(Style::Normal) => "body",
        QueryOp::Body(Style::RecommendsFollowupFromError) => "recommends",
        QueryOp::Body(Style::RecommendsChecked) => "recommends_checked",
        QueryOp::Body(Style::Expanded) => "expanded",
        QueryOp::Body(Style::CheckApiSafety) => "api_safety",
    }
}

impl BucketCache {
    pub(crate) fn new(cache: Arc<Cache>, prelude: &Commands) -> Self {
        let solver = cache.solver;
        BucketCache {
            cache,
            prefix: Prefix::new(prelude, solver),
            axioms: HashMap::new(),
            repeats: HashMap::new(),
        }
    }

    /// Index the batches of `context` not indexed yet.
    pub(crate) fn index(&mut self, context: &[CommandBatch]) {
        for batch in &context[self.prefix.len()..] {
            for command in batch.commands.iter() {
                let CommandX::Global(decl) = &**command else { continue };
                let DeclX::Axiom(axiom) = &**decl else { continue };
                for labeled in air::labeled_axioms(&axiom.expr) {
                    let (hash, labels) = self.axiom(&labeled);
                    self.axioms.entry(hash).or_insert(labels);
                }
            }
            self.prefix.push(&batch.commands, batch.owner.clone());
        }
    }

    /// The hash a recorded failure names a labeled axiom by, and its labels.
    fn axiom(&self, labeled: &Expr) -> (u64, Vec<ArcDynMessage>) {
        let mut hash = Fnv::new();
        hash.node(&self.prefix.printer.expr_to_node(labeled));
        let labels = match &**labeled {
            ExprX::LabeledAxiom(labels, _, _) => labels.clone(),
            _ => Vec::new(),
        };
        (hash.0, labels)
    }

    /// Look up every check of `cmds`, a query of `function` of kind `kind`
    /// run at `rlimit` with `multiple_errors` rounds, over the context
    /// indexed so far. One plan per command; a command that is not a check
    /// has none.
    pub(crate) fn plan(
        &mut self,
        context: &[CommandBatch],
        cmds: &CommandsWithContextX,
        function: &str,
        kind: &'static str,
        rlimit: f32,
        multiple_errors: u32,
    ) -> Vec<Option<Plan>> {
        self.index(context);
        let with_prefix = cmds.prover_choice != vir::def::ProverChoice::BitVector;
        let salt = rlimit.to_bits().to_le_bytes();
        let mut plans = Vec::new();
        for command in cmds.commands.iter() {
            let CommandX::CheckValid(query) = &**command else {
                plans.push(None);
                continue;
            };
            let repeat = self
                .repeats
                .entry((function.to_owned(), kind, cmds.context.desc.clone()))
                .or_insert(0);
            let key = key(function, kind, &cmds.context.desc, *repeat);
            *repeat += 1;
            let fingerprint = self.prefix.fingerprint(query, &salt, with_prefix);
            let path = self.cache.dir.join(format!("{key}.json"));
            self.cache.looked_up.fetch_add(1, Ordering::Relaxed);
            let replay = self
                .cache
                .read(&path)
                .filter(|record| record.serves(&fingerprint, multiple_errors))
                .and_then(|record| self.resolve(query, &record.rounds));
            if replay.is_some() {
                self.cache.replayed.fetch_add(1, Ordering::Relaxed);
            }
            plans.push(Some(Plan { path, fingerprint, multiple_errors, replay }));
        }
        plans
    }

    /// The recorded rounds against the current query; `None` when a round
    /// names an assertion or an axiom the query no longer has (which a
    /// matching fingerprint should rule out).
    fn resolve(&self, query: &Query, rounds: &[Round]) -> Option<Vec<Replay>> {
        let message_interface = VirMessageInterface {};
        let (assertions, own) = air::query_labels(&message_interface, query);
        let mut own_axioms: Option<HashMap<u64, Vec<ArcDynMessage>>> = None;
        let mut replays = Vec::with_capacity(rounds.len());
        for round in rounds {
            replays.push(match round {
                Round::Valid => Replay::Valid,
                Round::Canceled => Replay::Canceled,
                Round::InvalidBare => Replay::InvalidBare,
                Round::Invalid { assertion, assert_id, axiom } => {
                    let error = assertions.get(*assertion)?;
                    let labels = match axiom {
                        None => Vec::new(),
                        Some(hash) => match self.axioms.get(hash) {
                            Some(labels) => labels.clone(),
                            None => {
                                // A labeled axiom of the query's own assertion.
                                let own = own_axioms.get_or_insert_with(|| {
                                    let mut by_hash = HashMap::new();
                                    for labeled in &own {
                                        let (hash, labels) = self.axiom(labeled);
                                        by_hash.entry(hash).or_insert(labels);
                                    }
                                    by_hash
                                });
                                own.get(hash)?.clone()
                            }
                        },
                    };
                    use air::messages::MessageInterface;
                    Replay::Invalid {
                        error: message_interface.append_labels(error, &labels),
                        assert_id: assert_id.as_ref().map(|id| Arc::new(id.clone())),
                    }
                }
            });
        }
        Some(replays)
    }

    /// The round the solver just answered, as the record keeps it.
    pub(crate) fn round(
        &self,
        result: &ValidityResult,
        failure: Option<&FailedAssertion>,
    ) -> Option<Round> {
        Some(match result {
            ValidityResult::Valid(_) => Round::Valid,
            ValidityResult::Canceled => Round::Canceled,
            ValidityResult::Invalid(None, _, _) | ValidityResult::Invalid(_, None, _) => {
                Round::InvalidBare
            }
            ValidityResult::Invalid(Some(_), Some(_), assert_id) => {
                let failure = failure?;
                Round::Invalid {
                    assertion: failure.assertion,
                    assert_id: assert_id.as_ref().map(|id| (**id).clone()),
                    axiom: failure.axiom.as_ref().map(|labeled| self.axiom(labeled).0),
                }
            }
            ValidityResult::TypeError(_) | ValidityResult::UnexpectedOutput(_) => return None,
        })
    }

    /// Record what the solver answered for a query that missed.
    pub(crate) fn store(&self, plan: &Plan, rounds: Vec<Round>) {
        let record = Record {
            prefix: plan.fingerprint.prefix,
            body: plan.fingerprint.body,
            multiple_errors: plan.multiple_errors,
            rounds,
        };
        self.cache.write(&plan.path, &record);
    }
}

/// The name a query's record goes by: FNV-1a over its function, kind and
/// description, and its position among the queries that share all three.
/// Spans are left out, so an edit elsewhere in the crate, or in the
/// function's own body, keeps the name.
fn key(function: &str, kind: &str, description: &str, repeat: usize) -> String {
    let repeat = repeat.to_string();
    let mut hash = Fnv::new();
    for part in [function, kind, description, repeat.as_str()] {
        hash.write(part.as_bytes());
        hash.write(&[0]);
    }
    format!("q{:016x}", hash.0)
}
