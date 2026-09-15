use crate::ast::{
    AssertId, AxiomInfoFilter, Command, CommandX, Decl, Ident, Query, Typ, TypeError, Typs,
};
use crate::closure::ClosureTerm;
use crate::emitter::Emitter;
use crate::instantiations::ImportInstantiations;
use crate::messages::{ArcDynMessage, Diagnostics};
use crate::model::Model;
use crate::node;
use crate::printer::{macro_push_node, str_to_node};

use crate::scope_map::ScopeMap;
use crate::smt_process::SmtProcess;
use crate::smt_verify::ReportLongRunning;
use crate::typecheck::Typing;
use sise::TreeNode as Node;
use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::Duration;

#[derive(Clone, Debug)]
pub(crate) struct AssertionInfo {
    pub(crate) assert_id: Option<crate::ast::AssertId>,
    pub(crate) error: ArcDynMessage,
    pub(crate) label: Ident,
    pub(crate) filter: AxiomInfoFilter,
    pub(crate) decl: Decl,
    pub(crate) disabled: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct AxiomInfo {
    pub(crate) labels: Vec<Arc<dyn Any + Send + Sync>>,
    pub(crate) label: Ident,
    pub(crate) filter: AxiomInfoFilter,
    pub(crate) decl: Decl,
}

#[derive(Debug)]
pub enum UsageInfo {
    None,
    UsedAxioms(Vec<Ident>),
}

/// What cvc5 reported about one `check-sat` in provenance mode: the tag
/// lists of `(get-assertion-sources :tags-only)` and the instantiation dump.
/// Tags are the symbols from the wire (`hyp_3`, `ax_...`, `query`, `?`);
/// the join back to source happens in Verus.
#[derive(Debug, Clone, Default)]
pub struct ProvenanceInfo {
    /// SSA symbol -> original AIR variable and assignment version, recorded by lowering.
    pub variable_versions: VariableVersions,
    /// One entry per distinct tag list with at least one real tag.
    pub sources: Vec<Vec<String>>,
    /// Instantiated quantifiers, by `:qid`, with each instantiation vector
    /// printed as one string.
    pub instantiations: Vec<(String, Vec<String>)>,
    /// Reply lines the parser did not recognise, kept rather than failed on.
    pub unparsed: Vec<String>,
}

pub type VariableVersions = HashMap<String, (String, u32)>;

/// Why a `check-sat` answered `unknown`, as the solver reported it. The join
/// of the culprit `:qid`s back to source happens in Verus.
#[derive(Debug, Clone, Default)]
pub struct UnknownReason {
    /// The `(get-info :reason-unknown)` answer, unquoted: `incomplete`,
    /// `resourceout`, `timeout`, ...
    pub reason: String,
    /// cvc5's own classification of an incomplete answer, the `IncompleteId`
    /// behind `(get-info :incomplete-id)`: `QUANTIFIERS`, `ARITH_NL`,
    /// `QUANTIFIERS_MAX_INST_ROUNDS`, ... `None` when the answer was not
    /// incomplete or the solver cannot say.
    pub incomplete_id: Option<String>,
    /// The `:qid`s of `(get-info :incomplete-culprits)`: the asserted
    /// quantifiers no strategy claimed to have fully processed. Candidates,
    /// not a verdict: when the solver gave up for a global reason (the
    /// instantiation round limit, a module's own check) there are none.
    pub culprit_qids: Vec<String>,
}

/// What cvc5's `(get-info :nl-frontier)` reported for one `check-sat`
/// (`-V nl-frontier`): the nonlinear terms whose value in the linear model
/// the nonlinear extension could not reconcile with their arguments' values,
/// and where each entered the problem. Terms and tags are the solver's
/// spelling; the join back to source happens in Verus.
#[derive(Debug, Clone, Default)]
pub struct NlFrontier {
    /// SSA symbol -> original AIR variable and assignment version, recorded by lowering.
    pub variable_versions: VariableVersions,
    /// `unsat`, `sat` or `unknown` as cvc5 answered; `none` before a check.
    pub result: String,
    /// The unknown explanation in lower case (`incomplete`, `resourceout`,
    /// ...), `none` unless `unknown`.
    pub reason: String,
    /// Whether cvc5's nonlinear extension was on.
    pub enabled: bool,
    /// Model-based refinement runs, runs with an assertion false in the
    /// candidate model, and runs that gave up (no lemma, model unverified).
    pub checks: u64,
    pub rounds: u64,
    pub punts: u64,
    /// How the most recent run ended: `none`, `sat`, `lemma` or `punt`.
    pub last: String,
    /// Most recent round's atoms first, then by rounds wrong.
    pub atoms: Vec<NlAtom>,
    /// Atoms left out of `atoms`.
    pub omitted: u64,
    /// Whether the search for hosts in instantiations stopped early.
    pub truncated: bool,
    /// The reply, when it did not parse.
    pub unparsed: Option<String>,
}

/// What cvc5 reported for `(get-info :matching-loops)` after a `check-sat`
/// answered unknown (`-V matching-loops`): the quantifiers whose
/// instantiations fed themselves, symbols and SMT terms not yet joined to
/// source. The fields mirror the reply (see cvc5's
/// `theory/quantifiers/matching_loops.h`).
#[derive(Debug, Clone, Default)]
pub struct MatchingLoopsInfo {
    /// SSA symbol -> original AIR variable and assignment version, recorded by lowering.
    pub variable_versions: VariableVersions,
    /// The last instantiation round of the check
    pub rounds: u64,
    /// Instantiations recorded, and those past cvc5's recording cap
    pub instantiations: u64,
    pub dropped: u64,
    /// Whether the instantiation round limit stopped the check
    pub max_inst_rounds: bool,
    pub loops: Vec<MatchingLoop>,
    /// Reply parts the parser did not recognise, kept rather than failed on.
    pub unparsed: Vec<String>,
}

/// One self-feeding quantifier, as cvc5 reported it. Terms are SMT text.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct MatchingLoop {
    pub qid: String,
    /// high (the round limit cut the loop off while it climbed), medium, low
    pub confidence: String,
    /// linear-depth, exponential-fanout, or bounded
    pub growth: String,
    /// whether the chain follows instantiations that matched a term the
    /// previous rung introduced, rather than the deepest one of each round
    pub edges_confirmed: bool,
    /// whether consecutive rungs generalise to one shape
    pub stable: bool,
    pub instantiations: u64,
    pub rounds: u64,
    pub first_round: u64,
    pub last_round: u64,
    pub chain: u64,
    pub self_fed: u64,
    pub depth_per_rung: f64,
    pub depth_per_round: f64,
    pub fanout_per_round: f64,
    /// growth per step of the quantifier's own rounds: a loop that fires
    /// every other round doubles per step while `fanout_per_round` reads 1.41
    pub fanout_per_step: f64,
    /// qids of the other quantifiers a step passed through
    pub via: Vec<String>,
    /// the trigger whose matches formed the rungs, one term per trigger term
    pub trigger: Vec<String>,
    /// what each rung wraps around the previous one's growing subterm,
    /// generalised over the chain, `_0` marking that subterm; one per class
    /// when the loop climbs several subterms (`(r _0)`, `(l _0)`), and empty
    /// when the rungs do not grow into each other
    pub context: Vec<String>,
    /// the generalisation of every rung, and of every rung after the first
    pub shape: Vec<String>,
    pub step: Vec<String>,
    /// the first rungs and the last, each the trigger instantiated
    pub ladder: Vec<Vec<String>>,
    pub ladder_length: u64,
    /// instantiations of the quantifier per round, the last rounds
    pub per_round: Vec<u64>,
}

/// What a query's first `check-sat` also asks cvc5 for: the equalities its
/// e-graph holds between the query's own terms (`get-egraph-equalities`).
#[derive(Debug, Clone, Copy)]
pub struct EgraphRequest {
    /// The most equalities cvc5 replies with.
    pub limit: u32,
    /// Whether to include equalities with a side some quantifier was
    /// instantiated with.
    pub include_used: bool,
}

/// One equality from `(get-egraph-equalities)`, its terms as cvc5 printed
/// them. The same solver can parse them back in the same query's scope.
#[derive(Debug, Clone)]
pub struct EgraphEquality {
    pub lhs: String,
    pub rhs: String,
    /// `entailed` (every literal of the explanation holds at decision level 0
    /// in the query's scope), `decision`, or `unknown`
    pub level: String,
    /// whether some quantifier was instantiated with either side
    pub used: bool,
    /// the `:qid`s of those quantifiers
    pub used_by: Vec<String>,
    /// how many of the two sides are subterms of the query, 0 to 2
    pub focus: u32,
    /// the literals the equality follows from, except those cvc5 left out
    pub because: Vec<String>,
    /// how many literals of the explanation cvc5 left out, as naming a
    /// skolem or printing larger than its size limit; when not 0, `because`
    /// alone does not imply the equality
    pub because_hidden: u64,
}

/// cvc5's reply to `(get-egraph-equalities)` after a query's first
/// `check-sat`, with what it counted.
#[derive(Debug, Clone, Default)]
pub struct EgraphReply {
    pub equalities: Vec<EgraphEquality>,
    /// classes listed
    pub classes: u64,
    /// equalities before the limit
    pub candidates: u64,
    /// focus terms sent, and how many of them the e-graph holds
    pub focus: u64,
    pub focus_found: u64,
    /// equalities left out because a quantifier was instantiated with a side
    pub used_omitted: u64,
    /// terms left out because they print larger than cvc5's size limit
    pub too_large: u64,
    /// The solver's refusal, as after `unsat`, where there is no e-graph to
    /// read, or a reply this parser did not recognise.
    pub error: Option<String>,
    /// SSA symbol -> original AIR variable and assignment version, recorded by lowering.
    pub variable_versions: VariableVersions,
}

/// What cvc5's `(get-info :difficulty-gradient)` reported for one
/// `check-sat` (`-V difficulty`): per tagged input assertion, the lemma work
/// cvc5 attributed to it and, after `unsat`, whether the unsat core holds it.
/// Tags are the symbols from the wire; the join back to source happens in
/// Verus.
///
/// cvc5 keeps difficulty until the query's scope is popped, and the rounds
/// of a multi-error query share that scope, so a later round's counts
/// include the work of the rounds before it.
#[derive(Debug, Clone, Default)]
pub struct DifficultyGradient {
    /// `unsat`, `sat` or `unknown` as cvc5 answered; `none` before a check.
    pub result: String,
    /// Whether cvc5 tracked difficulty (`--produce-difficulty`).
    pub difficulty: bool,
    /// Whether each row says if the unsat core holds it: after `unsat` only.
    pub core: bool,
    /// One per distinct tagged input assertion, largest difficulty first.
    pub rows: Vec<DifficultyRow>,
    /// Input assertions without a tag, summed. Every assertion Verus emits
    /// is tagged, the AIR prelude's included; what is left is the assertion
    /// each multi-error round adds to disable the errors already reported.
    pub untagged_asserted: u64,
    pub untagged_difficulty: u64,
    /// How many of them the unsat core holds, when `core`.
    pub untagged_in_core: Option<u64>,
    /// Difficulty cvc5 could not carry back to a current input assertion.
    pub unmatched_difficulty: u64,
    /// The reply, when it did not parse.
    pub unparsed: Option<String>,
}

/// What cvc5's `(get-info :inst-pressure)` reported for one `check-sat`
/// (`-V inst-pressure`): per quantifier, by `:qid`, how often it was
/// instantiated and how often an attempt was rejected as a duplicate. The
/// join back to source happens in Verus.
#[derive(Debug, Clone, Default)]
pub struct InstPressure {
    /// Instantiation rounds that sent lemmas.
    pub rounds: u64,
    /// Whether each row says how many of its instances the refutation used.
    /// Only after `unsat` with proofs on, so not in an ordinary run.
    pub refutation: bool,
    /// Most instantiated first.
    pub quantifiers: Vec<QuantPressure>,
    /// The reply, when it did not parse.
    pub unparsed: Option<String>,
}

/// What cvc5's `(get-info :strategy-rung)` reported for one `check-sat` run
/// under `:quant-strategy` (see `Context::set_quant_strategy`).
#[derive(Debug, Clone, Default)]
pub struct StrategyRung {
    /// The strategy the check ran: `all`, `ematch`, `conflict`, `pool`,
    /// `enum` or `mbqi`.
    pub strategy: String,
    /// Whether alone, rather than alongside the default schedule.
    pub alone: bool,
    /// The ladder strategies the solver has a module for.
    pub available: Vec<String>,
    /// Instantiation rounds that sent lemmas.
    pub rounds: u64,
    /// The resources the check spent, in the unit of
    /// `reproducible-resource-limit`.
    pub resource_units: u64,
    /// Instantiations added, per strategy (`other` for the rest).
    pub instantiations: Vec<(String, u64)>,
    /// The reply, when it did not parse.
    pub unparsed: Option<String>,
}

/// One nonlinear term of `(get-info :nl-frontier)`.
#[derive(Debug, Clone, Default)]
pub struct NlAtom {
    /// The term as the input spelled it, e.g. `(* x y)`.
    pub atom: String,
    /// product, power, division, iand, pow2 or transcendental
    pub kind: String,
    /// Whether it was wrong in the most recent refinement round.
    pub current: bool,
    /// In how many rounds it was wrong.
    pub rounds: u64,
    /// Its value in the linear model, and the value its arguments give it
    /// (they differ: that is why it is on the frontier). Each is a rational
    /// as cvc5 prints it (`-5`, `1/2`), or `none`.
    pub value: String,
    pub from_args: String,
    /// The bounds asserted on the atom itself.
    pub lower: Option<NlBound>,
    pub upper: Option<NlBound>,
    /// Its distinct arguments with their values and asserted bounds.
    pub args: Vec<NlTerm>,
    /// Where it entered the problem.
    pub hosts: Vec<NlHost>,
}

/// A term with its model value and asserted bounds.
#[derive(Debug, Clone, Default)]
pub struct NlTerm {
    pub term: String,
    pub value: String,
    pub lower: Option<NlBound>,
    pub upper: Option<NlBound>,
}

/// A constant bound read off an asserted literal.
#[derive(Debug, Clone, Default)]
pub struct NlBound {
    /// A rational as cvc5 prints it, e.g. `5`, `-5` or `1/2`.
    pub value: String,
    pub strict: bool,
    /// Whether the literal is implied by the assertions (fixed at SAT level
    /// 0), rather than holding only in the branch the solver explored.
    pub fixed: bool,
}

/// A term that applies one function to exactly an atom's factors: in a
/// tagged input assertion, or in the instantiations of one quantifier.
#[derive(Debug, Clone, Default)]
pub struct NlHost {
    /// `true` for an input assertion, `false` for an instantiation.
    pub input: bool,
    pub term: String,
    /// Input hosts: the tags of the assertions holding the term.
    pub tags: Vec<String>,
    /// Instantiation hosts: the quantifier's `:qid`, and how many vectors.
    pub qid: Option<String>,
    pub count: u64,
}

/// One tagged input assertion of `(get-info :difficulty-gradient)`.
#[derive(Debug, Clone, Default)]
pub struct DifficultyRow {
    /// Several when hash-consing merged identical assertions.
    pub tags: Vec<String>,
    /// How many lemmas used a literal that this assertion made relevant
    /// (cvc5's `lemma-literal-all` difficulty): a heuristic measure of the
    /// solver work that flowed through it.
    pub difficulty: u64,
    /// Whether the unsat core holds it; `None` unless the reply has a core.
    pub in_core: Option<bool>,
}

/// One quantifier's row of `(get-info :inst-pressure)`. Counts are the
/// solver's own, disaggregated: every attempt that reached the duplicate
/// checks is counted once, as added or as one kind of duplicate.
#[derive(Debug, Clone, Default)]
pub struct QuantPressure {
    /// The `:qid`, or a synthetic `quant_<n>` when `named` is false.
    pub qid: String,
    pub named: bool,
    pub instantiations: u64,
    /// Rejected: the same term vector was used before.
    pub duplicate_eq: u64,
    /// Rejected: the instance was already entailed.
    pub duplicate_ent: u64,
    /// Rejected: the same lemma was already sent.
    pub duplicate_lemma: u64,
    /// Instances made because they conflicted with, or propagated in, the
    /// current assignment (conflict-based instantiation).
    pub conflict: u64,
    pub propagate: u64,
    /// The rounds of the first and last instantiation; none without one.
    pub first_round: Option<u64>,
    pub last_round: Option<u64>,
    /// Instances the refutation used, when `InstPressure::refutation`.
    pub refutation: Option<u64>,
}

#[derive(Debug)]
pub enum ValidityResult {
    Valid(UsageInfo),
    Invalid(Option<Model>, Option<ArcDynMessage>, Option<AssertId>),
    Canceled,
    TypeError(TypeError),
    UnexpectedOutput(String),
}

#[derive(Clone, Debug)]
pub(crate) enum ContextState {
    NotStarted,
    ReadyForQuery,
    FoundResult,
    FoundInvalid(Vec<AssertionInfo>, Option<Model>),
    Canceled,
    NoMoreQueriesAllowed,
}

pub struct QueryContext<'a, 'b: 'a> {
    pub report_long_running: Option<&'a mut ReportLongRunning<'b>>,
}

impl<'a, 'b: 'a> Default for QueryContext<'a, 'b> {
    fn default() -> Self {
        QueryContext { report_long_running: None }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum SmtSolver {
    Z3,
    Cvc5,
}

impl SmtSolver {
    /// The solver's executable name, as used in messages.
    pub fn name(&self) -> &'static str {
        match self {
            SmtSolver::Z3 => "z3",
            SmtSolver::Cvc5 => "cvc5",
        }
    }
}

impl Default for SmtSolver {
    fn default() -> Self {
        SmtSolver::Z3
    }
}

/// The counters that name AIR's generated symbols (axiom labels, arrays,
/// lambdas, chooses and applies) and anonymous axiom tags, as they stood when
/// a name scope opened.
#[derive(Clone, Copy)]
struct NameCounters {
    axiom_infos: u64,
    array: u64,
    lambda: u64,
    choose: u64,
    apply: u64,
    anon_axiom: u64,
}

pub struct Context {
    pub(crate) message_interface: Arc<dyn crate::messages::MessageInterface>,
    smt_process: Option<SmtProcess>,
    pub(crate) axiom_infos: ScopeMap<Ident, Arc<AxiomInfo>>,
    pub(crate) axiom_infos_count: u64,
    pub(crate) array_map: ScopeMap<ClosureTerm, Ident>,
    pub(crate) array_count: u64,
    pub(crate) lambda_map: ScopeMap<ClosureTerm, Ident>,
    pub(crate) lambda_count: u64,
    pub(crate) choose_map: ScopeMap<ClosureTerm, Ident>,
    pub(crate) choose_count: u64,
    pub(crate) apply_map: ScopeMap<(Typs, Typ), Ident>,
    pub(crate) apply_count: u64,
    /// One entry per open name scope. Popping a scope restores its counters,
    /// so replaying a popped scope reproduces the names it generated: a
    /// resident session rebuilds query prefixes that way, and instantiation
    /// certificates refer to formulas by those names.
    name_counters: Vec<NameCounters>,
    pub(crate) typing: Typing,
    pub(crate) debug: bool,
    pub(crate) ignore_unexpected_smt: bool,
    pub(crate) rlimit: u32,
    pub(crate) air_initial_log: Emitter,
    pub(crate) air_middle_log: Emitter,
    pub(crate) air_final_log: Emitter,
    pub(crate) smt_log: Emitter,
    pub(crate) smt_transcript_log: Option<Box<dyn std::io::Write + Send>>,
    pub(crate) time_smt_init: Duration,
    pub(crate) time_smt_run: Duration,
    pub(crate) rlimit_count: Option<(u64, u64)>,
    pub(crate) state: ContextState,
    pub(crate) expected_solver_version: Option<String>,
    pub(crate) profile_logfile_name: Option<String>,
    pub(crate) single_check_query: bool,
    pub(crate) usage_info_enabled: bool,
    pub(crate) check_valid_used: bool,
    pub(crate) solver: SmtSolver,
    /// Put provenance ids on the wire: goal labels carry their AssertId.
    /// On by default under cvc5, which reads them back; z3 would only warn.
    pub(crate) emit_assert_ids: bool,
    /// Axioms that arrived without a tag and without a `:qid` to derive one
    /// from are tagged `ax_anon_<n>` with this counter.
    pub(crate) anon_axiom_count: u64,
    /// Provenance mode (`-V provenance`): cvc5 runs with preprocessing
    /// proofs, twice the per-query budget, and is asked for the sources of
    /// each query. Off by default; it perturbs the search, so plain runs stay
    /// the verdict of record.
    pub(crate) provenance: bool,
    /// The provenance of the last `check-sat`, until the caller takes it.
    pub(crate) last_provenance: Option<ProvenanceInfo>,
    /// Difficulty mode (`-V difficulty`): cvc5 tracks per-assertion
    /// difficulty and unsat cores, which needs preprocessing proofs and
    /// solving under assumptions, gets twice the per-query budget, and is
    /// asked for `(get-info :difficulty-gradient)` after every `check-sat`.
    /// It perturbs the search, so plain runs stay the verdict of record.
    pub(crate) difficulty: bool,
    /// The difficulty gradient of the last `check-sat`, until the caller
    /// takes it.
    pub(crate) last_difficulty: Option<DifficultyGradient>,
    /// Why the last `check-sat` answered `unknown`, until the caller takes it.
    pub(crate) last_unknown_reason: Option<UnknownReason>,
    /// Nonlinear frontier mode (`-V nl-frontier`): cvc5 is asked for
    /// `(get-info :nl-frontier)` after every `check-sat`. cvc5 records the
    /// frontier during every check anyway, so the search is the ordinary one.
    pub(crate) nl_frontier: bool,
    /// The nonlinear frontier of the last `check-sat`, until the caller takes it.
    pub(crate) last_nl_frontier: Option<NlFrontier>,
    /// Matching-loop mode (`-V matching-loops`): cvc5 records each
    /// instantiation's round, terms and parents, and is asked for the loops
    /// among them after every unknown. Recording spends no resource units,
    /// so the verdict is a plain run's unless `inst_max_rounds` is set.
    pub(crate) matching_loops: bool,
    /// cvc5's `--inst-max-rounds`, only under matching-loop mode. A loop is
    /// high confidence only when this limit stopped the check.
    pub(crate) inst_max_rounds: Option<u32>,
    /// The matching loops of the last unknown `check-sat`, until taken.
    pub(crate) last_matching_loops: Option<MatchingLoopsInfo>,
    /// Ask cvc5 for `(get-info :inst-pressure)` after every `check-sat`
    /// (`-V inst-pressure`). Read-only: the search is unchanged.
    pub(crate) inst_pressure: bool,
    /// The instantiation pressure of the last `check-sat`, until the caller
    /// takes it.
    pub(crate) last_inst_pressure: Option<InstPressure>,
    /// Whether this solver may save and restore instantiations across
    /// rechecks of a query (cvc5 only, fixed at launch).
    pub(crate) instantiation_replay: bool,
    /// Whether this solver records its instantiation graph (cvc5 only,
    /// fixed at launch).
    pub(crate) inst_graph: bool,
    /// Whether this solver was launched with every quantifier instantiation
    /// strategy available to `quant_strategy` (cvc5 only, fixed at launch).
    pub(crate) strategy_ladder: bool,
    /// The instantiation strategy the next `check-sat` runs, and whether
    /// alone rather than alongside the default schedule; reset right after
    /// it, whatever it answers (cvc5 only).
    pub(crate) quant_strategy: Option<(String, bool)>,
    /// What the last `check-sat` run under `quant_strategy` reported, until
    /// the caller takes it.
    pub(crate) last_strategy_rung: Option<StrategyRung>,
    /// The key under which the next query's scope restores saved
    /// instantiations, and whether they are the only ones allowed (cvc5
    /// only).
    pub(crate) restore_instantiations: Option<(String, bool)>,
    /// The keys this solver has saved instantiations under.
    pub(crate) saved_instantiations: HashSet<String>,
    /// A certificate to import before the next query's first `check-sat`,
    /// once its declarations are in scope (cvc5 only).
    pub(crate) import_instantiations: Option<ImportInstantiations>,
    variable_versions: VariableVersions,
    /// Ask each query's first `check-sat` for the equalities cvc5's e-graph
    /// holds between the query's terms (cvc5 only).
    pub(crate) egraph_request: Option<EgraphRequest>,
    /// The query's terms that focus the request, from lowering to the check.
    pub(crate) egraph_focus: Option<Vec<sise::TreeNode>>,
    /// The reply to the last request, until the caller takes it.
    pub(crate) last_egraph: Option<EgraphReply>,
    /// An equality to assert in the next query's scope just before its first
    /// `check-sat` (cvc5 only).
    pub(crate) inject_equality: Option<(sise::TreeNode, sise::TreeNode)>,
}

impl Context {
    pub fn new(
        message_interface: Arc<dyn crate::messages::MessageInterface>,
        solver: SmtSolver,
    ) -> Self {
        let mut context = Context {
            message_interface: message_interface.clone(),
            smt_process: None,
            axiom_infos: ScopeMap::new(),
            axiom_infos_count: 0,
            array_map: ScopeMap::new(),
            array_count: 0,
            lambda_map: ScopeMap::new(),
            lambda_count: 0,
            choose_map: ScopeMap::new(),
            choose_count: 0,
            apply_map: ScopeMap::new(),
            apply_count: 0,
            name_counters: Vec::new(),
            typing: Typing {
                message_interface: message_interface.clone(),
                decls: crate::scope_map::ScopeMap::new(),
                snapshots: HashSet::new(),
                break_labels_local: HashSet::new(),
                break_labels_in_scope: crate::scope_map::ScopeMap::new(),
                solver: solver.clone(),
            },
            debug: false,
            ignore_unexpected_smt: false,
            rlimit: 0,
            air_initial_log: Emitter::new(
                message_interface.clone(),
                false,
                false,
                None,
                solver.clone(),
            ),
            air_middle_log: Emitter::new(
                message_interface.clone(),
                false,
                false,
                None,
                solver.clone(),
            ),
            air_final_log: Emitter::new(
                message_interface.clone(),
                false,
                false,
                None,
                solver.clone(),
            ),
            smt_log: Emitter::new(message_interface.clone(), true, true, None, solver.clone()),
            smt_transcript_log: None,
            time_smt_init: Duration::new(0, 0),
            time_smt_run: Duration::new(0, 0),
            rlimit_count: match solver {
                SmtSolver::Z3 => Some((0, 0)),
                SmtSolver::Cvc5 => None,
            },
            state: ContextState::NotStarted,
            expected_solver_version: None,
            profile_logfile_name: None,
            single_check_query: false,
            usage_info_enabled: false,
            check_valid_used: false,
            emit_assert_ids: matches!(solver, SmtSolver::Cvc5),
            anon_axiom_count: 0,
            provenance: false,
            last_provenance: None,
            difficulty: false,
            last_difficulty: None,
            last_unknown_reason: None,
            nl_frontier: false,
            last_nl_frontier: None,
            matching_loops: false,
            inst_max_rounds: None,
            last_matching_loops: None,
            inst_pressure: false,
            last_inst_pressure: None,
            instantiation_replay: false,
            inst_graph: false,
            strategy_ladder: false,
            quant_strategy: None,
            last_strategy_rung: None,
            restore_instantiations: None,
            saved_instantiations: HashSet::new(),
            import_instantiations: None,
            variable_versions: HashMap::new(),
            egraph_request: None,
            egraph_focus: None,
            last_egraph: None,
            inject_equality: None,
            solver,
        };
        context.axiom_infos.push_scope(false);
        context.array_map.push_scope(false);
        context.lambda_map.push_scope(false);
        context.choose_map.push_scope(false);
        context.apply_map.push_scope(false);
        context.typing.decls.push_scope(false);
        context.typing.break_labels_in_scope.push_scope(false);
        context
    }

    pub fn get_smt_process(&mut self) -> &mut SmtProcess {
        // Only start the smt process if there are queries to run
        if self.smt_process.is_none() {
            let transcript_log = self.smt_transcript_log.take();
            self.smt_process = Some(SmtProcess::launch(
                &self.solver,
                transcript_log,
                self.provenance,
                self.difficulty,
                self.instantiation_replay,
                self.inst_graph,
                self.matching_loops,
                self.inst_max_rounds,
                self.strategy_ladder,
            ));
        }
        self.smt_process.as_mut().unwrap()
    }

    /// Send everything buffered since the last solver interaction and wait for
    /// the solver to acknowledge it, returning whatever it printed.
    ///
    /// `push`, `pop` and `global` only append to the pipe buffer; the solver
    /// does not see them until a query flushes it. A caller that needs to
    /// attribute the cost of those commands separately from the query that
    /// follows must flush them itself. Returns nothing before the solver has
    /// started, leaving the buffer intact: an unstarted context has no pending
    /// work worth launching one for.
    pub fn flush_commands(&mut self) -> Vec<String> {
        if self.smt_process.is_none() {
            return Vec::new();
        }
        let smt_data = self.smt_log.take_pipe_data();
        self.get_smt_process().send_commands(smt_data)
    }

    pub fn set_air_initial_log(&mut self, writer: Box<dyn std::io::Write + Send>) {
        self.air_initial_log.set_log(Some(writer));
    }

    pub fn set_air_middle_log(&mut self, writer: Box<dyn std::io::Write + Send>) {
        self.air_middle_log.set_log(Some(writer));
    }

    pub fn set_air_final_log(&mut self, writer: Box<dyn std::io::Write + Send>) {
        self.air_final_log.set_log(Some(writer));
    }

    pub fn set_smt_log(&mut self, writer: Box<dyn std::io::Write + Send>) {
        self.smt_log.set_log(Some(writer));
    }

    pub fn set_smt_transcript_log(&mut self, writer: Box<dyn std::io::Write + Send>) {
        if let Some(smt_process) = &mut self.smt_process {
            smt_process.set_transcript_log(writer);
        } else {
            self.smt_transcript_log = Some(writer);
        }
    }

    pub fn set_debug(&mut self, debug: bool) {
        self.debug = debug;
    }

    pub fn get_debug(&self) -> bool {
        self.debug
    }

    pub fn get_solver(&self) -> &SmtSolver {
        &self.solver
    }

    pub fn set_ignore_unexpected_smt(&mut self, ignore_unexpected_smt: bool) {
        self.ignore_unexpected_smt = ignore_unexpected_smt;
    }

    pub fn get_time(&self) -> (Duration, Duration) {
        (self.time_smt_init, self.time_smt_run)
    }

    pub fn get_rlimit_count(&self) -> Option<(u64, u64)> {
        self.rlimit_count
    }

    pub fn set_expected_solver_version(&mut self, version: String) {
        self.expected_solver_version = Some(version);
    }

    /// Whether goal labels (and, later, other top-level assertions) carry
    /// their provenance ids on the wire. Defaults to the solver being cvc5.
    pub fn set_emit_assert_ids(&mut self, enabled: bool) {
        self.emit_assert_ids = enabled;
    }

    /// The provenance cvc5 reported for the most recent `check-sat`, if any;
    /// each call returns it once.
    pub fn take_provenance(&mut self) -> Option<ProvenanceInfo> {
        self.last_provenance.take().map(|mut info| {
            info.variable_versions = self.variable_versions.clone();
            info
        })
    }

    /// Why the most recent `check-sat` answered `unknown`, if it did; each call
    /// returns it once. Rounds that did not answer `unknown` leave none.
    pub fn take_unknown_reason(&mut self) -> Option<UnknownReason> {
        self.last_unknown_reason.take()
    }

    /// The nonlinear frontier cvc5 reported for the most recent `check-sat`,
    /// if it was asked; each call returns it once.
    pub fn take_nl_frontier(&mut self) -> Option<NlFrontier> {
        self.last_nl_frontier.take().map(|mut frontier| {
            frontier.variable_versions = self.variable_versions.clone();
            frontier
        })
    }

    /// Ask cvc5 for `(get-info :nl-frontier)` after every `check-sat` (cvc5
    /// only). Nothing about the solver's launch or budget changes.
    pub fn set_nl_frontier(&mut self, enabled: bool) {
        assert!(!enabled || matches!(self.solver, SmtSolver::Cvc5));
        self.nl_frontier = enabled;
    }

    /// The instantiation pressure cvc5 reported for the most recent
    /// `check-sat`, if it was asked; each call returns it once.
    pub fn take_inst_pressure(&mut self) -> Option<InstPressure> {
        self.last_inst_pressure.take()
    }

    /// Ask for `(get-info :inst-pressure)` after every `check-sat` (cvc5 only).
    /// It only reads counters, so the solver and its budget are unchanged.
    pub fn set_inst_pressure(&mut self, enabled: bool) {
        assert!(!enabled || matches!(self.solver, SmtSolver::Cvc5));
        self.inst_pressure = enabled;
    }

    /// Turn provenance mode on (cvc5 only; must precede the first query).
    /// Under it the solver is launched with `--proof-mode=pp-only`, each
    /// query runs with twice the budget, and the sources are requested.
    pub fn set_provenance(&mut self, enabled: bool) {
        assert!(matches!(self.state, ContextState::NotStarted));
        assert!(!enabled || matches!(self.solver, SmtSolver::Cvc5));
        self.provenance = enabled;
    }

    /// The matching loops cvc5 reported after the most recent unknown
    /// `check-sat`, if any; each call returns them once.
    pub fn take_matching_loops(&mut self) -> Option<MatchingLoopsInfo> {
        self.last_matching_loops.take().map(|mut info| {
            info.variable_versions = self.variable_versions.clone();
            info
        })
    }

    /// Turn matching-loop mode on (cvc5 only; must precede the first query).
    /// The solver is launched with `--matching-loops`, and with
    /// `--inst-max-rounds` when `inst_max_rounds` is given; each unknown is
    /// followed by `(get-info :matching-loops)`.
    pub fn set_matching_loops(&mut self, enabled: bool, inst_max_rounds: Option<u32>) {
        assert!(matches!(self.state, ContextState::NotStarted));
        assert!(!enabled || matches!(self.solver, SmtSolver::Cvc5));
        self.matching_loops = enabled;
        self.inst_max_rounds = if enabled { inst_max_rounds } else { None };
    }

    /// The difficulty gradient cvc5 reported for the most recent
    /// `check-sat`, if it was asked; each call returns it once.
    pub fn take_difficulty(&mut self) -> Option<DifficultyGradient> {
        self.last_difficulty.take()
    }

    /// Turn difficulty mode on (cvc5 only; must precede the first query).
    /// Under it the solver is launched with `DIFFICULTY_ARGS`, each query
    /// runs with twice the budget, and `(get-info :difficulty-gradient)`
    /// follows every `check-sat`.
    pub fn set_difficulty(&mut self, enabled: bool) {
        assert!(matches!(self.state, ContextState::NotStarted));
        assert!(!enabled || matches!(self.solver, SmtSolver::Cvc5));
        self.difficulty = enabled;
    }

    /// Allow saving and restoring instantiations (cvc5 only; must precede the
    /// first query). The solver is launched with `--no-fresh-declarations`,
    /// so a recheck's re-declared constants are the ones its saved
    /// instantiations mention.
    pub fn set_instantiation_replay(&mut self, enabled: bool) {
        assert!(matches!(self.state, ContextState::NotStarted));
        assert!(!enabled || matches!(self.solver, SmtSolver::Cvc5));
        self.instantiation_replay = enabled;
    }

    pub fn instantiation_replay(&self) -> bool {
        self.instantiation_replay
    }

    /// Record the instantiation graph (cvc5 only; must precede the first
    /// query). The solver is launched with `--inst-graph`.
    pub fn set_inst_graph(&mut self, enabled: bool) {
        assert!(matches!(self.state, ContextState::NotStarted));
        assert!(!enabled || matches!(self.solver, SmtSolver::Cvc5));
        self.inst_graph = enabled;
    }

    pub fn inst_graph(&self) -> bool {
        self.inst_graph
    }

    /// Launch the solver with every quantifier instantiation strategy
    /// available to `set_quant_strategy` (cvc5 only; must precede the first
    /// query). The strategies the default schedule leaves off are created but
    /// stay idle, so a check without a strategy runs that schedule.
    pub fn set_strategy_ladder(&mut self, enabled: bool) {
        assert!(matches!(self.state, ContextState::NotStarted));
        assert!(!enabled || matches!(self.solver, SmtSolver::Cvc5));
        self.strategy_ladder = enabled;
    }

    pub fn strategy_ladder(&self) -> bool {
        self.strategy_ladder
    }

    /// Run the next `check_valid`'s first `check-sat` with one instantiation
    /// strategy (`ematch`, `conflict`, `pool`, `enum` or `mbqi`; cvc5 only),
    /// `alone` or alongside the default schedule. The options are set right
    /// before that `check-sat` and set back right after it, so they apply to
    /// that check alone, and `(get-info :strategy-rung)` is read in between
    /// (`take_strategy_rung`). That `check_valid` consumes the setting
    /// whether or not it reaches the solver, so a later check never inherits
    /// it. A strategy the solver has no module for runs nothing; one launched
    /// without `set_strategy_ladder` has E-matching and pools only.
    pub fn set_quant_strategy(&mut self, strategy: Option<&str>, alone: bool) {
        assert!(strategy.is_none() || matches!(self.solver, SmtSolver::Cvc5));
        self.quant_strategy = strategy.map(|strategy| (strategy.to_owned(), alone));
    }

    /// What the most recent `check-sat` run under `set_quant_strategy`
    /// reported, if one ran; each call returns it once.
    pub fn take_strategy_rung(&mut self) -> Option<StrategyRung> {
        self.last_strategy_rung.take()
    }

    /// Ask cvc5 for `(get-info :strategy-rung)` between queries, starting the
    /// context and the solver if needed, and flush whatever was queued
    /// before. `None` when the solver does not know the key, as a cvc5
    /// without `:quant-strategy` would not: setting that option on one would
    /// fail the next check. Read-only. The `available` list is filled in by
    /// the solver's first `check-sat`, so it is empty before one has run.
    pub fn probe_strategy_rung(&mut self) -> Option<StrategyRung> {
        if !matches!(self.solver, SmtSolver::Cvc5) {
            return None;
        }
        self.ensure_started();
        self.get_smt_process();
        self.smt_log.log_get_info("strategy-rung");
        let lines = self.flush_commands();
        let line = lines.iter().find(|line| line.starts_with("(:strategy-rung "))?;
        let rung = crate::smt_verify::parse_strategy_rung(line);
        rung.unparsed.is_none().then_some(rung)
    }

    /// The `reproducible-resource-limit` the next query's checks run with
    /// (cvc5 only): the rlimit, doubled in the modes that pay for proofs.
    pub fn cvc5_query_budget(&self) -> u32 {
        crate::smt_verify::cvc5_query_budget(self)
    }

    /// Ask the solver for the instantiation graph of its last `check-sat` and
    /// return its reply lines (cvc5 with `set_inst_graph` only). Read-only:
    /// call it after a query's answer and before anything that checks again.
    pub fn instantiation_graph(&mut self) -> Vec<String> {
        assert!(self.inst_graph);
        self.smt_log.log_get_instantiation_graph();
        self.flush_commands()
    }

    /// Restore the instantiations saved under `key` in the next query's scope
    /// (cvc5 only). cvc5 replays each saved term vector through its own
    /// instantiation path, and only for quantifiers that scope asserts, so a
    /// key that saved nothing, or saved for another query, is harmless. With
    /// `only`, no other instantiation happens in that scope, so the solver
    /// answers unsat or unknown from the restored instances alone.
    pub fn set_restore_instantiations(&mut self, key: Option<String>, only: bool) {
        assert!(key.is_none() || matches!(self.solver, SmtSolver::Cvc5));
        self.restore_instantiations = key.map(|key| (key, only));
    }

    /// Whether this solver has saved instantiations under `key`.
    pub fn has_saved_instantiations(&self, key: &str) -> bool {
        self.saved_instantiations.contains(key)
    }

    /// Import `certificate`, which another solver exported, in the next query's
    /// scope just before its first `check-sat`, where the query's declarations
    /// are in scope (cvc5 only). cvc5 skips an entry naming a symbol it has not
    /// declared.
    pub fn set_import_instantiations(&mut self, certificate: Option<ImportInstantiations>) {
        assert!(certificate.is_none() || matches!(self.solver, SmtSolver::Cvc5));
        self.import_instantiations = certificate;
    }

    /// Ask the solver for what `key` saved, as a certificate another solver
    /// can import (cvc5 only). `None` when the reply is an error, or names no
    /// instance. Flushes: call it after `save_instantiations` and before
    /// `finish_query`.
    pub fn export_instantiations(&mut self, key: &str) -> Option<ImportInstantiations> {
        assert!(matches!(self.solver, SmtSolver::Cvc5));
        self.smt_log.log_export_instantiations(key);
        ImportInstantiations::parse(&self.flush_commands().join("\n"), key)
    }

    /// Save the current query's instantiations under `key` before
    /// `finish_query` pops its scope (cvc5 only). Call only after the solver
    /// answered the query: cvc5 rejects a save with no result to save from.
    pub fn save_instantiations(&mut self, key: &str) {
        assert!(matches!(self.solver, SmtSolver::Cvc5));
        self.smt_log.log_save_instantiations(key);
        self.saved_instantiations.insert(key.to_owned());
    }

    /// Ask each following query's first `check-sat` for the equalities
    /// cvc5's e-graph then holds, in the classes of the query's own terms,
    /// until set to `None` (cvc5 only). Take each reply with `take_egraph`
    /// after `check_valid`. Assignment versions are recorded for the reply,
    /// as in provenance mode. The request is read in the same batch as the
    /// check, so nothing sent after `check-sat` has changed the solver's state.
    /// `None` also drops focus terms or an injected equality that a check
    /// which never reached `check-sat` left behind.
    pub fn set_egraph_request(&mut self, request: Option<EgraphRequest>) {
        assert!(request.is_none() || matches!(self.solver, SmtSolver::Cvc5));
        self.egraph_request = request;
        if request.is_none() {
            self.egraph_focus = None;
            self.inject_equality = None;
        }
    }

    /// The reply to the e-graph request of the most recent query, if one was
    /// asked for; each call returns it once.
    pub fn take_egraph(&mut self) -> Option<EgraphReply> {
        self.last_egraph.take().map(|mut reply| {
            reply.variable_versions = self.variable_versions.clone();
            reply
        })
    }

    /// Assert `lhs = rhs` in the next query's scope, after its own assertion
    /// and just before its first `check-sat` (cvc5 only). `finish_query` pops
    /// it with the scope. The terms must come from an `EgraphReply` of the
    /// same solver for the same query, which names only symbols that scope
    /// declares: cvc5 exits on a term it cannot parse. Err if either is not a
    /// single s-expression.
    pub fn set_inject_equality(&mut self, lhs: &str, rhs: &str) -> Result<(), String> {
        assert!(matches!(self.solver, SmtSolver::Cvc5));
        let parse = |term: &str| {
            sise::parse_tree(&mut sise::Parser::new(term))
                .map_err(|_| format!("not a single SMT term: {term}"))
        };
        self.inject_equality = Some((parse(lhs)?, parse(rhs)?));
        Ok(())
    }

    pub fn set_profile_with_logfile_name(&mut self, file_name: String) {
        assert!(matches!(self.state, ContextState::NotStarted));
        self.profile_logfile_name = Some(file_name);
    }

    pub fn set_rlimit(&mut self, rlimit: u32) {
        self.rlimit = rlimit;
        // The AIR logs record the budget in solver units whichever solver runs.
        self.air_initial_log.log_set_option("rlimit", &rlimit.to_string());
        self.air_middle_log.log_set_option("rlimit", &rlimit.to_string());
        self.air_final_log.log_set_option("rlimit", &rlimit.to_string());
    }

    pub fn set_single_check_query(&mut self) {
        self.single_check_query = true;
        self.air_initial_log.log_set_option("single_check_query", "true");
        self.air_middle_log.log_set_option("single_check_query", "true");
        self.air_final_log.log_set_option("single_check_query", "true");
    }

    pub fn enable_usage_info(&mut self) {
        assert!(matches!(self.state, ContextState::NotStarted));
        self.usage_info_enabled = true;
        self.set_z3_param_bool("produce-unsat-cores", true, true);
    }

    // emit blank line into log files
    pub fn blank_line(&mut self) {
        self.air_initial_log.blank_line();
        self.air_middle_log.blank_line();
        self.air_final_log.blank_line();
        self.smt_log.blank_line();
    }

    // Single-line comment, emitted with ";;" into log files
    pub fn comment(&mut self, s: &str) {
        self.air_initial_log.comment(s);
        self.air_middle_log.comment(s);
        self.air_final_log.comment(s);
        self.smt_log.comment(s);
    }

    fn log_set_z3_param(&mut self, option: &str, value: &str) {
        self.air_initial_log.log_set_option(option, value);
        self.air_middle_log.log_set_option(option, value);
        self.air_final_log.log_set_option(option, value);
        self.smt_log.log_set_option(option, value);
    }

    pub(crate) fn set_z3_param_bool(&mut self, option: &str, value: bool, write_to_logs: bool) {
        if option == "air_recommended_options" && value {
            match self.solver {
                SmtSolver::Z3 => {
                    self.set_z3_param_bool("auto_config", false, true);
                    self.set_z3_param_bool("smt.mbqi", false, true);
                    self.set_z3_param_u32("smt.case_split", 3, true);
                    self.set_z3_param_f64("smt.qi.eager_threshold", 100.0, true);
                    self.set_z3_param_bool("smt.delay_units", true, true);
                    self.set_z3_param_u32("smt.arith.solver", 2, true);
                    self.set_z3_param_bool("smt.arith.nl", false, true);
                    self.set_z3_param_bool("pi.enabled", false, true);
                    self.set_z3_param_bool("rewriter.sort_disjunctions", false, true);
                }
                SmtSolver::Cvc5 => {
                    self.smt_log.log_node(&node!((set-logic {str_to_node("ALL")})));
                    self.set_z3_param_bool("incremental", true, true);
                }
            }
        } else if option == "single_check_query" && value {
            self.single_check_query = true;
            if write_to_logs {
                self.set_single_check_query();
            }
        } else {
            if write_to_logs {
                self.log_set_z3_param(option, &value.to_string());
            }
        }
    }

    pub(crate) fn set_z3_param_u32(&mut self, option: &str, value: u32, write_to_logs: bool) {
        if option == "rlimit" && write_to_logs && matches!(self.solver, SmtSolver::Z3) {
            self.set_rlimit(value);
        } else {
            if write_to_logs {
                self.log_set_z3_param(option, &value.to_string());
            }
        }
    }

    pub(crate) fn set_z3_param_f64(&mut self, option: &str, value: f64, write_to_logs: bool) {
        if write_to_logs {
            let mut s = value.to_string();
            if !s.contains(".") {
                s += ".0";
            }
            self.log_set_z3_param(option, &s);
        }
    }

    pub(crate) fn set_z3_param_str(&mut self, option: &str, value: &str, write_to_logs: bool) {
        if write_to_logs {
            self.log_set_z3_param(option, value);
        }
    }

    pub fn set_z3_param(&mut self, option: &str, value: &str) {
        if value == "true" {
            self.set_z3_param_bool(option, true, true);
        } else if value == "false" {
            self.set_z3_param_bool(option, false, true);
        } else if let Ok(v) = value.parse::<u32>() {
            self.set_z3_param_u32(option, v, true);
        } else if let Ok(v) = value.parse::<f64>() {
            self.set_z3_param_f64(option, v, true);
        } else if value.is_ascii() {
            self.set_z3_param_str(option, value, true);
        } else {
            panic!("unexpected z3 param {}", value);
        }
    }

    pub(crate) fn push_name_scope(&mut self) {
        self.name_counters.push(NameCounters {
            axiom_infos: self.axiom_infos_count,
            array: self.array_count,
            lambda: self.lambda_count,
            choose: self.choose_count,
            apply: self.apply_count,
            anon_axiom: self.anon_axiom_count,
        });
        self.axiom_infos.push_scope(false);
        self.array_map.push_scope(false);
        self.lambda_map.push_scope(false);
        self.choose_map.push_scope(false);
        self.apply_map.push_scope(false);
        self.typing.decls.push_scope(false);
    }

    pub(crate) fn pop_name_scope(&mut self) {
        // The popped scope's names left the solver with it, and the maps below
        // forget them, so its numbers are free for the next scope to reuse.
        let counters =
            self.name_counters.pop().expect("pop_name_scope without a matching push_name_scope");
        self.axiom_infos_count = counters.axiom_infos;
        self.array_count = counters.array;
        self.lambda_count = counters.lambda;
        self.choose_count = counters.choose;
        self.apply_count = counters.apply;
        self.anon_axiom_count = counters.anon_axiom;
        self.axiom_infos.pop_scope();
        self.array_map.pop_scope();
        self.lambda_map.pop_scope();
        self.choose_map.pop_scope();
        self.apply_map.pop_scope();
        self.typing.decls.pop_scope();
    }

    pub(crate) fn ensure_started(&mut self) {
        match self.state {
            ContextState::NotStarted => {
                let profile_logfile_name = self.profile_logfile_name.clone();
                if let Some(profile_logfile_name) = profile_logfile_name {
                    self.set_z3_param("trace", "true");
                    // Very expensive.  May be needed to support more detailed log analysis.
                    // self.set_z3_param("proof", "true");

                    // sise does not support backslashes in atoms, which appear in Windows paths
                    let profile_logfile_name = profile_logfile_name.replace("\\", "/");
                    self.log_set_z3_param("trace_file_name", &profile_logfile_name);
                }
                self.blank_line();
                if self.provenance {
                    self.comment(&format!(
                        "provenance mode: cvc5 args {}",
                        crate::smt_process::PROVENANCE_ARGS.join(" ")
                    ));
                }
                if self.matching_loops {
                    let rounds = match self.inst_max_rounds {
                        Some(n) => format!(" --inst-max-rounds={n}"),
                        None => String::new(),
                    };
                    self.comment(&format!(
                        "matching-loop mode: cvc5 args --matching-loops{rounds}"
                    ));
                }
                if self.difficulty {
                    self.comment(&format!(
                        "difficulty mode: cvc5 args {}",
                        crate::smt_process::DIFFICULTY_ARGS.join(" ")
                    ));
                }
                self.comment("AIR prelude");
                self.smt_log.log_node(&node!((declare-sort {str_to_node(crate::def::FUNCTION)} 0)));
                self.blank_line();
                self.state = ContextState::ReadyForQuery;
            }
            ContextState::ReadyForQuery => {}
            ContextState::NoMoreQueriesAllowed => {
                panic!("no more queries allowed after disabling incremental solving");
            }
            _ => {
                panic!("expected call to finish_query before next command");
            }
        }
    }

    pub fn push(&mut self) {
        self.ensure_started();
        self.air_initial_log.log_push();
        self.air_middle_log.log_push();
        self.air_final_log.log_push();
        self.smt_log.log_push();
        self.push_name_scope();
    }

    pub fn pop(&mut self) {
        self.air_initial_log.log_pop();
        self.air_middle_log.log_pop();
        self.air_final_log.log_pop();
        self.smt_log.log_pop();
        self.pop_name_scope();
    }

    pub fn global(&mut self, decl: &Decl) -> Result<(), TypeError> {
        self.ensure_started();
        self.air_initial_log.log_decl(decl);
        self.air_middle_log.log_decl(decl);
        self.air_final_log.log_decl(decl);
        let (gen_decls, decl) = crate::typecheck::check_decl(self, decl)?;
        for gen_decl in gen_decls.iter() {
            crate::smt_verify::smt_add_decl(self, gen_decl);
        }
        crate::typecheck::add_decl(self, &decl, true)?;
        crate::smt_verify::smt_add_decl(self, &decl);
        Ok(())
    }

    pub fn check_valid(
        &mut self,
        message_interface: &dyn crate::messages::MessageInterface,
        diagnostics: &impl Diagnostics,
        query: &Query,
        query_context: QueryContext<'_, '_>,
    ) -> ValidityResult {
        self.ensure_started();
        // Cleared here as well as in `smt_check_assertion`: a query can fail
        // before it reaches the solver, and must not report an earlier reason.
        self.last_unknown_reason = None;

        self.air_initial_log.log_query(query);
        let query = match crate::typecheck::check_query(self, query) {
            Ok(query) => query,
            Err(err) => {
                // This check's strategy, whether or not it reached the solver.
                self.quant_strategy = None;
                return ValidityResult::TypeError(err);
            }
        };
        let (query, snapshots, local_vars, variable_versions) = crate::var_to_const::lower_query(
            &query,
            self.provenance || self.egraph_request.is_some(),
        );
        self.variable_versions = variable_versions;
        self.air_middle_log.log_query(&query);
        let query = crate::block_to_assert::lower_query(message_interface, &query);
        self.air_final_log.log_query(&query);

        let model = Model::new(snapshots, local_vars);
        let validity = crate::smt_verify::smt_check_query(
            self,
            diagnostics,
            &query,
            model,
            query_context.report_long_running,
        );
        self.check_valid_used = true;
        // Taken by this check's check-sat; cleared here too for a check that
        // stopped before one, so the strategy never reaches a later check.
        self.quant_strategy = None;

        validity
    }

    pub fn check_valid_used(&self) -> bool {
        self.check_valid_used
    }

    /// After receiving ValidityResult::Invalid, try to find another error.
    /// only_check_earlier == true means to only look for errors preceding all the previous
    /// errors, with the goal of making sure that the earliest error gets reported.
    /// Once only_check_earlier is set, it remains set until finish_query is called.
    pub fn check_valid_again(
        &mut self,
        diagnostics: &impl Diagnostics,
        only_check_earlier: bool,
        query_context: QueryContext<'_, '_>,
    ) -> ValidityResult {
        if let ContextState::FoundInvalid(infos, Some(air_model)) = self.state.clone() {
            let res = crate::smt_verify::smt_check_assertion(
                self,
                diagnostics,
                infos,
                air_model,
                only_check_earlier,
                query_context.report_long_running,
            );
            self.check_valid_used = true;
            res
        } else {
            panic!("check_valid_again expected query to be ValidityResult::Invalid(_, Some(_))");
        }
    }

    pub fn finish_query(&mut self) {
        if self.single_check_query {
            self.state = ContextState::NoMoreQueriesAllowed;
        } else {
            self.pop_name_scope();
            self.smt_log.log_pop();
            self.state = ContextState::ReadyForQuery;
        }
    }

    pub fn eval_expr(&mut self, expr: sise::TreeNode) -> String {
        self.smt_log.log_eval(expr);
        let smt_data = self.smt_log.take_pipe_data();
        let smt_output = self.get_smt_process().send_commands(smt_data);
        if smt_output.len() != 1 {
            panic!("unexpected output from SMT eval {:?}", smt_output);
        }
        smt_output[0].clone()
    }

    pub fn command(
        &mut self,
        message_interface: &dyn crate::messages::MessageInterface,
        diagnostics: &impl Diagnostics,
        command: &Command,
        query_context: QueryContext<'_, '_>,
    ) -> ValidityResult {
        match &**command {
            CommandX::Push => {
                self.push();
                ValidityResult::Valid(UsageInfo::None)
            }
            CommandX::Pop => {
                self.pop();
                ValidityResult::Valid(UsageInfo::None)
            }
            CommandX::SetOption(option, value) => {
                self.set_z3_param(option, value);
                ValidityResult::Valid(UsageInfo::None)
            }
            CommandX::Global(decl) => {
                if let Err(err) = self.global(&decl) {
                    ValidityResult::TypeError(err)
                } else {
                    ValidityResult::Valid(UsageInfo::None)
                }
            }
            CommandX::CheckValid(query) => {
                self.check_valid(message_interface, diagnostics, &query, query_context)
            }
            #[cfg(feature = "singular")]
            CommandX::CheckSingular(_) => {
                panic!("CheckSingular not supported in this context");
            }
        }
    }
}
