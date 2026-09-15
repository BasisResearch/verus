//! A counterfactual twin of one retained query (`counterfactual_twin`).
//!
//! The request names one edit: remove or add an axiom (a hypothesis, a
//! module-level axiom such as a broadcast lemma, or an AIR expression), set a
//! function's fuel, raise the resource limit, or reorder assertions. The
//! worker checks the query as it was retained (the base) and then the edited
//! query (the twin), each as an ordinary check in its own scope on the same
//! declaration prefix, and reports how the two checks differ: the answers,
//! the instantiations per quantifier and inference, the resource units, and in
//! a difficulty session each input assertion's difficulty and unsat-core
//! membership (`air::twin`).
//!
//! Only the edit's own scope ever holds the edit. A module-level axiom is
//! removed by rebuilding the prefix without it, from the first scope holding
//! it, in scopes that are popped before the reply; the recorded prefix is
//! then replayed as it was. An axiom below every scope (the bucket's base
//! context) cannot be rebuilt away; a fuel-guarded one, as a broadcast
//! lemma's is, is hidden through the query's fuel hypothesis instead, and
//! the reply says so. The reply says how many scopes the solver has open
//! before and after, and with `recheck_base` checks the base once more and
//! compares it with the first base check.
//!
//! Neither check is a verification result, and the twin's verdict licenses
//! nothing: an added axiom is assumed, not proved.

use super::{QueryDiagnostics, QueryId, QueryJournal, QueryResult, RetainedBucket, SolverState};
use crate::provenance::{ResolvedTag, Symbols};
use air::ast::{
    AssertId, Axiom, BinaryOp, BindX, BinderX, CommandX, DeclX, Expr, ExprX, Ident, MultiOp, Quant,
    Query, TypX,
};
use air::context::{
    BranchProfile, Context, DifficultyGradient, InstPressure, QueryContext, SmtSolver,
    UnknownReason, ValidityResult,
};
use air::twin::{AxiomRef, InstCounts};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeSet, HashSet};
use std::io;
use std::sync::Arc;
use std::time::Instant;
use vir::ast::Fun;
use vir::messages::VirMessageInterface;

/// The one edit a twin makes, spelled as the protocol spells it:
/// `{"remove_axiom": "hyp_1"}`, `{"flip_fuel": {"fn": "f", "fuel": 0}}`, ...
#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "snake_case", deny_unknown_fields)]
pub(super) enum TwinEdit {
    /// An AIR expression, or the name of a broadcast lemma or group (or
    /// its axiom's tag or qid), which applies as `broadcast use` would: its
    /// fuel is assumed, and its axiom added when the bucket declared it only
    /// for a later query.
    AddAxiom(String),
    /// A hypothesis tag (`hyp_1`), an axiom tag (`ax_...`), a quantifier's
    /// `:qid`, or the function a broadcast axiom belongs to.
    RemoveAxiom(String),
    /// Give `fn` this much fuel for the whole query: 0 hides its
    /// definition, 1 reveals it, more unrolls a recursive one further.
    FlipFuel {
        #[serde(rename = "fn")]
        function: String,
        fuel: u32,
    },
    /// Check the twin with this rlimit, in the units of `--rlimit`.
    BumpRlimit(f32),
    /// These assertions of one block, by `AssertId`, in this order.
    ReorderAsserts(Vec<AssertName>),
}

/// An `AssertId` as a request may spell it: `[3, 1]`, `"3.1"`, `"aid_3_1"`
/// or `"assert@3.1"`.
#[derive(Clone, Debug, Deserialize)]
#[serde(untagged)]
pub(super) enum AssertName {
    Path(Vec<u64>),
    Text(String),
}

impl AssertName {
    fn id(&self) -> Option<AssertId> {
        match self {
            AssertName::Path(path) => Some(Arc::new(path.clone())),
            AssertName::Text(text) => {
                let text = text.trim();
                let text = text.strip_prefix("assert@").unwrap_or(text);
                let text = text.strip_prefix("aid_").unwrap_or(text);
                let parts: Option<Vec<u64>> =
                    text.split(['.', '_']).map(|part| part.parse().ok()).collect();
                parts.filter(|p| !p.is_empty()).map(Arc::new)
            }
        }
    }
}

pub(super) struct TwinRequest {
    pub(super) edit: TwinEdit,
    /// How many quantifiers and assertions the reply lists at most.
    pub(super) limit: usize,
    /// Check the base again after the twin, and compare.
    pub(super) recheck_base: bool,
}

/// The default and the most rows a reply lists.
pub(super) const DEFAULT_TWIN_LIMIT: usize = 20;
pub(super) const MAX_TWIN_LIMIT: usize = 200;
/// The `:qid` of the fuel hypothesis a twin writes when it hides a function
/// in a query that hid none.
const TWIN_FUEL_QID: &str = "internal_twin_nondefault_fuel";
/// The provenance tag (`ax_twin_fuel`) of a fuel assumption a twin adds.
const TWIN_FUEL_TAG: &str = "twin_fuel";
/// A twin's rlimit may be at most this many times the query's.
const MAX_RLIMIT_FACTOR: f32 = 16.0;

const CAVEAT: &str = "Both checks ran in scopes popped right after them; the session's solver state is unchanged. Neither is a verification result: make the edit in the source and verify it normally, and prove an added axiom before relying on it. Resource units and elapsed time of two checks in one solver differ by more than the edit (caches survive a pop): read instantiation counts first, and recheck_base to measure the noise.";

#[derive(Serialize)]
pub(super) struct TwinReport {
    edit: EditReport,
    base: BranchReport,
    twin: BranchReport,
    outcome_flip: OutcomeFlip,
    /// Null only when the solver reported no instantiation counters.
    inst_count_delta: Option<InstCountDelta>,
    /// Null outside a difficulty session (see `unavailable`).
    difficulty_delta: Option<DifficultyDeltaReport>,
    did_relevant_delta: Option<RelevanceReport>,
    /// For `add_axiom`: whether the twin's context may prove its goal only
    /// because it contradicts itself.
    #[serde(skip_serializing_if = "Option::is_none")]
    vacuity: Option<Vacuity>,
    /// Whether the solver was left as it was found. Not `session`: the
    /// reply's event already names its session under that key.
    integrity: SessionCheck,
    /// Parts of the comparison this session could not make, and why.
    unavailable: Vec<String>,
    caveat: &'static str,
    pub(super) elapsed_ms: u128,
    pub(super) restore_ms: u128,
}

#[derive(Serialize)]
struct EditReport {
    /// add_axiom, remove_axiom, flip_fuel, bump_rlimit or reorder_asserts
    kind: &'static str,
    /// The axioms removed, or the one added by name.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    axioms: Vec<MatchedAxiom>,
    /// An added AIR expression, as given.
    #[serde(skip_serializing_if = "Option::is_none")]
    expression: Option<String>,
    /// The function whose fuel the twin assumes so that an added axiom
    /// applies, as `broadcast use` of it would.
    #[serde(skip_serializing_if = "Option::is_none")]
    fuel_assumed: Option<String>,
    /// For flip_fuel, and for remove_axiom of a base-context axiom, which
    /// is hidden (fuel 0) rather than removed.
    #[serde(skip_serializing_if = "Option::is_none")]
    fuel: Option<FuelReport>,
    #[serde(skip_serializing_if = "Option::is_none")]
    rlimit: Option<Pair<f32>>,
    /// The assertions moved, in their new order.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    order: Vec<String>,
    /// Scopes of the prefix rebuilt without a removed module-level axiom.
    #[serde(skip_serializing_if = "Option::is_none")]
    rebuilt_scopes: Option<usize>,
}

#[derive(Clone, Serialize)]
struct MatchedAxiom {
    /// `query`: a local declaration of the query (a hypothesis has kind
    /// requires, type_invariant, fuel or trait_bound); `prefix`: a
    /// module-level axiom in the query's context; `base`: one below every
    /// scope (declared before the bucket's first query, or before a spinoff
    /// solver's first); `retained`: one the bucket declared after this
    /// query's prefix.
    place: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    tag: Option<ResolvedTag>,
    #[serde(skip_serializing_if = "Option::is_none")]
    qid: Option<String>,
}

#[derive(Serialize)]
struct FuelReport {
    /// The function, as its fuel constant names it.
    function: String,
    fuel: u32,
    recursive: bool,
    /// Whether its module gives it fuel by default.
    default_visible: bool,
    /// Whether the query hid it before the edit.
    hidden_before: bool,
    /// `reveal`s of it in the body, removed so the edit decides alone.
    reveals_removed: usize,
}

#[derive(Clone, Copy, Serialize)]
struct Pair<T> {
    base: T,
    twin: T,
}

#[derive(Serialize)]
struct BranchReport {
    /// As check_session reports it.
    result: QueryResult,
    /// valid, invalid, resource_limit or incomplete (cvc5 gave up, which
    /// check_session reports as invalid).
    class: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    reason: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    incomplete_id: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    assert_id: Option<Vec<u64>>,
    rlimit: f32,
    /// What cvc5 spent on the check, when it says.
    #[serde(skip_serializing_if = "Option::is_none")]
    resource_units: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    instantiations: Option<u64>,
    elapsed_ms: u128,
}

#[derive(Serialize)]
struct OutcomeFlip {
    base: &'static str,
    twin: &'static str,
    flipped: bool,
}

#[derive(Serialize)]
struct InstCountDelta {
    total: i64,
    base_total: u64,
    twin_total: u64,
    rounds: Pair<u64>,
    /// Whether instances are split by the inference that sent them.
    by_inference: bool,
    /// Quantifiers whose count changed; those instantiated in only one check.
    changed: usize,
    started: Vec<String>,
    stopped: Vec<String>,
    /// The share of all the change that the first row carries, 0 to 1.
    #[serde(skip_serializing_if = "Option::is_none")]
    top_share: Option<f64>,
    /// Largest change first; `omitted` more had a change too.
    by_quantifier: Vec<QuantDeltaReport>,
    omitted: usize,
}

#[derive(Serialize)]
struct QuantDeltaReport {
    qid: String,
    /// The function (or prelude) the quantifier belongs to, and where it is
    /// written when the user wrote it.
    #[serde(skip_serializing_if = "Option::is_none")]
    fun: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    span: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    role: Option<&'static str>,
    base: u64,
    twin: u64,
    delta: i64,
    /// Attempts rejected as duplicates in each check.
    #[serde(skip_serializing_if = "is_zero_pair")]
    duplicates: Pair<u64>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    by_inference: Vec<InferenceReport>,
}

fn is_zero_pair(pair: &Pair<u64>) -> bool {
    pair.base == 0 && pair.twin == 0
}

#[derive(Serialize)]
struct InferenceReport {
    inference: String,
    base: u64,
    twin: u64,
    delta: i64,
}

#[derive(Serialize)]
struct DifficultyDeltaReport {
    /// The base check's most difficult input assertion, and its difficulty
    /// in the twin.
    hardest_assertion: Option<TagDeltaReport>,
    total: Pair<u64>,
    /// Largest change first; `omitted` more changed too.
    rows: Vec<TagDeltaReport>,
    omitted: usize,
}

#[derive(Serialize)]
struct TagDeltaReport {
    tags: Vec<ResolvedTag>,
    /// Null where the check did not have the assertion.
    base: Option<u64>,
    twin: Option<u64>,
    delta: i64,
    #[serde(skip_serializing_if = "Option::is_none")]
    base_in_core: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    twin_in_core: Option<bool>,
}

#[derive(Serialize)]
struct RelevanceReport {
    /// unsat_core (both checks answered unsat) or difficulty (some lemma work
    /// flowed through the assertion; misses what cvc5 substituted away).
    basis: &'static str,
    became_relevant: Vec<Vec<ResolvedTag>>,
    became_irrelevant: Vec<Vec<ResolvedTag>>,
    /// Prelude axioms, and entries past the limit, left out.
    omitted: usize,
}

#[derive(Serialize)]
struct Vacuity {
    /// The class of a check of the query with every goal switched off (each
    /// goal also requires an unconstrained boolean) and every assumption
    /// kept: `valid` means the hypotheses and the body's assumptions
    /// contradict each other wherever a goal is reached, so any goal would
    /// be proved.
    base_goals_off: &'static str,
    twin_goals_off: &'static str,
    /// The added axiom makes the context contradictory where the base's
    /// was not.
    inconsistent: bool,
    /// The twin needed at most a tenth of the base's instantiations.
    instantiation_collapse: bool,
    /// The twin flipped to valid and is inconsistent or collapsed: the
    /// added axiom may prove the goal by proving anything.
    possibly_vacuous: bool,
}

#[derive(Serialize)]
struct SessionCheck {
    /// The solver's open scopes before the base check and after the twin,
    /// as cvc5 counts them; equal when every edit was popped.
    stack_levels_before: Option<u64>,
    stack_levels_after: Option<u64>,
    intact: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    recheck: Option<Recheck>,
}

#[derive(Serialize)]
struct Recheck {
    result: QueryResult,
    class: &'static str,
    /// Same class as the first base check.
    same_result: bool,
    /// Same instantiations per quantifier as the first base check.
    same_instantiations: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    instantiations: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    resource_units: Option<u64>,
    elapsed_ms: u128,
}

/// One check of a query, with what cvc5 reported about it.
struct Branch {
    result: QueryResult,
    assert_id: Option<Vec<u64>>,
    elapsed_ms: u128,
    rlimit: f32,
    pressure: Option<InstPressure>,
    profile: Option<BranchProfile>,
    difficulty: Option<DifficultyGradient>,
    unknown: Option<UnknownReason>,
}

impl Branch {
    fn class(&self) -> &'static str {
        match self.result {
            QueryResult::Valid => "valid",
            QueryResult::ResourceLimit => "resource_limit",
            QueryResult::Invalid => match &self.unknown {
                Some(unknown) if unknown.reason.contains("incomplete") => "incomplete",
                _ => "invalid",
            },
        }
    }

    fn counts(&self) -> InstCounts<'_> {
        InstCounts { pressure: self.pressure.as_ref(), profile: self.profile.as_ref() }
    }

    fn resource_units(&self) -> Option<u64> {
        self.profile.as_ref().filter(|p| p.unparsed.is_none()).map(|p| p.resource_units)
    }

    fn report(&self) -> BranchReport {
        let instantiations = self.counts().total();
        BranchReport {
            result: self.result,
            class: self.class(),
            reason: self.unknown.as_ref().map(|u| u.reason.clone()).filter(|r| !r.is_empty()),
            incomplete_id: self.unknown.as_ref().and_then(|u| u.incomplete_id.clone()),
            assert_id: self.assert_id.clone(),
            rlimit: self.rlimit,
            resource_units: self.resource_units(),
            instantiations,
            elapsed_ms: self.elapsed_ms,
        }
    }
}

enum BranchError {
    /// The check never reached the solver (the edited query does not
    /// type-check); the session is as it was.
    Refused(String),
    Fatal(io::Error),
}

/// Check `query` once, as a resident check does, reading the instantiation
/// counters and branch profile after its `check-sat`. The query's scope is
/// popped before this returns.
fn run_branch(
    air: &mut Context,
    query: &Query,
    rlimit: f32,
    set_rlimit: &impl Fn(&mut Context, f32),
) -> Result<Branch, BranchError> {
    set_rlimit(air, rlimit);
    let pressure_was = air.inst_pressure();
    air.set_inst_pressure(true);
    air.set_branch_profile(true);
    let start = Instant::now();
    let outcome = air.check_valid(
        &VirMessageInterface {},
        &QueryDiagnostics::default(),
        query,
        QueryContext::default(),
    );
    let elapsed_ms = start.elapsed().as_millis();
    air.set_inst_pressure(pressure_was);
    air.set_branch_profile(false);
    let pressure = air.take_inst_pressure();
    let profile = air.take_branch_profile();
    let difficulty = air.take_difficulty();
    let unknown = air.take_unknown_reason();
    drop(air.take_provenance());
    drop(air.take_matching_loops());
    drop(air.take_nl_frontier());
    let (result, assert_id) = match outcome {
        ValidityResult::Valid(_) => (QueryResult::Valid, None),
        ValidityResult::Invalid(_, _, id) => (QueryResult::Invalid, id.map(|id| (*id).clone())),
        ValidityResult::Canceled => (QueryResult::ResourceLimit, None),
        // A type error opens no scope to pop.
        ValidityResult::TypeError(error) => {
            return Err(BranchError::Refused(format!(
                "the edited query does not type-check: {}",
                error
            )));
        }
        ValidityResult::UnexpectedOutput(error) => {
            return Err(BranchError::Fatal(io::Error::other(error)));
        }
    };
    air.finish_query();
    Ok(Branch { result, assert_id, elapsed_ms, rlimit, pressure, profile, difficulty, unknown })
}

/// The edit, applied: the twin query, how to check it, and what to report.
struct Plan {
    query: Query,
    rlimit: f32,
    /// Rebuild the prefix from this scope without the axioms these names
    /// select, for a removed module-level axiom.
    rebuild: Option<(usize, Vec<String>)>,
    report: EditReport,
    /// Check the hypotheses alone in both queries (an added axiom).
    vacuity: bool,
}

/// Every module-level axiom of `scopes`, with the scope it is in.
fn prefix_axioms<'a>(
    journal: &'a QueryJournal,
    scopes: std::ops::Range<usize>,
) -> impl Iterator<Item = (usize, &'a Axiom)> + 'a {
    scopes.flat_map(move |scope| {
        journal.contexts[scope].iter().flat_map(move |batch| {
            batch.iter().filter_map(move |command| match &**command {
                CommandX::Global(decl) => match &**decl {
                    DeclX::Axiom(axiom) => Some((scope, axiom)),
                    _ => None,
                },
                _ => None,
            })
        })
    })
}

/// Every axiom of the bucket's base context, which lies below every scope.
fn base_axioms(journal: &QueryJournal) -> impl Iterator<Item = &Axiom> {
    journal.base.iter().flat_map(|batch| {
        batch.iter().filter_map(|command| match &**command {
            CommandX::Global(decl) => match &**decl {
                DeclX::Axiom(axiom) => Some(axiom),
                _ => None,
            },
            _ => None,
        })
    })
}

/// The names `name` stands for: itself, and the tags of the axioms a
/// function of that name states. A bare name that fits functions of several
/// paths is refused rather than taken for all of them.
fn names_for(name: &str, symbols: Option<&Symbols>) -> Result<Vec<String>, String> {
    let mut names = vec![name.trim().to_owned()];
    if let Some(symbols) = symbols {
        let owned = symbols.axioms_owned_by(name);
        let owners: BTreeSet<&str> = owned.iter().map(|(_, owner)| owner.as_str()).collect();
        if owners.len() > 1 {
            return Err(format!(
                "{name} names the axioms of {} functions ({}); give the full path",
                owners.len(),
                owners.into_iter().collect::<Vec<_>>().join(", ")
            ));
        }
        names.extend(owned.into_iter().map(|(tag, _)| tag));
    }
    Ok(names)
}

/// The fuel constant guarding `expr`, for an axiom of the shape Verus gives
/// a broadcast lemma or group: `(=> (fuel_bool fuel%f) ...)`.
fn fuel_guard(expr: &Expr) -> Option<Ident> {
    let ExprX::Binary(BinaryOp::Implies, guard, _) = &**expr else { return None };
    let ExprX::Apply(f, args) = &**guard else { return None };
    match &args[..] {
        [arg] if f.as_str() == vir::def::FUEL_BOOL => match &**arg {
            ExprX::Var(x) => Some(x.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// Whether the query's body assumes `(fuel_bool ident)`, as a `reveal` or
/// `broadcast use` in it does.
fn body_reveals(query: &Query, ident: &Ident) -> bool {
    fn any_assume(stmt: &air::ast::Stmt, wanted: &dyn Fn(&Expr) -> bool) -> bool {
        match &**stmt {
            air::ast::StmtX::Assume(e) => wanted(e),
            air::ast::StmtX::Block(stmts) | air::ast::StmtX::Switch(stmts) => {
                stmts.iter().any(|s| any_assume(s, wanted))
            }
            air::ast::StmtX::DeadEnd(s) | air::ast::StmtX::Breakable(_, s) => any_assume(s, wanted),
            _ => false,
        }
    }
    any_assume(&query.assertion, &|e| match &**e {
        ExprX::Apply(f, args) => {
            f.as_str() == vir::def::FUEL_BOOL && args.len() == 1 && is_var(&args[0], ident)
        }
        _ => false,
    })
}

/// Whether the query's fuel hypothesis hides the function with fuel
/// constant `ident`.
fn query_hides(query: &Query, ident: &Ident) -> bool {
    query.local.iter().any(|decl| match &**decl {
        DeclX::Axiom(axiom) if matches!(axiom.tag, Some(air::def::ProvenanceTag::Hyp(_))) => {
            matches!(fuel_hypothesis(&axiom.expr), Some(Some((_, hidden))) if hidden.iter().any(|h| is_var(h, ident)))
        }
        _ => false,
    })
}

fn named_by(axiom: &Axiom, names: &[String]) -> bool {
    names.iter().any(|name| air::twin::axiom_named(axiom, name))
}

fn matched(
    place: &'static str,
    axiom: &AxiomRef,
    fun: &Fun,
    symbols: Option<&Symbols>,
) -> MatchedAxiom {
    MatchedAxiom {
        place,
        tag: axiom.tag.as_ref().map(|tag| match symbols {
            Some(symbols) => symbols.tag_of(fun, &tag.to_symbol()),
            None => {
                ResolvedTag { tag: tag.to_symbol(), kind: String::new(), owner: None, span: None }
            }
        }),
        qid: axiom.qid.as_ref().map(|qid| qid.to_string()),
    }
}

fn empty_report(kind: &'static str) -> EditReport {
    EditReport {
        kind,
        axioms: Vec::new(),
        expression: None,
        fuel_assumed: None,
        fuel: None,
        rlimit: None,
        order: Vec::new(),
        rebuilt_scopes: None,
    }
}

/// Apply `edit` to the query retained at `prefix` of `journal`, without
/// touching the solver. `Err` is a refusal to report.
fn plan(
    edit: &TwinEdit,
    journal: &QueryJournal,
    prefix: usize,
    query: &Query,
    rlimit: f32,
    fun: &Fun,
    symbols: Option<&Symbols>,
) -> Result<Plan, String> {
    match edit {
        TwinEdit::RemoveAxiom(name) => {
            let names = names_for(name, symbols)?;
            let mut twin = query.clone();
            let mut report = empty_report("remove_axiom");
            for name in &names {
                let (next, removed) = air::twin::remove_local_axioms(&twin, name);
                twin = next;
                report.axioms.extend(removed.iter().map(|a| matched("query", a, fun, symbols)));
            }
            let in_prefix: Vec<(usize, AxiomRef)> = prefix_axioms(journal, 0..prefix)
                .filter(|(_, axiom)| named_by(axiom, &names))
                .map(|(scope, axiom)| (scope, AxiomRef::of(axiom)))
                .collect();
            report.axioms.extend(in_prefix.iter().map(|(_, a)| matched("prefix", a, fun, symbols)));
            if report.axioms.is_empty() {
                // Below every scope, so it cannot be rebuilt away. An axiom
                // guarded by a function's fuel, as a broadcast lemma's or
                // group's is, can be hidden instead.
                let in_base: Vec<&Axiom> =
                    base_axioms(journal).filter(|a| named_by(a, &names)).collect();
                if in_base.is_empty() {
                    // The prelude is asserted before the bucket's context and
                    // is not journaled at all.
                    if name.trim().trim_matches('|').starts_with("prelude_") {
                        return Err(format!(
                            "{name} is a prelude axiom, asserted before the bucket's context and below every scope; a twin cannot remove it"
                        ));
                    }
                    return Err(format!(
                        "nothing in this query's context is named {name}: name a hypothesis tag (hyp_<k>), an axiom tag (ax_...), a quantifier qid, or the function that states a broadcast axiom"
                    ));
                }
                let guards: BTreeSet<Ident> =
                    in_base.iter().filter_map(|a| fuel_guard(&a.expr)).collect();
                let (Some(guard), true) = (guards.iter().next(), guards.len() == 1) else {
                    return Err(format!(
                        "{name} is in the bucket's base context (every declaration made before the bucket's first query), below every scope the worker can rebuild, and no function's fuel guards it; only a broadcast lemma's axiom there can be hidden"
                    ));
                };
                let Some(target) = FuelScan::of(journal, prefix).target(guard) else {
                    return Err(format!(
                        "{name} is guarded by {guard}, which this query's context does not declare"
                    ));
                };
                let (twin, fuel) = flip_fuel(query, &target, 0)?;
                report.axioms.extend(
                    in_base.iter().map(|a| matched("base", &AxiomRef::of(a), fun, symbols)),
                );
                report.fuel = Some(fuel);
                return Ok(Plan { query: twin, rlimit, rebuild: None, report, vacuity: false });
            }
            let rebuild = in_prefix.iter().map(|(scope, _)| *scope).min().map(|first| {
                report.rebuilt_scopes = Some(prefix - first);
                (first, names)
            });
            Ok(Plan { query: twin, rlimit, rebuild, report, vacuity: false })
        }
        TwinEdit::AddAxiom(text) => {
            let mut report = empty_report("add_axiom");
            let mut twin = query.clone();
            if text.trim_start().starts_with('(') {
                report.expression = Some(text.clone());
                let axiom = air::twin::parse_axiom(Arc::new(VirMessageInterface {}), text)?;
                twin = air::twin::with_local_axiom(&twin, axiom);
                return Ok(Plan { query: twin, rlimit, rebuild: None, report, vacuity: true });
            }
            let names = names_for(text, symbols)?;
            let in_base = base_axioms(journal).find(|a| named_by(a, &names)).map(|a| ("base", a));
            let found = in_base
                .or_else(|| {
                    prefix_axioms(journal, 0..prefix)
                        .find(|(_, a)| named_by(a, &names))
                        .map(|(_, a)| ("prefix", a))
                })
                .or_else(|| {
                    prefix_axioms(journal, prefix..journal.contexts.len())
                        .find(|(_, a)| named_by(a, &names))
                        .map(|(_, a)| ("retained", a))
                });
            let Some((place, found)) = found else {
                return Err(format!(
                    "no axiom of this bucket is named {text}; give an AIR expression in parentheses, or the tag, qid or function of a broadcast lemma or group"
                ));
            };
            // The axiom of a broadcast lemma or group is guarded by its
            // fuel, which the query assumes only where it `broadcast use`s
            // it. Adding the axiom means assuming that, as the source edit
            // would.
            let guard = fuel_guard(&found.expr);
            let assumed = guard.as_ref().and_then(|c| {
                if body_reveals(query, c) {
                    Some("the body already reveals it")
                } else if FuelScan::of(journal, prefix).default_visible(c) && !query_hides(query, c)
                {
                    Some("its module reveals it by default")
                } else {
                    None
                }
            });
            match (place, &guard, assumed) {
                ("retained", _, _) => {
                    report.axioms.push(matched(place, &AxiomRef::of(found), fun, symbols));
                    let axiom = Axiom {
                        named: found.named.clone(),
                        tag: found.tag.clone(),
                        expr: found.expr.clone(),
                    };
                    twin = air::twin::with_local_axiom(&twin, axiom);
                }
                (_, None, _) => {
                    return Err(format!("{text} is already in this query's context"));
                }
                (_, Some(_), Some(why)) => {
                    return Err(format!(
                        "{text} already applies to this query: its axiom is in the context and {why}"
                    ));
                }
                (_, Some(_), None) => {
                    report.axioms.push(matched(place, &AxiomRef::of(found), fun, symbols));
                }
            }
            if let (Some(c), None) = (&guard, assumed) {
                let revealed = air::ast_util::str_apply(
                    vir::def::FUEL_BOOL,
                    &vec![air::ast_util::ident_var(c)],
                );
                let tag = Some(air::def::ProvenanceTag::Axiom(Arc::new(TWIN_FUEL_TAG.to_owned())));
                twin =
                    air::twin::with_local_axiom(&twin, Axiom { named: None, tag, expr: revealed });
                report.fuel_assumed = Some(fuel_path(c));
            }
            Ok(Plan { query: twin, rlimit, rebuild: None, report, vacuity: true })
        }
        TwinEdit::BumpRlimit(twin_rlimit) => {
            if !rlimit.is_finite() {
                return Err("this query has no resource limit to raise".to_owned());
            }
            if !twin_rlimit.is_finite() || *twin_rlimit <= 0.0 {
                return Err("bump_rlimit must be a positive number".to_owned());
            }
            if *twin_rlimit > rlimit * MAX_RLIMIT_FACTOR {
                return Err(format!(
                    "bump_rlimit may be at most {MAX_RLIMIT_FACTOR} times the query's rlimit ({rlimit})"
                ));
            }
            let mut report = empty_report("bump_rlimit");
            report.rlimit = Some(Pair { base: rlimit, twin: *twin_rlimit });
            Ok(Plan {
                query: query.clone(),
                rlimit: *twin_rlimit,
                rebuild: None,
                report,
                vacuity: false,
            })
        }
        TwinEdit::ReorderAsserts(names) => {
            let ids: Option<Vec<AssertId>> = names.iter().map(AssertName::id).collect();
            let Some(ids) = ids else {
                return Err(
                    "name each assertion by its assert_id, such as [3, 1] or \"3.1\"".to_owned()
                );
            };
            let twin = air::twin::reorder_asserts(query, &ids)?;
            let mut report = empty_report("reorder_asserts");
            report.order = ids.iter().map(air::twin::assert_id_text).collect();
            Ok(Plan { query: twin, rlimit, rebuild: None, report, vacuity: false })
        }
        TwinEdit::FlipFuel { function, fuel } => {
            let target = FuelScan::of(journal, prefix).find(function)?;
            let (twin, fuel_report) = flip_fuel(query, &target, *fuel)?;
            if *fuel == 1
                && fuel_report.default_visible
                && !fuel_report.hidden_before
                && fuel_report.reveals_removed == 0
            {
                return Err(format!(
                    "{} is already visible in this query, so fuel 1 changes nothing; 0 hides it, and 2 or more unrolls a recursive function further",
                    target.name
                ));
            }
            let mut report = empty_report("flip_fuel");
            report.fuel = Some(fuel_report);
            Ok(Plan { query: twin, rlimit, rebuild: None, report, vacuity: false })
        }
    }
}

/// A function with fuel in a query's context: its fuel constant, and for a
/// recursive one the constant that counts its unrollings.
#[derive(Debug)]
struct FuelTarget {
    ident: Ident,
    fuel_nat: Option<Ident>,
    /// The function's path, read back from the constant's name.
    name: String,
    default_visible: bool,
}

/// `toydb!encoding.decode.?` -> `toydb::encoding::decode`.
fn friendly_path(ident: &str) -> String {
    let ident = ident.trim_end_matches('?').trim_end_matches('.');
    ident.replace(['!', '.'], "::")
}

/// `fuel%crate!f.` -> `crate::f`.
fn fuel_path(ident: &Ident) -> String {
    let fuel_prefix = vir::def::prefix_fuel_id(&Arc::new(String::new()));
    friendly_path(ident.strip_prefix(fuel_prefix.as_str()).unwrap_or(ident))
}

/// The fuel declarations of a query's context: every function's fuel
/// constant, the unrolling constant of each recursive one, and the fuel
/// constants its module reveals by default.
struct FuelScan {
    /// Each fuel constant with the function's path.
    constants: Vec<(Ident, String)>,
    nats: HashSet<Ident>,
    defaults: HashSet<Ident>,
}

impl FuelScan {
    fn of(journal: &QueryJournal, prefix: usize) -> Self {
        let fuel_prefix = vir::def::prefix_fuel_id(&Arc::new(String::new()));
        let mut scan =
            FuelScan { constants: Vec::new(), nats: HashSet::new(), defaults: HashSet::new() };
        // `(=> (fuel_bool_default group) (and (fuel_bool_default member) ...))`
        // reveals the members with the group.
        let mut implied: Vec<(Ident, Vec<Ident>)> = Vec::new();
        // fuel constants are declared in the base context, below every scope
        for batch in journal.base.iter().chain(journal.contexts[..prefix].iter().flatten()) {
            for command in batch.iter() {
                let CommandX::Global(decl) = &**command else { continue };
                match &**decl {
                    DeclX::Const(x, typ) => match &**typ {
                        TypX::Named(t) if t.as_str() == vir::def::FUEL_ID => {
                            if let Some(rest) = x.strip_prefix(fuel_prefix.as_str()) {
                                scan.constants.push((x.clone(), friendly_path(rest)));
                            }
                        }
                        TypX::Named(t) if t.as_str() == vir::def::FUEL_TYPE => {
                            scan.nats.insert(x.clone());
                        }
                        _ => {}
                    },
                    DeclX::Axiom(axiom) => match &*axiom.expr {
                        ExprX::Binary(BinaryOp::Implies, guard, members) => {
                            if let Some(group) = fuel_default_of(guard) {
                                implied.push((group, fuel_defaults_in(members)));
                            }
                        }
                        _ => scan.defaults.extend(fuel_defaults_in(&axiom.expr)),
                    },
                    _ => {}
                }
            }
        }
        let mut grew = true;
        while grew {
            grew = false;
            for (group, members) in &implied {
                if scan.defaults.contains(group) {
                    for member in members {
                        grew |= scan.defaults.insert(member.clone());
                    }
                }
            }
        }
        scan
    }

    fn default_visible(&self, ident: &Ident) -> bool {
        self.defaults.contains(ident)
    }

    /// The function with fuel constant `ident`.
    fn target(&self, ident: &Ident) -> Option<FuelTarget> {
        let nat_prefix = vir::def::prefix_fuel_nat(&Arc::new(String::new()));
        let fuel_prefix = vir::def::prefix_fuel_id(&Arc::new(String::new()));
        let (ident, name) = self.constants.iter().find(|(x, _)| x == ident)?;
        let rest = ident.strip_prefix(fuel_prefix.as_str()).unwrap_or(ident);
        let nat = Arc::new(format!("{nat_prefix}{rest}"));
        Some(FuelTarget {
            fuel_nat: self.nats.contains(&nat).then_some(nat),
            default_visible: self.default_visible(ident),
            ident: ident.clone(),
            name: name.clone(),
        })
    }

    /// The one function `function` names: by its whole path (with or
    /// without `crate::`) or fuel constant, else by path suffix, which a
    /// bare name shared by several functions fails.
    fn find(&self, function: &str) -> Result<FuelTarget, String> {
        let fuel_prefix = vir::def::prefix_fuel_id(&Arc::new(String::new()));
        let given = function.trim();
        let bare = given.strip_prefix("crate::").unwrap_or(given);
        let whole = format!("crate::{bare}");
        let suffix = format!("::{bare}");
        let exact: Vec<&(Ident, String)> = self
            .constants
            .iter()
            .filter(|(ident, name)| {
                name == given
                    || name == bare
                    || *name == whole
                    || ident.as_str() == given
                    || ident.strip_prefix(fuel_prefix.as_str()) == Some(given)
            })
            .collect();
        let found = if exact.is_empty() {
            self.constants.iter().filter(|(_, name)| name.ends_with(&suffix)).collect()
        } else {
            exact
        };
        match &found[..] {
            [(ident, _)] => Ok(self.target(ident).expect("a scanned constant")),
            [] => Err(format!(
                "no function named {function} has fuel in this query's context (spec functions with bodies and broadcast lemmas do)"
            )),
            many => {
                let names: Vec<&str> =
                    many.iter().take(10).map(|(_, name)| name.as_str()).collect();
                Err(format!("{function} names {} functions: {}", many.len(), names.join(", ")))
            }
        }
    }
}

/// `(fuel_bool_default fuel%f)` -> `fuel%f`.
fn fuel_default_of(expr: &Expr) -> Option<Ident> {
    let ExprX::Apply(f, args) = &**expr else { return None };
    match &args[..] {
        [arg] if f.as_str() == vir::def::FUEL_BOOL_DEFAULT => match &**arg {
            ExprX::Var(x) => Some(x.clone()),
            _ => None,
        },
        _ => None,
    }
}

/// The fuel constants `expr` reveals by default: one `fuel_bool_default`
/// application, or a conjunction of them as a module-level `broadcast use`
/// makes.
fn fuel_defaults_in(expr: &Expr) -> Vec<Ident> {
    match &**expr {
        ExprX::Multi(MultiOp::And, exprs) => exprs.iter().filter_map(fuel_default_of).collect(),
        _ => fuel_default_of(expr).into_iter().collect(),
    }
}

/// Whether `expr` is the fuel hypothesis of a query: `fuel_defaults`, or
/// `(forall ((id FuelId)) (or (= (fuel_bool id) (fuel_bool_default id)) (= id
/// fuel%h) ...))` for a query that hides some functions. Returns the bound
/// variable and the hidden functions' constants for the second shape.
fn fuel_hypothesis(expr: &Expr) -> Option<Option<(Ident, Vec<Expr>)>> {
    match &**expr {
        ExprX::Var(x) if x.as_str() == vir::def::FUEL_DEFAULTS => Some(None),
        ExprX::Bind(bind, body) => {
            let BindX::Quant(Quant::Forall, binders, _, _) = &**bind else { return None };
            let [binder] = &binders[..] else { return None };
            if !matches!(&*binder.a, TypX::Named(t) if t.as_str() == vir::def::FUEL_ID) {
                return None;
            }
            let ExprX::Multi(MultiOp::Or, disjuncts) = &**body else { return None };
            let (first, rest) = disjuncts.split_first()?;
            match &**first {
                ExprX::Binary(BinaryOp::Eq, lhs, _) if matches!(&**lhs, ExprX::Apply(f, _) if f.as_str() == vir::def::FUEL_BOOL) =>
                    {}
                _ => return None,
            }
            let hidden = rest
                .iter()
                .filter_map(|d| match &**d {
                    ExprX::Binary(BinaryOp::Eq, _, h) => Some(h.clone()),
                    _ => None,
                })
                .collect();
            Some(Some((binder.name.clone(), hidden)))
        }
        _ => None,
    }
}

fn is_var(expr: &Expr, name: &Ident) -> bool {
    matches!(&**expr, ExprX::Var(x) if x == name)
}

/// `query` with `target` given `fuel` for its whole body, as a
/// `reveal_with_fuel` at the top of it would (0: hidden).
fn flip_fuel(query: &Query, target: &FuelTarget, fuel: u32) -> Result<(Query, FuelReport), String> {
    use air::ast_util::{ident_var, mk_eq, str_apply, str_var};
    if fuel >= 2 && target.fuel_nat.is_none() {
        return Err(format!("{} is not recursive: any fuel above 1 is the same as 1", target.name));
    }
    // The body's own reveals of the function go, so that the edit decides.
    let reveal = |e: &Expr| match &**e {
        ExprX::Apply(f, args) => {
            f.as_str() == vir::def::FUEL_BOOL && args.len() == 1 && is_var(&args[0], &target.ident)
        }
        ExprX::Bind(bind, body) => {
            matches!(&**bind, BindX::Quant(Quant::Exists, ..))
                && matches!(&**body, ExprX::Binary(BinaryOp::Eq, lhs, _)
                    if target.fuel_nat.as_ref().is_some_and(|nat| is_var(lhs, nat)))
        }
        _ => false,
    };
    let (assertion, reveals_removed) = air::twin::remove_assumes(&query.assertion, &reveal);
    let query = Arc::new(air::ast::QueryX { local: query.local.clone(), assertion });
    let mut hidden_before = false;
    let mut found = false;
    let (query, _) = air::twin::replace_local_axioms(&query, &mut |axiom: &Axiom| {
        if found || !matches!(axiom.tag, Some(air::def::ProvenanceTag::Hyp(_))) {
            return None;
        }
        let shape = fuel_hypothesis(&axiom.expr)?;
        found = true;
        let (id, mut hidden) = match shape {
            None => (Arc::new("id".to_owned()), Vec::new()),
            Some((id, hidden)) => (id, hidden),
        };
        hidden_before = hidden.iter().any(|h| is_var(h, &target.ident));
        if fuel > 0 || hidden_before {
            return None;
        }
        hidden.push(ident_var(&target.ident));
        let x_id = ident_var(&id);
        let fuel_bool = str_apply(vir::def::FUEL_BOOL, &vec![x_id.clone()]);
        let mut disjuncts =
            vec![mk_eq(&fuel_bool, &str_apply(vir::def::FUEL_BOOL_DEFAULT, &vec![x_id.clone()]))];
        disjuncts.extend(hidden.iter().map(|h| mk_eq(&x_id, h)));
        // A query that hid nothing asserted `fuel_defaults`, whose
        // quantifier is the prelude's; the replacement gets a name of its own,
        // so the instantiation delta shows the one stop and the other start.
        let qid = match &*axiom.expr {
            ExprX::Bind(bind, _) => match &**bind {
                BindX::Quant(_, _, _, qid) => qid.clone(),
                _ => None,
            },
            _ => None,
        }
        .or_else(|| Some(Arc::new(TWIN_FUEL_QID.to_owned())));
        let binders = Arc::new(vec![Arc::new(BinderX {
            name: id,
            a: Arc::new(TypX::Named(Arc::new(vir::def::FUEL_ID.to_owned()))),
        })]);
        let triggers = Arc::new(vec![Arc::new(vec![fuel_bool])]);
        let bind = Arc::new(BindX::Quant(Quant::Forall, binders, triggers, qid));
        let body = Arc::new(ExprX::Multi(MultiOp::Or, Arc::new(disjuncts)));
        Some(Axiom {
            named: axiom.named.clone(),
            tag: axiom.tag.clone(),
            expr: Arc::new(ExprX::Bind(bind, body)),
        })
    });
    if fuel == 0 && !found {
        return Err("this query has no fuel hypothesis to hide the function in".to_owned());
    }
    let mut query = query;
    let tag = || Some(air::def::ProvenanceTag::Axiom(Arc::new(TWIN_FUEL_TAG.to_owned())));
    if fuel >= 1 {
        let revealed = str_apply(vir::def::FUEL_BOOL, &vec![ident_var(&target.ident)]);
        query =
            air::twin::with_local_axiom(&query, Axiom { named: None, tag: tag(), expr: revealed });
    }
    if fuel >= 2 {
        let nat = target.fuel_nat.as_ref().expect("checked above");
        let mut added = str_var(vir::def::FUEL_PARAM);
        for _ in 0..fuel - 1 {
            added = str_apply(vir::def::SUCC, &vec![added]);
        }
        let binder = air::ast_util::ident_binder(
            &Arc::new(vir::def::FUEL_PARAM.to_owned()),
            &Arc::new(TypX::Named(Arc::new(vir::def::FUEL_TYPE.to_owned()))),
        );
        let unrolled =
            air::ast_util::mk_exists(&vec![binder], &vec![], None, &mk_eq(&ident_var(nat), &added));
        query =
            air::twin::with_local_axiom(&query, Axiom { named: None, tag: tag(), expr: unrolled });
    }
    Ok((
        query,
        FuelReport {
            function: target.name.clone(),
            fuel,
            recursive: target.fuel_nat.is_some(),
            default_visible: target.default_visible,
            hidden_before,
            reveals_removed,
        },
    ))
}

/// Run `check` on `prefix` rebuilt without the axioms `names` select, from
/// scope `first` on. The rebuilt scopes are popped before this returns, and
/// the journal is left at `first`, so the next restore replays the prefix
/// as recorded. `Ok(Err(_))`: the rebuild was refused by AIR, and nothing of
/// it is left open.
fn with_rebuilt_prefix<T>(
    journal: &mut QueryJournal,
    air: &mut Context,
    prefix: usize,
    first: usize,
    names: &[String],
    check: impl FnOnce(&mut Context) -> T,
) -> io::Result<Result<T, String>> {
    journal.restore_prefix(air, first)?;
    let mut pushed = 0;
    let mut rebuild = || -> Result<(), String> {
        for scope in first..prefix {
            air.push();
            pushed += 1;
            for batch in journal.contexts[scope].iter() {
                for command in batch.iter() {
                    let CommandX::Global(decl) = &**command else { continue };
                    if let DeclX::Axiom(axiom) = &**decl {
                        if named_by(axiom, names) {
                            continue;
                        }
                    }
                    air.global(decl).map_err(|error| error.to_string())?;
                }
            }
        }
        Ok(())
    };
    let rebuilt = rebuild();
    let result = match rebuilt {
        Ok(()) => {
            let output = air.flush_commands();
            if !output.is_empty() {
                for _ in 0..pushed {
                    air.pop();
                }
                return Err(io::Error::other(format!(
                    "solver rejected the rebuilt context: {}",
                    output.join(" ")
                )));
            }
            Ok(check(air))
        }
        Err(error) => Err(format!("the context without the axiom does not type-check: {error}")),
    };
    for _ in 0..pushed {
        air.pop();
    }
    Ok(result)
}

/// Serve a twin request for one query of `bucket`, whose address the caller
/// has checked. `Ok(Err(_))` is a refusal to report; `Err` ends the session.
pub(super) fn serve(
    bucket: &RetainedBucket,
    id: QueryId,
    request: TwinRequest,
    set_rlimit: &impl Fn(&mut Context, f32),
) -> io::Result<Result<TwinReport, String>> {
    let mut state =
        bucket.state.lock().map_err(|_| io::Error::other("resident bucket poisoned"))?;
    let (solver, local) = bucket.addresses[id.0];
    let SolverState { air, journal } = &mut state[solver];
    if !matches!(air.get_solver(), SmtSolver::Cvc5) {
        return Ok(Err("counterfactual twins need cvc5".to_owned()));
    }
    let retained = &journal.queries[local];
    let (base_query, rlimit, prefix, fun) =
        (retained.query.clone(), retained.rlimit, retained.prefix, retained.context.fun.clone());
    let symbols = bucket.symbols.as_ref();
    let plan = match plan(&request.edit, journal, prefix, &base_query, rlimit, &fun, symbols) {
        Ok(plan) => plan,
        Err(message) => return Ok(Err(message)),
    };
    let restore_start = Instant::now();
    journal.restore_prefix(air, prefix)?;
    let restore_ms = restore_start.elapsed().as_millis();
    let levels_before = air.assertion_stack_levels();
    let start = Instant::now();
    let base = match run_branch(air, &base_query, rlimit, set_rlimit) {
        Ok(branch) => branch,
        Err(BranchError::Refused(message)) => return Ok(Err(message)),
        Err(BranchError::Fatal(error)) => return Err(error),
    };
    let twin = match &plan.rebuild {
        None => run_branch(air, &plan.query, plan.rlimit, set_rlimit),
        Some((first, names)) => {
            let outcome = with_rebuilt_prefix(journal, air, prefix, *first, names, |air| {
                run_branch(air, &plan.query, plan.rlimit, set_rlimit)
            })?;
            // Back to the recorded prefix before anything else is checked.
            journal.restore_prefix(air, prefix)?;
            match outcome {
                Ok(twin) => twin,
                Err(message) => return Ok(Err(message)),
            }
        }
    };
    let twin = match twin {
        Ok(branch) => branch,
        Err(BranchError::Refused(message)) => return Ok(Err(message)),
        Err(BranchError::Fatal(error)) => return Err(error),
    };
    let vacuity = if plan.vacuity {
        // Each query with every goal switched off: valid only by contradiction.
        let mut falsified = |query: &Query| -> io::Result<Result<&'static str, String>> {
            match run_branch(air, &air::twin::goals_off(query), rlimit, set_rlimit) {
                Ok(branch) => Ok(Ok(branch.class())),
                Err(BranchError::Refused(message)) => Ok(Err(message)),
                Err(BranchError::Fatal(error)) => Err(error),
            }
        };
        let base_goals_off = match falsified(&base_query)? {
            Ok(class) => class,
            Err(message) => return Ok(Err(message)),
        };
        let twin_goals_off = match falsified(&plan.query)? {
            Ok(class) => class,
            Err(message) => return Ok(Err(message)),
        };
        let (base_total, twin_total) =
            (base.counts().total().unwrap_or(0), twin.counts().total().unwrap_or(0));
        let inconsistent = twin_goals_off == "valid" && base_goals_off != "valid";
        let instantiation_collapse = base_total > 0 && twin_total * 10 <= base_total;
        let flipped_to_valid = twin.class() == "valid" && base.class() != "valid";
        Some(Vacuity {
            base_goals_off,
            twin_goals_off,
            inconsistent,
            instantiation_collapse,
            possibly_vacuous: flipped_to_valid && (inconsistent || instantiation_collapse),
        })
    } else {
        None
    };
    let recheck = if request.recheck_base {
        match run_branch(air, &base_query, rlimit, set_rlimit) {
            Ok(again) => {
                let same_instantiations =
                    air::twin::diff_instantiations(&base.counts(), &again.counts())
                        .is_some_and(|delta| delta.quantifiers.iter().all(|q| q.delta() == 0));
                Some(Recheck {
                    result: again.result,
                    class: again.class(),
                    same_result: again.class() == base.class(),
                    same_instantiations,
                    instantiations: again.counts().total(),
                    resource_units: again.resource_units(),
                    elapsed_ms: again.elapsed_ms,
                })
            }
            Err(BranchError::Refused(message)) => return Ok(Err(message)),
            Err(BranchError::Fatal(error)) => return Err(error),
        }
    } else {
        None
    };
    let levels_after = air.assertion_stack_levels();
    let elapsed_ms = start.elapsed().as_millis();

    let mut unavailable = Vec::new();
    let inst_count_delta =
        air::twin::diff_instantiations(&base.counts(), &twin.counts()).map(|delta| {
            if !delta.by_inference {
                unavailable.push(
                    "inst_count_delta.by_inference: this cvc5 has no (get-info :branch-profile)"
                        .to_owned(),
                );
            }
            report_instantiations(&delta, symbols, request.limit)
        });
    if inst_count_delta.is_none() {
        unavailable
            .push("inst_count_delta: the solver reported no instantiation counters".to_owned());
    }
    let difficulty = match (&base.difficulty, &twin.difficulty) {
        (Some(b), Some(t)) => air::twin::diff_difficulty(b, t),
        _ => None,
    };
    if difficulty.is_none() {
        unavailable.push(if air.difficulty() {
            "difficulty_delta, did_relevant_delta: cvc5 reported no difficulty for one of the checks".to_owned()
        } else {
            "difficulty_delta, did_relevant_delta: open the session with difficulty to compare them".to_owned()
        });
    }
    let resolve = |tags: &[String]| -> Vec<ResolvedTag> {
        tags.iter()
            .map(|tag| match symbols {
                Some(symbols) => symbols.tag_of(&fun, tag),
                None => {
                    ResolvedTag { tag: tag.clone(), kind: String::new(), owner: None, span: None }
                }
            })
            .collect()
    };
    let (difficulty_delta, did_relevant_delta) = match &difficulty {
        Some(delta) => {
            let row = |r: &air::twin::TagDelta| TagDeltaReport {
                tags: resolve(&r.tags),
                base: r.base,
                twin: r.twin,
                delta: r.delta(),
                base_in_core: r.base_in_core,
                twin_in_core: r.twin_in_core,
            };
            let changed: Vec<&air::twin::TagDelta> =
                delta.rows.iter().filter(|r| r.delta() != 0).collect();
            let rows: Vec<TagDeltaReport> =
                changed.iter().take(request.limit).map(|r| row(r)).collect();
            let relevance = air::twin::relevance_delta(delta);
            let mut omitted = 0;
            let mut list = |indices: &[usize]| -> Vec<Vec<ResolvedTag>> {
                let mut out: Vec<Vec<ResolvedTag>> = Vec::new();
                for &i in indices {
                    let tags = resolve(&delta.rows[i].tags);
                    if out.len() >= request.limit || tags.iter().all(|t| t.kind == "prelude") {
                        omitted += 1;
                    } else {
                        out.push(tags);
                    }
                }
                out
            };
            let became_relevant = list(&relevance.became_relevant);
            let became_irrelevant = list(&relevance.became_irrelevant);
            (
                Some(DifficultyDeltaReport {
                    hardest_assertion: delta.hardest.map(|i| row(&delta.rows[i])),
                    total: Pair { base: delta.base_total, twin: delta.twin_total },
                    omitted: changed.len().saturating_sub(rows.len()),
                    rows,
                }),
                Some(RelevanceReport {
                    basis: relevance.basis,
                    became_relevant,
                    became_irrelevant,
                    omitted,
                }),
            )
        }
        None => (None, None),
    };
    Ok(Ok(TwinReport {
        edit: plan.report,
        outcome_flip: OutcomeFlip {
            base: base.class(),
            twin: twin.class(),
            flipped: base.class() != twin.class(),
        },
        base: base.report(),
        twin: twin.report(),
        inst_count_delta,
        difficulty_delta,
        did_relevant_delta,
        vacuity,
        integrity: SessionCheck {
            intact: levels_before.is_some() && levels_before == levels_after,
            stack_levels_before: levels_before,
            stack_levels_after: levels_after,
            recheck,
        },
        unavailable,
        caveat: CAVEAT,
        elapsed_ms,
        restore_ms,
    }))
}

fn report_instantiations(
    delta: &air::twin::InstDelta,
    symbols: Option<&Symbols>,
    limit: usize,
) -> InstCountDelta {
    let mut changed: Vec<&air::twin::QuantDelta> =
        delta.quantifiers.iter().filter(|q| q.delta() != 0).collect();
    // The prelude's boxing axioms ride every user quantifier's instances and
    // tie with it; on a tie the user's comes first (stable: the rest keep
    // `air::twin`'s order).
    let prelude = |q: &air::twin::QuantDelta| q.qid.starts_with("prelude_");
    changed.sort_by(|a, b| b.delta().abs().cmp(&a.delta().abs()).then(prelude(a).cmp(&prelude(b))));
    let moved: u64 = changed.iter().map(|q| q.delta().unsigned_abs()).sum();
    let top_share = changed.first().filter(|_| moved > 0).map(|q| {
        let share = q.delta().unsigned_abs() as f64 / moved as f64;
        (share * 1000.0).round() / 1000.0
    });
    let only = |pick: fn(&air::twin::QuantDelta) -> bool| -> Vec<String> {
        delta.quantifiers.iter().filter(|q| pick(q)).take(limit).map(|q| q.qid.clone()).collect()
    };
    let by_quantifier = changed
        .iter()
        .take(limit)
        .map(|q| {
            let (fun, span) = match symbols.and_then(|s| s.quantifier_site(&q.qid)) {
                Some((fun, span)) => (Some(fun.to_owned()), span.map(str::to_owned)),
                None if q.qid.starts_with("prelude_") => (Some("prelude".to_owned()), None),
                None => (None, None),
            };
            QuantDeltaReport {
                qid: q.qid.clone(),
                fun,
                span,
                role: symbols.and_then(|s| s.quantifier_role(&q.qid)),
                base: q.base,
                twin: q.twin,
                delta: q.delta(),
                duplicates: Pair { base: q.base_duplicates, twin: q.twin_duplicates },
                by_inference: q
                    .inferences
                    .iter()
                    .filter(|i| i.base != i.twin)
                    .map(|i| InferenceReport {
                        inference: i.inference.clone(),
                        base: i.base,
                        twin: i.twin,
                        delta: i.twin as i64 - i.base as i64,
                    })
                    .collect(),
            }
        })
        .collect::<Vec<_>>();
    InstCountDelta {
        total: delta.twin_total as i64 - delta.base_total as i64,
        base_total: delta.base_total,
        twin_total: delta.twin_total,
        rounds: Pair { base: delta.base_rounds, twin: delta.twin_rounds },
        by_inference: delta.by_inference,
        changed: changed.len(),
        started: only(|q| q.base == 0 && q.twin > 0),
        stopped: only(|q| q.base > 0 && q.twin == 0),
        top_share,
        omitted: changed.len().saturating_sub(by_quantifier.len()),
        by_quantifier,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn query(text: &str) -> Query {
        let node = sise::parse_tree(&mut sise::Parser::new(text)).unwrap();
        let commands = air::parser::Parser::new(Arc::new(VirMessageInterface {}))
            .nodes_to_commands(&[node])
            .unwrap();
        match &*commands[0] {
            CommandX::CheckValid(q) => q.clone(),
            _ => panic!("expected check-valid"),
        }
    }

    fn target(recursive: bool) -> FuelTarget {
        FuelTarget {
            ident: Arc::new("fuel%crate!f.".to_owned()),
            fuel_nat: recursive.then(|| Arc::new("fuel_nat%crate!f.".to_owned())),
            name: "crate::f".to_owned(),
            default_visible: true,
        }
    }

    const QUERY: &str = "(check-valid
        (axiom fuel_defaults)
        (block
          (assume (fuel_bool fuel%crate!f.))
          (assume (exists ((fuel% Fuel)) (= fuel_nat%crate!f. (succ (succ fuel%)))))
          (assert true)))";

    #[test]
    fn fuel_zero_hides_the_function_and_drops_its_reveals() {
        let q = query(QUERY);
        // the parser leaves the hypothesis untagged; tag it as Verus does
        let (q, _) = air::twin::replace_local_axioms(&q, &mut |a: &Axiom| {
            Some(Axiom {
                named: None,
                tag: Some(air::def::ProvenanceTag::Hyp(air::def::HypId(0))),
                expr: a.expr.clone(),
            })
        });
        let (twin, report) = flip_fuel(&q, &target(true), 0).unwrap();
        assert_eq!(report.reveals_removed, 2);
        assert!(!report.hidden_before);
        let DeclX::Axiom(hyp) = &*twin.local[0] else { panic!() };
        let Some(Some((_, hidden))) = fuel_hypothesis(&hyp.expr) else { panic!("{:?}", hyp.expr) };
        assert_eq!(hidden.len(), 1);
        assert!(is_var(&hidden[0], &target(true).ident));
        // hiding it again changes nothing more
        let (again, report) = flip_fuel(&twin, &target(true), 0).unwrap();
        assert!(report.hidden_before);
        assert_eq!(again.local.len(), twin.local.len());
    }

    #[test]
    fn fuel_above_one_unrolls_a_recursive_function() {
        let q = query(QUERY);
        let (twin, report) = flip_fuel(&q, &target(true), 3).unwrap();
        assert_eq!(report.reveals_removed, 2);
        // the hypothesis, the reveal, and the unrolling
        assert_eq!(twin.local.len(), 3);
        let DeclX::Axiom(unroll) = &*twin.local[2] else { panic!() };
        let text = format!("{:?}", unroll.expr);
        assert_eq!(text.matches("succ").count(), 2, "{}", text);
        assert!(flip_fuel(&q, &target(false), 2).is_err());
        assert!(flip_fuel(&q, &target(false), 1).is_ok());
    }

    fn journal_with_base(text: &str) -> QueryJournal {
        let node = sise::parse_tree(&mut sise::Parser::new(&format!("({text})"))).unwrap();
        let sise::TreeNode::List(nodes) = node else { panic!() };
        let commands = air::parser::Parser::new(Arc::new(VirMessageInterface {}))
            .nodes_to_commands(&nodes)
            .unwrap();
        let mut journal = QueryJournal::new();
        journal.record_base(std::iter::once(commands));
        journal
    }

    const BASE: &str = "
        (declare-const fuel%crate!g. FuelId)
        (declare-const fuel%crate!m. FuelId)
        (declare-const fuel%crate!r. FuelId)
        (declare-const fuel%crate!a.s. FuelId)
        (declare-const fuel%crate!b.s. FuelId)
        (declare-const fuel_nat%crate!r. Fuel)
        (axiom (fuel_bool_default fuel%crate!g.))
        (axiom (=> (fuel_bool_default fuel%crate!g.) (and (fuel_bool_default fuel%crate!m.))))
        (axiom (=> (fuel_bool fuel%crate!r.) (forall ((x Int)) (> x 0))))";

    #[test]
    fn the_fuel_scan_reads_defaults_through_groups() {
        let journal = journal_with_base(BASE);
        let scan = FuelScan::of(&journal, 0);
        let fuel = |name: &str| Arc::new(format!("fuel%crate!{name}."));
        assert!(scan.default_visible(&fuel("g")));
        // revealed with its group
        assert!(scan.default_visible(&fuel("m")));
        assert!(!scan.default_visible(&fuel("r")));
        let r = scan.target(&fuel("r")).unwrap();
        assert_eq!(
            (r.name.as_str(), r.fuel_nat.is_some(), r.default_visible),
            ("crate::r", true, false)
        );
        assert!(scan.target(&fuel("m")).unwrap().fuel_nat.is_none());
        assert!(scan.target(&Arc::new("fuel%crate!none.".to_owned())).is_none());
        // a whole path first, then a suffix, which a shared bare name fails
        assert_eq!(scan.find("crate::r").unwrap().name, "crate::r");
        assert_eq!(scan.find("r").unwrap().name, "crate::r");
        assert_eq!(scan.find("a::s").unwrap().name, "crate::a::s");
        assert!(scan.find("s").unwrap_err().contains("2 functions"));
        assert!(scan.find("q").is_err());
    }

    #[test]
    fn fuel_guards_and_reveals_are_recognised() {
        let journal = journal_with_base(BASE);
        let axioms: Vec<&Axiom> = base_axioms(&journal).collect();
        assert_eq!(axioms.len(), 3);
        assert!(fuel_guard(&axioms[0].expr).is_none());
        assert!(fuel_guard(&axioms[1].expr).is_none(), "a default guard is not fuel");
        assert_eq!(
            fuel_guard(&axioms[2].expr).as_deref().map(String::as_str),
            Some("fuel%crate!r.")
        );
        let q = query(QUERY);
        let f = target(true).ident;
        assert!(body_reveals(&q, &f));
        assert!(!body_reveals(&q, &Arc::new("fuel%crate!g.".to_owned())));
        assert!(!query_hides(&q, &f));
        let (q, _) = air::twin::replace_local_axioms(&q, &mut |a: &Axiom| {
            Some(Axiom {
                named: None,
                tag: Some(air::def::ProvenanceTag::Hyp(air::def::HypId(0))),
                expr: a.expr.clone(),
            })
        });
        let (hidden, _) = flip_fuel(&q, &target(true), 0).unwrap();
        assert!(query_hides(&hidden, &f));
        assert!(!body_reveals(&hidden, &f), "the reveals went with the hide");
    }

    #[test]
    fn function_paths_read_back_from_fuel_constants() {
        assert_eq!(
            friendly_path("toydb!encoding.keycode.decode."),
            "toydb::encoding::keycode::decode"
        );
        assert_eq!(friendly_path("crate!f.?"), "crate::f");
    }

    #[test]
    fn assertion_names_parse() {
        let id = |name: AssertName| name.id().map(|id| (*id).clone());
        assert_eq!(id(AssertName::Text("3.1".into())), Some(vec![3, 1]));
        assert_eq!(id(AssertName::Text("aid_3_1".into())), Some(vec![3, 1]));
        assert_eq!(id(AssertName::Text("assert@5".into())), Some(vec![5]));
        assert_eq!(id(AssertName::Path(vec![2])), Some(vec![2]));
        assert_eq!(id(AssertName::Text("x".into())), None);
    }

    #[test]
    fn edits_parse_as_the_plan_spells_them() {
        let edit: TwinEdit =
            serde_json::from_value(serde_json::json!({"flip_fuel": {"fn": "decode", "fuel": 2}}))
                .unwrap();
        assert!(matches!(edit, TwinEdit::FlipFuel { fuel: 2, .. }));
        let edit: TwinEdit =
            serde_json::from_value(serde_json::json!({"reorder_asserts": ["assert@5", [3], "4"]}))
                .unwrap();
        assert!(matches!(edit, TwinEdit::ReorderAsserts(names) if names.len() == 3));
        assert!(
            serde_json::from_value::<TwinEdit>(
                serde_json::json!({"bump_rlimit": 5, "remove_axiom": "x"})
            )
            .is_err()
        );
    }
}
