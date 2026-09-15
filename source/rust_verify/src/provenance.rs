//! Owned source metadata used by both batch verification and resident rechecks.
use std::collections::{HashMap, HashSet};
use vir::ast::Fun;
use vir::ast_util::fun_as_friendly_rust_name;

/// One `check-sat` under `-V provenance`, as cvc5 reported it. `sources` are
/// the tag lists of `(get-assertion-sources :tags-only)`, `instantiations`
/// the `:qid`s the solver instantiated with their vectors. Symbols, not yet
/// joined to source.
#[derive(serde::Serialize, Clone, Debug)]
pub struct QueryProvenance {
    #[serde(skip)]
    pub variable_versions: air::context::VariableVersions,
    pub desc: String,
    pub span: String,
    /// Under `--expand-errors`, the obligation the recheck was focused on, as
    /// the symbol its goal tag carries (`aid_3_1_2`).
    pub focus: Option<String>,
    /// 0 for the first check of the query, then one per multi-error round
    pub round: usize,
    /// "valid", "invalid", "canceled", or the solver's unexpected output
    pub result: String,
    pub sources: Vec<Vec<String>>,
    pub instantiations: Vec<(String, Vec<String>)>,
    pub unparsed: Vec<String>,
}

/// One tag from a solver reply, joined back to source.
#[derive(serde::Serialize, Clone, Debug, PartialEq, Eq)]
pub struct ResolvedTag {
    /// the symbol as it was on the wire
    pub tag: String,
    /// requires, type_invariant, fuel, trait_bound, query, axiom, prelude,
    /// anonymous_axiom, untagged
    pub kind: String,
    /// the function, datatype or quantifier that owns it, when known
    #[serde(skip_serializing_if = "Option::is_none")]
    pub owner: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<String>,
}

/// One instantiated quantifier, joined back to source.
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedInstantiation {
    pub qid: String,
    /// prelude, or the function the quantifier was written in
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fun: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<String>,
    /// the tagged assertion the quantifier was sent inside, when known
    #[serde(skip_serializing_if = "Option::is_none")]
    pub inside: Option<ResolvedTag>,
    /// Where the quantifier is written, in prose. A reader should show this
    /// rather than the generated `qid`, which names nothing in the source.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub site: Option<String>,
    /// Why the quantifier exists, as the encoder that emitted it said. A
    /// reader classifies an instantiation from this, never by matching on
    /// `qid`, which is generated and names nothing a user wrote.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub role: Option<&'static str>,
    pub count: usize,
    /// The instantiation terms as the source spells them (boxes dropped,
    /// symbols as they were written), rendered by `vir::air_names` from the
    /// names the encoders recorded. This is what a reader should show.
    pub terms: Vec<String>,
    /// The same terms as the solver sees them. Kept for debugging this
    /// pipeline; not for display.
    pub vectors: Vec<String>,
}

/// A query's provenance with every symbol joined to source (`-V provenance`).
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedQueryProvenance {
    pub desc: String,
    pub span: String,
    /// Under `--expand-errors`, the obligation this recheck was focused on,
    /// as the symbol its goal tag carries (`aid_3_1_2`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub focus: Option<String>,
    pub round: usize,
    pub result: String,
    /// hypotheses (requires, type invariants, fuel, trait bounds) that fed
    /// some preprocessed assertion
    pub hypotheses: Vec<ResolvedTag>,
    /// the tag lists that name the query or a hypothesis, or hold more than
    /// one tag (a merge or a substitution); singleton axioms are counted, not
    /// listed
    pub sources: Vec<Vec<ResolvedTag>>,
    pub axioms_in_scope: usize,
    pub instantiations: Vec<ResolvedInstantiation>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub unparsed: Vec<String>,
}

/// One `check-sat` under `-V nl-frontier`, as cvc5 reported it: solver
/// terms, tag symbols and qids, not yet joined to source.
#[derive(Clone, Debug)]
pub struct QueryNlFrontier {
    pub desc: String,
    pub span: String,
    /// `body`, `recommends`, `expanded`, ...: a recommends rerun or an
    /// expanded recheck shares the body check's `desc` and `span`
    pub kind: &'static str,
    /// Under `--expand-errors`, the obligation the recheck was focused on, as
    /// the symbol its goal tag carries (`aid_3_1_2`).
    pub focus: Option<String>,
    /// 0 for the first check of the query, then one per multi-error round
    pub round: usize,
    /// "valid", "invalid", "canceled", or the solver's unexpected output
    pub result: String,
    pub frontier: air::context::NlFrontier,
}

/// A constant bound the solver read off an asserted literal.
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedNlBound {
    /// decimal, or `p/q` for a rational
    pub value: String,
    pub strict: bool,
    /// Whether the literal is implied by the query's assertions, rather than
    /// holding only in the branch the solver was exploring.
    pub fixed: bool,
}

/// An argument of a frontier atom, in source spelling.
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedNlTerm {
    pub term: String,
    /// the solver's spelling, for debugging this pipeline; not for display
    pub smt: String,
    /// its value in the solver's candidate model
    pub value: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lower: Option<ResolvedNlBound>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub upper: Option<ResolvedNlBound>,
}

/// Where a frontier atom entered the problem, joined to source.
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedNlHost {
    /// `input` (a hypothesis, the goal or an axiom holds the term) or
    /// `instance` (instantiating a quantifier produced it)
    #[serde(rename = "in")]
    pub place: &'static str,
    /// the hosting term in source spelling, e.g. `(x * y)`
    pub term: String,
    /// input hosts: the assertions holding the term
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub tags: Vec<ResolvedTag>,
    /// instance hosts: the quantifier
    #[serde(skip_serializing_if = "Option::is_none")]
    pub qid: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fun: Option<String>,
    /// the quantifier's span in source; for a spec function's definition,
    /// which no quantifier in source spells, the function's span
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub site: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub role: Option<&'static str>,
    /// input: assertions holding it; instance: vectors producing it
    pub count: u64,
}

/// One nonlinear term the solver could not reconcile, joined to source.
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedNlAtom {
    /// the term in source spelling, e.g. `x * y`
    pub atom: String,
    /// the solver's spelling
    pub smt: String,
    /// product, power, division, iand, pow2, transcendental
    pub kind: String,
    /// whether it was wrong in the solver's most recent refinement round
    pub current: bool,
    /// in how many refinement rounds it was wrong
    pub rounds: u64,
    /// the linear model's value for it, and the value its arguments give it
    pub value: String,
    pub from_args: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lower: Option<ResolvedNlBound>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub upper: Option<ResolvedNlBound>,
    pub args: Vec<ResolvedNlTerm>,
    pub hosts: Vec<ResolvedNlHost>,
    /// The best source location of a host: a hypothesis, the goal of this
    /// query (its span), a quantifier written in source or the spec function
    /// whose definition produced it, or an axiom. The span is of the
    /// enclosing clause, function or quantifier, not of the arithmetic
    /// expression itself. None when no host has a location (the solver's own
    /// lemmas can introduce products).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<String>,
    /// what `span` is: the host tag's kind (requires, goal, axiom, ...) or
    /// the quantifier's role
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span_basis: Option<String>,
}

/// A query's nonlinear frontier joined to source (`-V nl-frontier`).
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedQueryNlFrontier {
    pub desc: String,
    pub span: String,
    pub kind: &'static str,
    /// Under `--expand-errors`, the obligation this recheck was focused on,
    /// as the symbol its goal tag carries (`aid_3_1_2`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub focus: Option<String>,
    pub round: usize,
    pub result: String,
    /// cvc5's own answer to the check: unsat, sat, unknown, or none
    pub solver_result: String,
    /// cvc5's unknown explanation (incomplete, resourceout, ...) or none
    pub reason: String,
    /// whether cvc5's nonlinear extension was on
    pub enabled: bool,
    /// model-based refinement runs, runs with something false in the
    /// candidate model, and runs that gave up
    pub checks: u64,
    pub rounds: u64,
    pub punts: u64,
    /// how the most recent run ended: none, sat, lemma or punt
    pub last: String,
    pub atoms: Vec<ResolvedNlAtom>,
    pub omitted: u64,
    pub truncated: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unparsed: Option<String>,
}

/// One `check-sat` under `-V difficulty`, as cvc5 reported it: rows by tag
/// symbol, not yet joined to source.
#[derive(Clone, Debug)]
pub struct QueryDifficulty {
    pub desc: String,
    pub span: String,
    /// `body`, `recommends`, `expanded`, ...: a recommends rerun or an
    /// expanded recheck shares the body check's `desc` and `span`
    pub kind: &'static str,
    /// Under `--expand-errors`, the obligation the recheck was focused on, as
    /// the symbol its goal tag carries (`aid_3_1_2`).
    pub focus: Option<String>,
    /// 0 for the first check of the query, then one per multi-error round
    pub round: usize,
    /// "valid", "invalid", "canceled", or the solver's unexpected output
    pub result: String,
    pub gradient: air::context::DifficultyGradient,
}

/// One tagged input assertion of a query, joined to source. The numbers are
/// cvc5's own; nothing here is derived.
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedDifficultyRow {
    /// The assertion's tags, each joined to source; several when identical
    /// assertions were merged.
    pub tags: Vec<ResolvedTag>,
    /// How many lemmas used a literal this assertion made relevant (cvc5's
    /// difficulty measure): a heuristic for the solver work through it.
    pub difficulty: u64,
    /// Whether the unsat core holds it; present only after `unsat`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub in_core: Option<bool>,
}

/// Whether a difficulty row is an axiom that did nothing: it was in scope,
/// no lemma used a literal it made relevant, and the unsat core does not
/// hold it (or the check reported no core). Most of a query's rows are
/// these, so `resolve_difficulty` counts them instead of listing them. A row
/// cvc5 sent without tags is listed rather than counted, so that nothing
/// disappears into the count.
fn is_idle_axiom(tags: &[ResolvedTag], difficulty: u64, in_core: Option<bool>) -> bool {
    difficulty == 0
        && in_core != Some(true)
        && !tags.is_empty()
        && tags.iter().all(|t| matches!(t.kind.as_str(), "axiom" | "prelude" | "anonymous_axiom"))
}

/// A query's difficulty gradient with every tag joined to source
/// (`-V difficulty`).
///
/// Several records of one function can share `desc`, `span`, `kind` and
/// `round`: a bit-vector or nonlinear subquery and a loop body check each
/// come from the function's own check. Expanded rechecks carry `focus` to
/// say which obligation they are about.
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedQueryDifficulty {
    pub desc: String,
    pub span: String,
    pub kind: &'static str,
    /// Under `--expand-errors`, the obligation this recheck was focused on,
    /// as the symbol its goal tag carries (`aid_3_1_2`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub focus: Option<String>,
    /// 0 for the first check, then one per multi-error round. The rounds of
    /// a query share its solver scope, and cvc5 keeps difficulty until that
    /// scope is popped, so a round's counts include the rounds before it.
    pub round: usize,
    pub result: String,
    /// cvc5's own answer to the check: unsat, sat, unknown, or none. Empty
    /// when `unparsed` is set, since cvc5 then never answered the key.
    pub solver_result: String,
    /// whether cvc5 tracked difficulty
    pub difficulty: bool,
    /// whether each row carries `in_core`
    pub core: bool,
    /// Largest difficulty first: every hypothesis and the goal, and each
    /// axiom that did some work or is in the core.
    pub rows: Vec<ResolvedDifficultyRow>,
    /// The axioms in scope that did no work (difficulty 0) and are not in
    /// the core, counted rather than listed: most of what is in scope.
    pub idle_axioms: u64,
    /// the untagged input assertions (each multi-error round's assertion
    /// disabling the errors already found), summed
    pub untagged_asserted: u64,
    pub untagged_difficulty: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub untagged_in_core: Option<u64>,
    /// difficulty cvc5 could not carry back to a current input assertion
    pub unmatched_difficulty: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unparsed: Option<String>,
}

/// One `check-sat` under `-V inst-pressure`, as cvc5 reported it: rows by
/// `:qid`, not yet joined to source.
#[derive(Clone, Debug)]
pub struct QueryInstPressure {
    pub desc: String,
    pub span: String,
    /// `body`, `recommends`, `expanded`, ...: a recommends rerun or an
    /// expanded recheck shares the body check's `desc` and `span`
    pub kind: &'static str,
    /// Under `--expand-errors`, the obligation the recheck was focused on, as
    /// the symbol its goal tag carries (`aid_3_1_2`).
    pub focus: Option<String>,
    /// 0 for the first check of the query, then one per multi-error round
    pub round: usize,
    /// "valid", "invalid", "canceled", or the solver's unexpected output
    pub result: String,
    pub pressure: air::context::InstPressure,
}

/// One quantifier's instantiation pressure in one query, joined to source.
/// Every count is the solver's own; nothing here is derived.
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedQuantPressure {
    pub qid: String,
    /// false for a quantifier without a `:qid`: `qid` is then synthetic
    pub named: bool,
    /// prelude, or the function the quantifier was written in
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fun: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<String>,
    /// Where the quantifier is written, in prose (as in provenance).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub site: Option<String>,
    /// Why the quantifier exists, as the encoder that emitted it said.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub role: Option<&'static str>,
    pub instantiations: u64,
    /// attempts rejected because the term vector was used before
    pub duplicate_eq: u64,
    /// attempts rejected because the instance was already entailed
    pub duplicate_ent: u64,
    /// attempts rejected because the same lemma was already sent
    pub duplicate_lemma: u64,
    /// instances made by conflict-based instantiation because they
    /// conflicted with, or propagated in, the current assignment
    pub conflict: u64,
    pub propagate: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub first_round: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub last_round: Option<u64>,
    /// instances the refutation used; only after `unsat` with proofs on
    #[serde(skip_serializing_if = "Option::is_none")]
    pub refutation: Option<u64>,
}

/// A query's instantiation pressure with every quantifier joined to source
/// (`-V inst-pressure`).
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedQueryInstPressure {
    pub desc: String,
    pub span: String,
    pub kind: &'static str,
    /// Under `--expand-errors`, the obligation this recheck was focused on,
    /// as the symbol its goal tag carries (`aid_3_1_2`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub focus: Option<String>,
    pub round: usize,
    pub result: String,
    /// instantiation rounds that sent lemmas
    pub rounds: u64,
    /// whether each row carries `refutation`
    pub refutation: bool,
    /// most instantiated first
    pub quantifiers: Vec<ResolvedQuantPressure>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unparsed: Option<String>,
}

/// One unknown `check-sat` under `-V matching-loops`, as cvc5 reported it.
/// Symbols and SMT terms, not yet joined to source.
#[derive(Clone, Debug)]
pub struct QueryMatchingLoops {
    pub desc: String,
    pub span: String,
    /// Under `--expand-errors`, the obligation the recheck was focused on, as
    /// the symbol its goal tag carries (`aid_3_1_2`).
    pub focus: Option<String>,
    /// 0 for the first check of the query, then one per multi-error round
    pub round: usize,
    /// "invalid" or "canceled": the verdict the unknown turned into
    pub result: String,
    pub info: air::context::MatchingLoopsInfo,
}

/// A loop's terms as the solver sees them. Kept for debugging this
/// pipeline; not for display.
#[derive(serde::Serialize, Clone, Debug)]
pub struct MatchingLoopSmt {
    pub trigger: Vec<String>,
    pub context: Vec<String>,
    pub shape: Vec<String>,
    pub step: Vec<String>,
    pub ladder: Vec<Vec<String>>,
    pub via: Vec<String>,
}

/// One self-feeding quantifier, joined back to source (`-V matching-loops`).
/// The ladder, rounds and counts are the solver's own record; the verdict
/// that they form a loop is a judgement, graded by `confidence`.
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedMatchingLoop {
    pub qid: String,
    /// prelude, or the function the quantifier was written in
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fun: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<String>,
    /// Where the quantifier is written, in prose
    #[serde(skip_serializing_if = "Option::is_none")]
    pub site: Option<String>,
    /// Why the quantifier exists, as the encoder that emitted it said
    #[serde(skip_serializing_if = "Option::is_none")]
    pub role: Option<&'static str>,
    /// high: a stable shape of rising depth, fed by its own instantiations,
    /// still climbing when the round limit stopped the check; medium: the
    /// same without the round limit; low: rising depth with an unstable
    /// shape or without confirmed self-feeding edges
    pub confidence: String,
    /// linear-depth (+d solver term depth/round), exponential-fanout (xf
    /// instantiations/step, a step being one of the quantifier's own
    /// rounds), or bounded. The depth is the solver's, so it counts the boxes
    /// `term_ladder` leaves out.
    pub growth_rate: String,
    /// the trigger whose matches formed the rungs, in source spelling
    pub trigger: String,
    /// every rung generalised, then every rung after the first, with `_n`
    /// where they differ: `f(_0)  →  f(g(_0))`
    pub term_shape: String,
    /// what each rung wraps around the previous rung's growing subterm,
    /// generalised over the chain, `_0` marking that subterm: `cons(_1, _0)`;
    /// one per class when the loop climbs several subterms (`r(_0)`, `l(_0)`)
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub growth_context: Vec<String>,
    /// the trigger as instantiated by the first rungs of the chain and by its
    /// last, in source spelling; `…` stands for the rungs cvc5 left out
    pub term_ladder: Vec<String>,
    /// how many rungs the chain has
    pub ladder_length: u64,
    /// whether each rung grows out of the previous one by one context
    pub stable_shape: bool,
    /// confirmed: each rung matched a term the previous rung introduced;
    /// unconfirmed: the ladder is the deepest instantiation of each round
    pub edges: String,
    /// rounds in which the quantifier was instantiated, and the chain's span
    pub rounds: u64,
    pub first_round: u64,
    pub last_round: u64,
    pub instantiations: u64,
    /// instantiations that matched a term another of its own introduced
    pub self_fed: u64,
    pub depth_per_rung: f64,
    pub depth_per_round: f64,
    pub fanout_per_round: f64,
    /// growth per step of the quantifier's own rounds, which a loop that
    /// fires every other round shows and `fanout_per_round` averages away
    pub fanout_per_step: f64,
    /// instantiations per round, the last rounds of the check
    pub per_round: Vec<u64>,
    /// the other quantifiers a step passed through, where they are written
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub via: Vec<String>,
    /// quantifiers the user did not write (the prelude's box, has_type and
    /// arithmetic axioms, and the axioms Verus generates for definitions)
    /// that climbed in the same check on this loop's terms: a rung cvc5
    /// reported for them shares a term that this loop grows and no other
    /// written loop does. A quantifier can follow several loops.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub followers: Vec<String>,
    pub smt: MatchingLoopSmt,
}

/// An unknown query's matching loops, joined to source (`-V matching-loops`).
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedQueryMatchingLoops {
    pub desc: String,
    pub span: String,
    /// Under `--expand-errors`, the obligation this recheck was focused on,
    /// as the symbol its goal tag carries (`aid_3_1_2`).
    #[serde(skip_serializing_if = "Option::is_none")]
    pub focus: Option<String>,
    pub round: usize,
    pub result: String,
    /// the last instantiation round of the check
    pub rounds: u64,
    pub instantiations: u64,
    /// instantiations cvc5 stopped recording (past `--matching-loops-max`)
    #[serde(skip_serializing_if = "is_zero")]
    pub dropped: u64,
    /// whether the instantiation round limit stopped the check
    pub max_inst_rounds: bool,
    /// most confident first: the quantifiers the user wrote, or, when none of
    /// them looped, the others that did
    pub loops: Vec<ResolvedMatchingLoop>,
    /// quantifiers the user did not write that climbed alongside the written
    /// loops but share a term with none of them in particular
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub followers: Vec<String>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub unparsed: Vec<String>,
}

fn is_zero(n: &u64) -> bool {
    *n == 0
}

const PRELUDE_QID_PREFIX: &str = "prelude_";
/// The prelude writes this one by hand, so it has no `qid_map` entry.
const FUEL_DEFAULTS_QID: &str = "prelude_fuel_defaults";

/// Where an instantiated quantifier came from, joined back to source.
struct QuantifierJoin {
    fun: Option<String>,
    span: Option<String>,
    inside: Option<ResolvedTag>,
    site: Option<String>,
    role: Option<&'static str>,
}

/// A span without its directory or trailing id, for prose.
fn span_short(s: &Option<String>) -> Option<String> {
    s.as_ref()
        .map(|s| s.rsplit('/').next().unwrap_or(s).split(" (#").next().unwrap_or(s).to_string())
}

/// Every parenthesised subterm of an SMT term printed on one line, as text,
/// so that equal subterms of different terms compare equal.
fn subterms(term: &str, out: &mut HashSet<String>) {
    let mut starts = Vec::new();
    for (i, c) in term.char_indices() {
        match c {
            '(' => starts.push(i),
            ')' => {
                if let Some(start) = starts.pop() {
                    out.insert(term[start..=i].to_string());
                }
            }
            _ => {}
        }
    }
}

struct Hypothesis {
    kind: String,
    span: String,
}
struct Quantifier {
    fun: String,
    span: Option<String>,
    tag: Option<air::def::ProvenanceTag>,
    role: Option<&'static str>,
    /// positions of the binders that bind type parameters, which an
    /// instantiation's `terms` leave out
    type_binders: Vec<usize>,
}

/// One candidate culprit of an `unknown` answer, joined back to source.
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedCulprit {
    pub qid: String,
    /// prelude, or the function the quantifier was written in
    #[serde(skip_serializing_if = "Option::is_none")]
    pub fun: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<String>,
    /// Why the quantifier exists, as the encoder that emitted it said.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub role: Option<&'static str>,
}

impl ResolvedCulprit {
    /// Sort key: quantifiers with a source span, then the rest Verus emitted,
    /// then the prelude's.
    fn rank(&self) -> u8 {
        match (&self.span, self.fun.as_deref()) {
            (Some(_), _) => 0,
            (None, Some("prelude")) => 2,
            (None, _) => 1,
        }
    }
}

/// Why a query's first check answered `unknown`, with the solver's candidate
/// culprit quantifiers joined back to source.
#[derive(serde::Serialize, Clone, Debug)]
pub struct ResolvedUnknownReason {
    pub desc: String,
    pub span: String,
    /// the solver's `:reason-unknown`: incomplete, resourceout, timeout, ...
    pub reason: String,
    /// cvc5's `IncompleteId` for an incomplete answer: QUANTIFIERS, ARITH_NL,
    /// QUANTIFIERS_MAX_INST_ROUNDS, ...
    #[serde(skip_serializing_if = "Option::is_none")]
    pub incomplete_id: Option<String>,
    /// the asserted quantifiers no solver strategy claimed to have fully
    /// processed: those with a source span first and the prelude's last, each
    /// group in the order the solver found them
    pub culprits: Vec<ResolvedCulprit>,
}

/// The quantifier table alone. It is enough to join an `unknown` answer's
/// culprits to source, and cheap enough to capture in every run, unlike the
/// rest of `Symbols`.
pub(crate) struct Quantifiers(HashMap<String, Quantifier>);

impl Quantifiers {
    pub(crate) fn capture(global: &vir::context::GlobalCtx) -> Self {
        Self(
            global
                .qid_map
                .borrow()
                .iter()
                .map(|(qid, info)| {
                    (
                        qid.clone(),
                        Quantifier {
                            fun: fun_as_friendly_rust_name(&info.fun),
                            span: info.user.as_ref().map(|user| user.span.as_string.clone()),
                            tag: info.tag.clone(),
                            role: info.role.as_ref().map(role_name),
                            type_binders: info.type_binders.clone(),
                        },
                    )
                })
                .collect(),
        )
    }

    pub(crate) fn resolve_unknown(
        &self,
        desc: &str,
        span: &str,
        reason: air::context::UnknownReason,
    ) -> ResolvedUnknownReason {
        let mut culprits: Vec<ResolvedCulprit> = reason
            .culprit_qids
            .into_iter()
            .map(|qid| match self.0.get(&qid) {
                Some(info) => ResolvedCulprit {
                    fun: Some(info.fun.clone()),
                    span: info.span.clone(),
                    role: info.role,
                    qid,
                },
                None => ResolvedCulprit {
                    fun: qid.starts_with(PRELUDE_QID_PREFIX).then(|| "prelude".to_string()),
                    span: None,
                    role: (qid == FUEL_DEFAULTS_QID).then_some("fuel_defaults"),
                    qid,
                },
            })
            .collect();
        // Under plain E-matching every asserted quantifier is a culprit, and
        // the prelude alone contributes about 80. The ones with a source span
        // are the ones a user can act on, so they lead; the sort is stable.
        culprits.sort_by_key(ResolvedCulprit::rank);
        ResolvedUnknownReason {
            desc: desc.to_owned(),
            span: span.to_owned(),
            reason: reason.reason,
            incomplete_id: reason.incomplete_id,
            culprits,
        }
    }
}

/// No compiler context, source map, or VIR expression is retained here.
pub(crate) struct Symbols {
    hypotheses: HashMap<Fun, Vec<Hypothesis>>,
    quantifiers: HashMap<String, Quantifier>,
    axiom_owners: HashMap<String, String>,
    /// Owners of the internal quantifiers `quantifiers` has no function for.
    internal_qid_owners: HashMap<String, String>,
    source_names: vir::air_names::SourceNames,
    /// Friendly function name -> the function's span, when recorded (see
    /// `with_function_spans`).
    function_spans: HashMap<String, String>,
    /// The crate being verified, whose items the source names spell under
    /// its own name, and source pasted into it must spell under `crate::`.
    crate_name: String,
}

impl Symbols {
    /// What a generated `:qid` belongs to: its function or, for an internal
    /// quantifier made outside any function, the datatype, trait or impl it
    /// was made for. For a quantifier the user wrote, also its source span.
    pub(crate) fn quantifier_site(&self, qid: &str) -> Option<(&str, Option<&str>)> {
        match self.quantifiers.get(qid) {
            Some(q) => Some((q.fun.as_str(), q.span.as_deref())),
            None => self.internal_qid_owners.get(qid).map(|owner| (owner.as_str(), None)),
        }
    }

    /// Every `:qid` owned at `path` or inside it, matching whole segments:
    /// `a::S` takes `a::S`, `a::S::f` and `a::S<int.>` but not `a::Seq`. The
    /// prelude's quantifiers belong to nothing and are never found.
    pub(crate) fn quantifiers_of(&self, path: &str) -> std::collections::HashSet<String> {
        let path = path.strip_suffix("::").unwrap_or(path);
        let within = |owner: &str| {
            owner.strip_prefix(path).is_some_and(|rest| {
                rest.is_empty() || rest.starts_with("::") || rest.starts_with('<')
            })
        };
        let functions = self.quantifiers.iter().map(|(qid, q)| (qid, q.fun.as_str()));
        let internal = self.internal_qid_owners.iter().map(|(qid, owner)| (qid, owner.as_str()));
        functions
            .chain(internal)
            .filter(|(_, owner)| within(owner))
            .map(|(qid, _)| qid.clone())
            .collect()
    }

    pub(crate) fn capture(
        global: &vir::context::GlobalCtx,
        source_names: vir::air_names::SourceNames,
    ) -> Self {
        let hypotheses = global
            .hyp_map
            .borrow()
            .iter()
            .map(|(fun, hypotheses)| {
                (
                    fun.clone(),
                    hypotheses
                        .iter()
                        .map(|info| Hypothesis {
                            kind: match info.kind {
                                vir::sst::HypKind::Requires => "requires",
                                vir::sst::HypKind::TypeInvariant => "type_invariant",
                                vir::sst::HypKind::Fuel => "fuel",
                                vir::sst::HypKind::TraitBound => "trait_bound",
                            }
                            .to_owned(),
                            span: info.span.as_string.clone(),
                        })
                        .collect(),
                )
            })
            .collect();
        let Quantifiers(quantifiers) = Quantifiers::capture(global);
        Self {
            hypotheses,
            quantifiers,
            axiom_owners: global.axiom_owners.borrow().clone(),
            internal_qid_owners: global.internal_qid_owners.borrow().clone(),
            source_names,
            function_spans: HashMap::new(),
            crate_name: vir::def::krate_to_string_ignore_stable_id(&global.crate_name),
        }
    }

    /// The source of `hyp_k` of `fun`: the kind of hypothesis (`requires`,
    /// `type_invariant`, `fuel`, `trait_bound`) and its span. A bisect names
    /// the hypotheses it removes by this.
    pub(crate) fn hypothesis(&self, fun: &Fun, k: u64) -> Option<(&str, &str)> {
        let hypothesis = self.hypotheses.get(fun)?.get(usize::try_from(k).ok()?)?;
        Some((&hypothesis.kind, &hypothesis.span))
    }

    /// The source names for one query's solver terms: each SSA symbol in
    /// `versions` is named as its variable, followed by its assignment version
    /// when `annotate`. SSA versions are query-local, so a display keeps
    /// assignment identity, while source to paste into a function cannot.
    pub(crate) fn query_names<'a>(
        &'a self,
        versions: &air::context::VariableVersions,
        annotate: bool,
    ) -> std::borrow::Cow<'a, vir::air_names::SourceNames> {
        let mut names = std::borrow::Cow::Borrowed(&self.source_names);
        for (symbol, (base, version)) in versions {
            if let Some(name) = vir::air_names::source_symbol(&names, base) {
                let name = if annotate { format!("{name} (version {version})") } else { name };
                names.to_mut().insert(symbol.clone(), vir::air_names::SourceName::Symbol(name));
            }
        }
        names
    }

    /// The source names for pasting one query's solver terms into the crate
    /// they came from: SSA symbols as their variable alone, and the crate's
    /// own items as `crate::` paths, since a crate cannot name itself.
    pub(crate) fn paste_names<'a>(
        &'a self,
        versions: &air::context::VariableVersions,
    ) -> std::borrow::Cow<'a, vir::air_names::SourceNames> {
        use vir::air_names::SourceName;
        let mut names = self.query_names(versions, false);
        let own = format!("{}::", self.crate_name);
        // call heads, recorded with their type arguments, are renamed too
        let renamed: Vec<(String, SourceName)> = names
            .iter()
            .filter_map(|(symbol, name)| match name {
                SourceName::Symbol(name) => name
                    .strip_prefix(&own)
                    .map(|rest| (symbol.clone(), SourceName::Symbol(format!("crate::{rest}")))),
                SourceName::Function { name, type_args } => name.strip_prefix(&own).map(|rest| {
                    let name = format!("crate::{rest}");
                    (symbol.clone(), SourceName::Function { name, type_args: *type_args })
                }),
                _ => None,
            })
            .collect();
        if !renamed.is_empty() {
            let names = names.to_mut();
            for (symbol, name) in renamed {
                names.insert(symbol, name);
            }
        }
        names
    }

    /// Where the quantifier the solver names `qid` is written, when a proof
    /// relies on it: the user wrote it, or it defines a function. `None` for
    /// the encoding's own axioms (the prelude, boxing, type invariants, fuel)
    /// and for a name this crate's encoders did not mint.
    pub(crate) fn proof_quantifier_site(&self, qid: &str) -> Option<String> {
        let info = self.quantifiers.get(qid)?;
        match (&info.span, info.role) {
            (Some(span), _) => Some(format!("the quantifier at {span}")),
            (None, Some("definition" | "definition_unfold" | "definition_base")) => {
                Some(format!("the definition of `{}`", info.fun))
            }
            _ => None,
        }
    }

    /// Record each function's span, so that a spec function's definition
    /// axiom, which no quantifier in source spells, can be located at the
    /// function it defines.
    pub(crate) fn with_function_spans(mut self, functions: &[vir::ast::Function]) -> Self {
        self.function_spans = functions
            .iter()
            .map(|f| (fun_as_friendly_rust_name(&f.x.name), f.span.as_string.clone()))
            .collect();
        self
    }

    /// `with_function_spans` for the lowered functions a bucket verifies.
    pub(crate) fn with_sst_function_spans(mut self, functions: &[vir::sst::FunctionSst]) -> Self {
        self.function_spans = functions
            .iter()
            .map(|f| (fun_as_friendly_rust_name(&f.x.name), f.span.as_string.clone()))
            .collect();
        self
    }

    /// Where the function (or broadcast group) `name` is written, when this
    /// crate defines it.
    pub(crate) fn function_span(&self, name: &str) -> Option<&str> {
        self.function_spans.get(name).map(String::as_str)
    }

    /// The broadcast lemma or broadcast group that states the axiom `tag`
    /// tags. The encoder tags three kinds of axiom: those two, and a
    /// datatype's resolve axiom, which is the encoding's own.
    pub(crate) fn broadcast_owner(&self, tag: &air::def::ProvenanceTag) -> Option<&str> {
        let air::def::ProvenanceTag::Axiom(_) = tag else { return None };
        let owner = self.axiom_owners.get(&tag.to_symbol())?;
        (!owner.ends_with(vir::def::RESOLVE_AXIOM_OWNER_SUFFIX)).then_some(owner.as_str())
    }

    /// The group an ablation switches a declaration-prefix axiom in: the
    /// function or broadcast group that owns it, by its tag or else by its
    /// quantifier's `:qid`. `None` for the encoding's own axioms (datatypes,
    /// traits, boxing, fuel defaults, the prelude), which stay asserted.
    ///
    /// By `:qid`, only a quantifier the encoder says belongs to a function (a
    /// definition or return type invariant) or one the user wrote counts:
    /// `qid_map` records the function being encoded for every quantifier,
    /// including trait-impl and boxing axioms made while encoding it, and
    /// those are not the function's.
    pub(crate) fn axiom_group(&self, axiom: &air::ast::Axiom) -> Option<&str> {
        if let Some(tag @ air::def::ProvenanceTag::Axiom(_)) = &axiom.tag {
            return self.broadcast_owner(tag);
        }
        let qid = air::bisect::axiom_qid(&axiom.expr)?;
        let q = self.quantifiers.get(&*qid)?;
        let owned = match q.role {
            Some(role) => role != "fuel_defaults",
            None => q.span.is_some(),
        };
        owned.then_some(q.fun.as_str())
    }

    /// The role of the quantifier `qid` names (`definition`,
    /// `definition_unfold`, `return_type_invariant`, ...), when the encoder
    /// recorded one.
    pub(crate) fn quantifier_role(&self, qid: &str) -> Option<&'static str> {
        self.quantifiers.get(qid).and_then(|q| q.role)
    }

    /// Join one tag from a reply about one of `fun`'s queries back to source.
    fn tag_of(&self, fun: &Fun, symbol: &str) -> ResolvedTag {
        let mut r =
            ResolvedTag { tag: symbol.to_string(), kind: String::new(), owner: None, span: None };
        match air::def::ProvenanceTag::from_symbol(symbol) {
            Some(air::def::ProvenanceTag::Hyp(air::def::HypId(k))) => {
                match self.hypotheses.get(fun).and_then(|hs| hs.get(k as usize)) {
                    Some(info) => {
                        r.kind = info.kind.clone();
                        r.owner = Some(fun_as_friendly_rust_name(fun));
                        r.span = Some(info.span.clone());
                    }
                    None => r.kind = "hypothesis (unknown id)".to_string(),
                }
            }
            Some(air::def::ProvenanceTag::Query) => r.kind = "query".to_string(),
            Some(air::def::ProvenanceTag::Assert(_)) => r.kind = "goal".to_string(),
            Some(air::def::ProvenanceTag::Axiom(ident)) => {
                let ident: &str = &ident;
                if let Some(owner) = self.axiom_owners.get(symbol) {
                    r.kind = "axiom".to_string();
                    // a broadcast axiom is known by the function that states
                    // it, so the span is that function's (`with_function_spans`)
                    r.span = self.function_spans.get(owner).cloned();
                    r.owner = Some(owner.clone());
                } else if let Some(info) = self.quantifiers.get(ident) {
                    r.kind = "axiom".to_string();
                    r.owner = Some(info.fun.clone());
                    r.span = info.span.clone();
                } else if ident.starts_with(PRELUDE_QID_PREFIX) {
                    r.kind = "prelude".to_string();
                } else if ident.starts_with("anon_") {
                    r.kind = "anonymous_axiom".to_string();
                } else {
                    r.kind = "axiom".to_string();
                }
            }
            None => r.kind = "untagged".to_string(),
        }
        r
    }

    /// Join a quantifier that one of `fun`'s queries instantiated back to
    /// source by its `:qid`.
    fn quantifier(&self, fun: &Fun, qid: &str) -> QuantifierJoin {
        let (fun_name, span, inside, role) = match self.quantifiers.get(qid) {
            Some(info) => (
                Some(info.fun.clone()),
                info.span.clone(),
                info.tag.as_ref().map(|t| self.tag_of(fun, &t.to_symbol())),
                info.role,
            ),
            None => (
                qid.starts_with(PRELUDE_QID_PREFIX).then(|| "prelude".to_string()),
                None,
                None,
                (qid == FUEL_DEFAULTS_QID).then_some("fuel_defaults"),
            ),
        };
        let site = quantifier_site(&inside, &span_short(&span));
        QuantifierJoin { fun: fun_name, span, inside, site, role }
    }

    pub(crate) fn resolve(&self, fun: &Fun, q: QueryProvenance) -> ResolvedQueryProvenance {
        let is_hyp_kind =
            |k: &str| matches!(k, "requires" | "type_invariant" | "fuel" | "trait_bound");
        let source_names = self.query_names(&q.variable_versions, true);
        let mut hypotheses: Vec<ResolvedTag> = Vec::new();
        let mut sources: Vec<Vec<ResolvedTag>> = Vec::new();
        let mut axioms_in_scope = 0usize;
        for list in q.sources.iter() {
            let tags: Vec<ResolvedTag> = list.iter().map(|t| self.tag_of(fun, t)).collect();
            let interesting =
                tags.len() > 1 || tags.iter().any(|t| is_hyp_kind(&t.kind) || t.kind == "query");
            for t in tags.iter() {
                if is_hyp_kind(&t.kind) && !hypotheses.contains(t) {
                    hypotheses.push(t.clone());
                }
            }
            if interesting {
                sources.push(tags);
            } else {
                axioms_in_scope += 1;
            }
        }
        let instantiations = q
            .instantiations
            .iter()
            .map(|(qid, vectors)| {
                let QuantifierJoin { fun: fun_name, span, inside, site, role } =
                    self.quantifier(fun, qid);
                let type_binders =
                    self.quantifiers.get(qid).map_or(&[][..], |q| q.type_binders.as_slice());
                ResolvedInstantiation {
                    qid: qid.clone(),
                    fun: fun_name,
                    span,
                    inside,
                    site,
                    role,
                    count: vectors.len(),
                    terms: vectors
                        .iter()
                        .map(|v| {
                            vir::air_names::render_vector_except(&source_names, v, type_binders)
                        })
                        .collect(),
                    vectors: vectors.clone(),
                }
            })
            .collect();
        ResolvedQueryProvenance {
            desc: q.desc,
            span: q.span,
            focus: q.focus,
            round: q.round,
            result: q.result,
            hypotheses,
            sources,
            axioms_in_scope,
            instantiations,
            unparsed: q.unparsed,
        }
    }

    /// Join each tagged assertion of a query's difficulty gradient to source.
    /// cvc5 reports every tagged assertion in scope, which is mostly axioms
    /// that play no part; those are counted in `idle_axioms`, not listed.
    pub(crate) fn resolve_difficulty(
        &self,
        fun: &Fun,
        q: QueryDifficulty,
    ) -> ResolvedQueryDifficulty {
        let g = q.gradient;
        let mut rows = Vec::new();
        let mut idle_axioms = 0u64;
        for row in g.rows {
            let tags: Vec<ResolvedTag> = row.tags.iter().map(|t| self.tag_of(fun, t)).collect();
            if is_idle_axiom(&tags, row.difficulty, row.in_core) {
                idle_axioms += 1;
            } else {
                rows.push(ResolvedDifficultyRow {
                    tags,
                    difficulty: row.difficulty,
                    in_core: row.in_core,
                });
            }
        }
        ResolvedQueryDifficulty {
            desc: q.desc,
            span: q.span,
            kind: q.kind,
            focus: q.focus,
            round: q.round,
            result: q.result,
            solver_result: g.result,
            difficulty: g.difficulty,
            core: g.core,
            rows,
            idle_axioms,
            untagged_asserted: g.untagged_asserted,
            untagged_difficulty: g.untagged_difficulty,
            untagged_in_core: g.untagged_in_core,
            unmatched_difficulty: g.unmatched_difficulty,
            unparsed: g.unparsed,
        }
    }

    /// Join each quantifier of a query's instantiation pressure to source.
    pub(crate) fn resolve_inst_pressure(
        &self,
        fun: &Fun,
        q: QueryInstPressure,
    ) -> ResolvedQueryInstPressure {
        let quantifiers = q
            .pressure
            .quantifiers
            .into_iter()
            .map(|p| {
                let join = if p.named {
                    self.quantifier(fun, &p.qid)
                } else {
                    QuantifierJoin { fun: None, span: None, inside: None, site: None, role: None }
                };
                ResolvedQuantPressure {
                    qid: p.qid,
                    named: p.named,
                    fun: join.fun,
                    span: join.span,
                    site: join.site,
                    role: join.role,
                    instantiations: p.instantiations,
                    duplicate_eq: p.duplicate_eq,
                    duplicate_ent: p.duplicate_ent,
                    duplicate_lemma: p.duplicate_lemma,
                    conflict: p.conflict,
                    propagate: p.propagate,
                    first_round: p.first_round,
                    last_round: p.last_round,
                    refutation: p.refutation,
                }
            })
            .collect();
        ResolvedQueryInstPressure {
            desc: q.desc,
            span: q.span,
            kind: q.kind,
            focus: q.focus,
            round: q.round,
            result: q.result,
            rounds: q.pressure.rounds,
            refutation: q.pressure.refutation,
            quantifiers,
            unparsed: q.pressure.unparsed,
        }
    }

    pub(crate) fn resolve_matching_loops(
        &self,
        fun: &Fun,
        q: QueryMatchingLoops,
    ) -> ResolvedQueryMatchingLoops {
        let names = self.query_names(&q.info.variable_versions, true);
        let render = |terms: &[String]| -> String {
            terms
                .iter()
                .map(|t| vir::air_names::render_term(&names, t))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let loops = q
            .info
            .loops
            .into_iter()
            .map(|l| {
                let QuantifierJoin { fun: fun_name, span, inside: _, site, role } =
                    self.quantifier(fun, &l.qid);
                let growth_rate = match l.growth.as_str() {
                    "linear-depth" => {
                        format!("linear-depth (+{:.2} solver term depth/round)", l.depth_per_round)
                    }
                    "exponential-fanout" => format!(
                        "exponential-fanout (x{:.2} instantiations/step)",
                        l.fanout_per_step
                    ),
                    other => other.to_string(),
                };
                let via = l
                    .via
                    .iter()
                    .map(|qid| self.quantifier(fun, qid).site.unwrap_or_else(|| qid.clone()))
                    .collect();
                let mut term_ladder: Vec<String> =
                    l.ladder.iter().map(|rung| render(rung)).collect();
                // cvc5 sends the first rungs and the last: mark the gap
                if term_ladder.len() >= 2 && l.ladder_length > term_ladder.len() as u64 {
                    term_ladder.insert(term_ladder.len() - 1, "…".to_string());
                }
                ResolvedMatchingLoop {
                    qid: l.qid.clone(),
                    fun: fun_name,
                    span,
                    site,
                    role,
                    confidence: l.confidence.clone(),
                    growth_rate,
                    trigger: render(&l.trigger),
                    term_shape: format!("{}  →  {}", render(&l.shape), render(&l.step)),
                    growth_context: l
                        .context
                        .iter()
                        .map(|c| vir::air_names::render_term(&names, c))
                        .collect(),
                    term_ladder,
                    ladder_length: l.ladder_length,
                    stable_shape: l.stable,
                    edges: if l.edges_confirmed { "confirmed" } else { "unconfirmed" }.to_string(),
                    rounds: l.rounds,
                    first_round: l.first_round,
                    last_round: l.last_round,
                    instantiations: l.instantiations,
                    self_fed: l.self_fed,
                    depth_per_rung: l.depth_per_rung,
                    depth_per_round: l.depth_per_round,
                    fanout_per_round: l.fanout_per_round,
                    fanout_per_step: l.fanout_per_step,
                    per_round: l.per_round.clone(),
                    via,
                    followers: Vec::new(),
                    smt: MatchingLoopSmt {
                        trigger: l.trigger,
                        context: l.context,
                        shape: l.shape,
                        step: l.step,
                        ladder: l.ladder,
                        via: l.via,
                    },
                }
            })
            .collect::<Vec<ResolvedMatchingLoop>>();
        // Only a quantifier the user wrote can drive a loop. The prelude's
        // axioms, and the ones Verus generates for definitions, climb when a
        // written quantifier feeds them new terms. When a check has a written
        // loop, each of the others follows the written loops whose own terms
        // it shares; terms every written loop has (`(I 0)`) pick out none.
        // When it has none, the others are its loops, so the check still
        // shows what climbed.
        let written =
            |l: &ResolvedMatchingLoop| l.qid.starts_with(air::profiler::USER_QUANT_PREFIX);
        let (mut loops, riders): (Vec<_>, Vec<_>) = loops.into_iter().partition(written);
        let mut followers = Vec::new();
        if loops.is_empty() {
            loops = riders;
        } else {
            let terms_of = |l: &ResolvedMatchingLoop| {
                let mut terms = HashSet::new();
                for t in l.smt.ladder.iter().flatten().chain(&l.smt.step) {
                    subterms(t, &mut terms);
                }
                terms
            };
            let grown: Vec<HashSet<String>> = loops.iter().map(terms_of).collect();
            let own: Vec<HashSet<String>> = (0..grown.len())
                .map(|i| {
                    let others =
                        |t: &String| (0..grown.len()).any(|j| j != i && grown[j].contains(t));
                    grown[i].iter().filter(|t| !others(t)).cloned().collect()
                })
                .collect();
            for rider in riders {
                let terms = terms_of(&rider);
                let label = rider.site.unwrap_or(rider.qid);
                let mut fed = false;
                for (driver, own) in loops.iter_mut().zip(&own) {
                    if !own.is_disjoint(&terms) {
                        driver.followers.push(label.clone());
                        fed = true;
                    }
                }
                if !fed {
                    followers.push(label);
                }
            }
        }
        ResolvedQueryMatchingLoops {
            desc: q.desc,
            span: q.span,
            focus: q.focus,
            round: q.round,
            result: q.result,
            rounds: q.info.rounds,
            instantiations: q.info.instantiations,
            dropped: q.info.dropped,
            max_inst_rounds: q.info.max_inst_rounds,
            loops,
            followers,
            unparsed: q.info.unparsed,
        }
    }

    /// Join a query's nonlinear frontier to source: atoms and arguments in
    /// source spelling, host tags and quantifiers joined, and each atom's
    /// best location.
    pub(crate) fn resolve_nl_frontier(
        &self,
        fun: &Fun,
        q: QueryNlFrontier,
    ) -> ResolvedQueryNlFrontier {
        let f = q.frontier;
        let names = self.query_names(&f.variable_versions, true);
        let bound = |b: &Option<air::context::NlBound>| {
            b.as_ref().map(|b| ResolvedNlBound {
                value: smt_number(&b.value),
                strict: b.strict,
                fixed: b.fixed,
            })
        };
        let atoms = f
            .atoms
            .iter()
            .map(|a| {
                let hosts: Vec<ResolvedNlHost> = a
                    .hosts
                    .iter()
                    .map(|h| {
                        let term = vir::air_names::render_smt_arith(&names, &h.term);
                        if h.input {
                            ResolvedNlHost {
                                place: "input",
                                term,
                                tags: h.tags.iter().map(|t| self.tag_of(fun, t)).collect(),
                                qid: None,
                                fun: None,
                                span: None,
                                site: None,
                                role: None,
                                count: h.count,
                            }
                        } else {
                            let join = h.qid.as_ref().map(|qid| self.quantifier(fun, qid));
                            let (qfun, span, site, role) = match join {
                                Some(j) => (j.fun, j.span, j.site, j.role),
                                None => (None, None, None, None),
                            };
                            // a definition axiom has no quantifier in source:
                            // locate it at the spec function it defines
                            let span = span.or_else(|| {
                                role.filter(|r| r.starts_with("definition"))
                                    .and(qfun.as_ref())
                                    .and_then(|f| self.function_spans.get(f).cloned())
                            });
                            ResolvedNlHost {
                                place: "instance",
                                term,
                                tags: Vec::new(),
                                qid: h.qid.clone(),
                                fun: qfun,
                                span,
                                site,
                                role,
                                count: h.count,
                            }
                        }
                    })
                    .collect();
                let (span, span_basis) = best_location(&hosts, &q.span);
                ResolvedNlAtom {
                    atom: vir::air_names::render_smt_arith(&names, &a.atom),
                    smt: a.atom.clone(),
                    kind: a.kind.clone(),
                    current: a.current,
                    rounds: a.rounds,
                    value: smt_number(&a.value),
                    from_args: smt_number(&a.from_args),
                    lower: bound(&a.lower),
                    upper: bound(&a.upper),
                    args: a
                        .args
                        .iter()
                        .map(|t| ResolvedNlTerm {
                            term: vir::air_names::render_smt_arith(&names, &t.term),
                            smt: t.term.clone(),
                            value: smt_number(&t.value),
                            lower: bound(&t.lower),
                            upper: bound(&t.upper),
                        })
                        .collect(),
                    hosts,
                    span,
                    span_basis,
                }
            })
            .collect();
        ResolvedQueryNlFrontier {
            desc: q.desc,
            span: q.span,
            focus: q.focus,
            round: q.round,
            result: q.result,
            kind: q.kind,
            solver_result: f.result,
            reason: f.reason,
            enabled: f.enabled,
            checks: f.checks,
            rounds: f.rounds,
            punts: f.punts,
            last: f.last,
            atoms,
            omitted: f.omitted,
            truncated: f.truncated,
            unparsed: f.unparsed,
        }
    }
}

/// The best location among an atom's hosts: a hypothesis clause, then the
/// goal of the query (whose span is the query's), then a quantifier written
/// in source or a spec function's definition, then an axiom with a span.
fn best_location(hosts: &[ResolvedNlHost], query_span: &str) -> (Option<String>, Option<String>) {
    let input_tags = || hosts.iter().filter(|h| h.place == "input").flat_map(|h| h.tags.iter());
    if let Some(t) = input_tags().find(|t| {
        matches!(t.kind.as_str(), "requires" | "type_invariant" | "trait_bound") && t.span.is_some()
    }) {
        return (t.span.clone(), Some(t.kind.clone()));
    }
    if input_tags().any(|t| matches!(t.kind.as_str(), "query" | "goal")) {
        return (Some(query_span.to_string()), Some("goal".to_string()));
    }
    if let Some(h) = hosts
        .iter()
        .find(|h| h.place == "instance" && h.span.is_some() && h.fun.as_deref() != Some("prelude"))
    {
        return (h.span.clone(), Some(h.role.unwrap_or("quantifier").to_string()));
    }
    if let Some(t) = input_tags().find(|t| t.kind == "axiom" && t.span.is_some()) {
        return (t.span.clone(), Some("axiom".to_string()));
    }
    (None, None)
}

/// A number from a solver reply as text. cvc5 prints a rational as `-5` or
/// `1/2`, which passes through; the SMT-LIB spellings `(- 5)` and `(/ 1 2)`
/// read the same.
fn smt_number(s: &str) -> String {
    let t = s.trim();
    if let Some(inner) = t.strip_prefix("(- ").and_then(|r| r.strip_suffix(')')) {
        let v = smt_number(inner);
        return match v.strip_prefix('-') {
            Some(positive) => positive.to_string(),
            None => format!("-{v}"),
        };
    }
    if let Some(inner) = t.strip_prefix("(/ ").and_then(|r| r.strip_suffix(')')) {
        if let Some((n, d)) = inner.split_once(' ') {
            return format!("{}/{}", smt_number(n), smt_number(d));
        }
    }
    t.to_string()
}

/// The exhaustive wire spelling of a recorded encoder role.
fn role_name(role: &vir::sst::QuantRole) -> &'static str {
    use vir::sst::QuantRole::*;
    match role {
        Definition => "definition",
        DefinitionUnfold => "definition_unfold",
        DefinitionBase => "definition_base",
        FuelDefaults => "fuel_defaults",
        ReturnTypeInvariant => "return_type_invariant",
    }
}

/// Describe a quantifier using its owning assertion and source span.
fn quantifier_site(inside: &Option<ResolvedTag>, span: &Option<String>) -> Option<String> {
    let kind = inside.as_ref().map(|i| i.kind.as_str()).unwrap_or("");
    let owner = inside.as_ref().and_then(|i| i.owner.clone());
    Some(match (kind, owner, span.clone()) {
        ("requires", _, Some(at)) => format!("the quantifier in the requires clause at {at}"),
        ("type_invariant", _, Some(at)) => {
            format!("the quantifier in the type invariant at {at}")
        }
        ("trait_bound", _, Some(at)) => format!("the quantifier in the trait bound at {at}"),
        ("axiom", Some(o), _) => format!("the broadcast axiom `{o}`"),
        ("axiom", None, Some(at)) => format!("the axiom at {at}"),
        (_, _, Some(at)) => format!("the quantifier at {at}"),
        (_, Some(o), None) => format!("a quantifier in `{o}`"),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unknown_culprits_put_source_spans_first_and_the_prelude_last() {
        let quantifier = |span: Option<&str>| Quantifier {
            fun: "lib::f".to_owned(),
            span: span.map(str::to_owned),
            tag: None,
            role: None,
            type_binders: Vec::new(),
        };
        let table = Quantifiers(HashMap::from([
            ("user_lib__f_0".to_owned(), quantifier(Some("lib.rs:3:9: 3:40 (#0)"))),
            ("internal_lib__f_definition".to_owned(), quantifier(None)),
        ]));
        let reason = air::context::UnknownReason {
            reason: "incomplete".to_owned(),
            incomplete_id: Some("QUANTIFIERS".to_owned()),
            culprit_qids: [
                "prelude_box_unbox_int",
                "internal_lib__f_definition",
                "unmapped",
                "prelude_fuel_defaults",
                "user_lib__f_0",
            ]
            .map(str::to_owned)
            .to_vec(),
        };
        let resolved = table.resolve_unknown("desc", "span", reason);
        let qids: Vec<&str> = resolved.culprits.iter().map(|c| c.qid.as_str()).collect();
        assert_eq!(
            qids,
            [
                "user_lib__f_0",
                "internal_lib__f_definition",
                "unmapped",
                "prelude_box_unbox_int",
                "prelude_fuel_defaults",
            ]
        );
        assert_eq!(resolved.culprits[4].role, Some("fuel_defaults"));
    }

    #[test]
    fn smt_numbers_read_as_numbers() {
        assert_eq!(smt_number("5"), "5");
        assert_eq!(smt_number("-5"), "-5");
        assert_eq!(smt_number("1/2"), "1/2");
        assert_eq!(smt_number("(- 5)"), "-5");
        assert_eq!(smt_number("(/ 1 2)"), "1/2");
        assert_eq!(smt_number("(- (/ 1 2))"), "-1/2");
    }

    fn host(place: &'static str, tags: Vec<ResolvedTag>, span: Option<&str>) -> ResolvedNlHost {
        ResolvedNlHost {
            place,
            term: "(x * y)".to_string(),
            tags,
            qid: None,
            fun: (place == "instance").then(|| "crate::area".to_string()),
            span: span.map(str::to_string),
            site: None,
            role: (place == "instance").then_some("definition"),
            count: 1,
        }
    }

    fn tag(kind: &str, span: Option<&str>) -> ResolvedTag {
        ResolvedTag {
            tag: "t".to_string(),
            kind: kind.to_string(),
            owner: None,
            span: span.map(str::to_string),
        }
    }

    #[test]
    fn location_prefers_hypotheses_then_the_goal_then_definitions() {
        let q = "src/a.rs:10:1: 20:2 (#0)";
        let def = host("instance", vec![], Some("src/a.rs:3:1: 3:30 (#0)"));
        let goal = host("input", vec![tag("query", None)], None);
        let req = host("input", vec![tag("requires", Some("src/a.rs:11:9: 11:20 (#0)"))], None);
        assert_eq!(
            best_location(&[def.clone(), goal.clone(), req], q),
            (Some("src/a.rs:11:9: 11:20 (#0)".to_string()), Some("requires".to_string()))
        );
        assert_eq!(
            best_location(&[def.clone(), goal], q),
            (Some(q.to_string()), Some("goal".to_string()))
        );
        assert_eq!(
            best_location(&[def], q),
            (Some("src/a.rs:3:1: 3:30 (#0)".to_string()), Some("definition".to_string()))
        );
        // the prelude's own definitions are no location
        let mut prelude = host("instance", vec![], Some("x"));
        prelude.fun = Some("prelude".to_string());
        assert_eq!(best_location(&[prelude], q), (None, None));
    }

    #[test]
    fn a_definition_host_is_located_at_its_spec_function() {
        let qid = "internal_crate__area_definition";
        let def_span = "src/a.rs:3:1: 3:40 (#0)";
        let symbols = Symbols {
            hypotheses: HashMap::new(),
            quantifiers: HashMap::from([(
                qid.to_string(),
                Quantifier {
                    fun: "crate::area".to_string(),
                    span: None,
                    tag: None,
                    role: Some("definition"),
                    type_binders: Vec::new(),
                },
            )]),
            axiom_owners: HashMap::new(),
            internal_qid_owners: HashMap::new(),
            source_names: HashMap::new(),
            function_spans: HashMap::from([("crate::area".to_string(), def_span.to_string())]),
            crate_name: "crate".to_string(),
        };
        let atom = air::context::NlAtom {
            atom: "(* h w)".to_string(),
            kind: "product".to_string(),
            hosts: vec![air::context::NlHost {
                input: false,
                term: "(Mul w h)".to_string(),
                qid: Some(qid.to_string()),
                count: 1,
                ..Default::default()
            }],
            ..Default::default()
        };
        let query = QueryNlFrontier {
            desc: "function body check".to_string(),
            span: "src/a.rs:5:1: 5:30 (#0)".to_string(),
            focus: None,
            round: 0,
            result: "invalid".to_string(),
            kind: "recommends",
            frontier: air::context::NlFrontier { atoms: vec![atom], ..Default::default() },
        };
        let fun = std::sync::Arc::new(vir::ast::FunX {
            path: std::sync::Arc::new(vir::ast::PathX {
                krate: vir::ast::CrateId::Internal,
                segments: std::sync::Arc::new(vec![std::sync::Arc::new("big".to_string())]),
            }),
        });
        let r = symbols.resolve_nl_frontier(&fun, query);
        assert_eq!(r.kind, "recommends");
        let a = &r.atoms[0];
        assert_eq!(a.hosts[0].span.as_deref(), Some(def_span));
        assert_eq!(
            (a.span.as_deref(), a.span_basis.as_deref()),
            (Some(def_span), Some("definition"))
        );
    }

    #[test]
    fn idle_axioms_are_the_ones_that_did_no_work() {
        // an axiom in scope that no lemma used and no core holds
        assert!(is_idle_axiom(&[tag("axiom", None)], 0, Some(false)));
        assert!(is_idle_axiom(&[tag("prelude", None)], 0, None));
        assert!(is_idle_axiom(&[tag("anonymous_axiom", None), tag("axiom", None)], 0, None));
        // an axiom that did work, or that the core holds, is listed
        assert!(!is_idle_axiom(&[tag("axiom", None)], 1, Some(false)));
        assert!(!is_idle_axiom(&[tag("axiom", None)], 0, Some(true)));
        // hypotheses and the goal are listed whatever they did
        assert!(!is_idle_axiom(&[tag("requires", None)], 0, Some(false)));
        assert!(!is_idle_axiom(&[tag("fuel", None)], 0, None));
        assert!(!is_idle_axiom(&[tag("query", None)], 0, Some(false)));
        // a merged row counts as idle only if every tag of it does
        assert!(!is_idle_axiom(&[tag("axiom", None), tag("requires", None)], 0, None));
        // a row without tags is listed rather than lost in the count
        assert!(!is_idle_axiom(&[], 0, None));
    }

    #[test]
    fn ablation_groups_only_a_function_or_broadcast_axiom() {
        use air::def::ProvenanceTag;
        use std::sync::Arc;
        let quantifier = |fun: &str, span: Option<&str>, role: Option<&'static str>| Quantifier {
            fun: fun.to_owned(),
            span: span.map(str::to_owned),
            tag: None,
            role,
            type_binders: Vec::new(),
        };
        let lemma = ProvenanceTag::Axiom(Arc::new("crate!lemma.".to_owned()));
        let resolve = ProvenanceTag::Axiom(Arc::new("crate!P.resolved".to_owned()));
        let symbols = Symbols {
            hypotheses: HashMap::new(),
            quantifiers: HashMap::from([
                (
                    "internal_crate__area_definition".to_owned(),
                    quantifier("crate::area", None, Some("definition")),
                ),
                ("internal_crate__area_box".to_owned(), quantifier("crate::area", None, None)),
                (
                    "user_crate__lemma_0".to_owned(),
                    quantifier("crate::lemma", Some("src/a.rs:9:5: 9:40 (#0)"), None),
                ),
            ]),
            axiom_owners: HashMap::from([
                (lemma.to_symbol(), "crate::lemma".to_owned()),
                (resolve.to_symbol(), format!("crate::P{}", vir::def::RESOLVE_AXIOM_OWNER_SUFFIX)),
            ]),
            internal_qid_owners: HashMap::new(),
            source_names: HashMap::new(),
            function_spans: HashMap::new(),
            crate_name: "crate".to_owned(),
        };
        let forall = |qid: Option<&str>| -> air::ast::Expr {
            let x = Arc::new(air::ast::BinderX {
                name: Arc::new("x".to_owned()),
                a: Arc::new(air::ast::TypX::Int),
            });
            let bind = air::ast::BindX::Quant(
                air::ast::Quant::Forall,
                Arc::new(vec![x]),
                Arc::new(Vec::new()),
                qid.map(|qid| Arc::new(qid.to_owned())),
            );
            Arc::new(air::ast::ExprX::Bind(Arc::new(bind), air::ast_util::mk_true()))
        };
        let axiom = |tag: Option<ProvenanceTag>, expr: air::ast::Expr| air::ast::Axiom {
            named: None,
            tag,
            expr,
        };
        let group = |axiom: &air::ast::Axiom| symbols.axiom_group(axiom).map(str::to_owned);
        // a broadcast lemma, by its tag
        let user = forall(Some("user_crate__lemma_0"));
        assert_eq!(
            group(&axiom(Some(lemma.clone()), user.clone())),
            Some("crate::lemma".to_owned())
        );
        // a datatype's resolve axiom is tagged too, but is the encoding's
        assert_eq!(group(&axiom(Some(resolve.clone()), forall(None))), None);
        assert_eq!(symbols.broadcast_owner(&resolve), None);
        // a definition, plain or fuel-guarded
        let definition = forall(Some("internal_crate__area_definition"));
        assert_eq!(group(&axiom(None, definition.clone())), Some("crate::area".to_owned()));
        let guarded = air::ast_util::mk_implies(&air::ast_util::str_var("fuel_bool"), &definition);
        assert_eq!(group(&axiom(None, guarded)), Some("crate::area".to_owned()));
        // a quantifier the user wrote, even untagged
        assert_eq!(group(&axiom(None, user)), Some("crate::lemma".to_owned()));
        // the encoding's own: made while encoding `area` but with no role, or
        // not in the table at all (prelude, fuel defaults, no qid)
        assert_eq!(group(&axiom(None, forall(Some("internal_crate__area_box")))), None);
        assert_eq!(group(&axiom(None, forall(Some("prelude_box_unbox_int")))), None);
        assert_eq!(group(&axiom(None, forall(Some("fuel_defaults")))), None);
        assert_eq!(group(&axiom(None, forall(None))), None);
    }
}
