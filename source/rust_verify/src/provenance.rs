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

/// One unknown `check-sat` under `-V matching-loops`, as cvc5 reported it.
/// Symbols and SMT terms, not yet joined to source.
#[derive(Clone, Debug)]
pub struct QueryMatchingLoops {
    pub desc: String,
    pub span: String,
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
    pub context: Option<String>,
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
    /// instantiations/round), or bounded. The depth is the solver's, so it
    /// counts the boxes `term_ladder` leaves out.
    pub growth_rate: String,
    /// the quantifier's first trigger, in source spelling
    pub trigger: String,
    /// every rung generalised, then every rung after the first, with `_n`
    /// where they differ: `f(_0)  →  f(g(_0))`
    pub term_shape: String,
    /// what each rung wraps around the previous rung's growing subterm,
    /// generalised over the chain, `_0` marking that subterm: `cons(_1, _0)`
    #[serde(skip_serializing_if = "Option::is_none")]
    pub growth_context: Option<String>,
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
    /// most confident first
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

struct Hypothesis {
    kind: String,
    span: String,
}
struct Quantifier {
    fun: String,
    span: Option<String>,
    tag: Option<air::def::ProvenanceTag>,
    role: Option<&'static str>,
}

const PRELUDE_QID_PREFIX: &str = "prelude_";
/// The prelude writes this one by hand, so it has no `qid_map` entry.
const FUEL_DEFAULTS_QID: &str = "prelude_fuel_defaults";

/// Where a quantifier is written, joined back to source.
struct QuantifierSite {
    fun: Option<String>,
    span: Option<String>,
    inside: Option<ResolvedTag>,
    site: Option<String>,
    role: Option<&'static str>,
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

/// A span as `file:line:col`, without its directory or byte range.
fn span_short(s: &Option<String>) -> Option<String> {
    s.as_ref()
        .map(|s| s.rsplit('/').next().unwrap_or(s).split(" (#").next().unwrap_or(s).to_string())
}

/// No compiler context, source map, or VIR expression is retained here.
pub(crate) struct Symbols {
    hypotheses: HashMap<Fun, Vec<Hypothesis>>,
    quantifiers: HashMap<String, Quantifier>,
    axiom_owners: HashMap<String, String>,
    source_names: vir::air_names::SourceNames,
}

impl Symbols {
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
        let quantifiers = global
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
                    },
                )
            })
            .collect();
        Self {
            hypotheses,
            quantifiers,
            axiom_owners: global.axiom_owners.borrow().clone(),
            source_names,
        }
    }

    /// One tag from a solver reply, joined back to source.
    fn tag_of(&self, fun: &Fun, symbol: &str) -> ResolvedTag {
        let hyp_map = &self.hypotheses;
        let qid_map = &self.quantifiers;
        let axiom_owners = &self.axiom_owners;
        let mut r =
            ResolvedTag { tag: symbol.to_string(), kind: String::new(), owner: None, span: None };
        match air::def::ProvenanceTag::from_symbol(symbol) {
            Some(air::def::ProvenanceTag::Hyp(air::def::HypId(k))) => {
                match hyp_map.get(fun).and_then(|hs| hs.get(k as usize)) {
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
                if let Some(owner) = axiom_owners.get(symbol) {
                    r.kind = "axiom".to_string();
                    r.owner = Some(owner.clone());
                } else if let Some(info) = qid_map.get(ident) {
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

    /// The source names for one query's terms: SSA versions are query-local,
    /// so each versioned symbol shows its assignment version.
    fn query_source_names(
        &self,
        versions: &air::context::VariableVersions,
    ) -> std::borrow::Cow<'_, vir::air_names::SourceNames> {
        let mut source_names = std::borrow::Cow::Borrowed(&self.source_names);
        for (symbol, (base, version)) in versions {
            if let Some(name) = vir::air_names::source_symbol(&source_names, base) {
                source_names.to_mut().insert(
                    symbol.clone(),
                    vir::air_names::SourceName::Symbol(format!("{name} (version {version})")),
                );
            }
        }
        source_names
    }

    /// Where the quantifier `qid` is written and why it exists, as far as the
    /// encoders recorded it.
    fn describe_quantifier(&self, fun: &Fun, qid: &str) -> QuantifierSite {
        match self.quantifiers.get(qid) {
            Some(info) => {
                let inside = info.tag.as_ref().map(|t| self.tag_of(fun, &t.to_symbol()));
                let site = quantifier_site(&inside, &span_short(&info.span));
                QuantifierSite {
                    fun: Some(info.fun.clone()),
                    span: info.span.clone(),
                    inside,
                    site,
                    role: info.role,
                }
            }
            None => {
                let inside = None;
                QuantifierSite {
                    fun: qid.starts_with(PRELUDE_QID_PREFIX).then(|| "prelude".to_string()),
                    span: None,
                    site: quantifier_site(&inside, &None),
                    inside,
                    role: (qid == FUEL_DEFAULTS_QID).then_some("fuel_defaults"),
                }
            }
        }
    }

    pub(crate) fn resolve(&self, fun: &Fun, q: QueryProvenance) -> ResolvedQueryProvenance {
        let tag_of = |fun: &Fun, symbol: &str| self.tag_of(fun, symbol);
        let is_hyp_kind =
            |k: &str| matches!(k, "requires" | "type_invariant" | "fuel" | "trait_bound");
        // SSA versions are query-local. Preserve assignment identity in the display.
        let source_names = self.query_source_names(&q.variable_versions);
        let mut hypotheses: Vec<ResolvedTag> = Vec::new();
        let mut sources: Vec<Vec<ResolvedTag>> = Vec::new();
        let mut axioms_in_scope = 0usize;
        for list in q.sources.iter() {
            let tags: Vec<ResolvedTag> = list.iter().map(|t| tag_of(fun, t)).collect();
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
                let QuantifierSite { fun: fun_name, span, inside, site, role } =
                    self.describe_quantifier(fun, qid);
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
                        .map(|v| vir::air_names::render_vector(&source_names, v))
                        .collect(),
                    vectors: vectors.clone(),
                }
            })
            .collect();
        ResolvedQueryProvenance {
            desc: q.desc,
            span: q.span,
            round: q.round,
            result: q.result,
            hypotheses,
            sources,
            axioms_in_scope,
            instantiations,
            unparsed: q.unparsed,
        }
    }

    pub(crate) fn resolve_matching_loops(
        &self,
        fun: &Fun,
        q: QueryMatchingLoops,
    ) -> ResolvedQueryMatchingLoops {
        let names = self.query_source_names(&q.info.variable_versions);
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
                let QuantifierSite { fun: fun_name, span, inside: _, site, role } =
                    self.describe_quantifier(fun, &l.qid);
                let growth_rate = match l.growth.as_str() {
                    "linear-depth" => {
                        format!("linear-depth (+{:.2} solver term depth/round)", l.depth_per_round)
                    }
                    "exponential-fanout" => format!(
                        "exponential-fanout (x{:.2} instantiations/round)",
                        l.fanout_per_round
                    ),
                    other => other.to_string(),
                };
                let via = l
                    .via
                    .iter()
                    .map(|qid| {
                        self.describe_quantifier(fun, qid).site.unwrap_or_else(|| qid.clone())
                    })
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
                        .as_ref()
                        .map(|c| vir::air_names::render_term(&names, c)),
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
