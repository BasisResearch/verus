//! Owned source metadata used by both batch verification and resident rechecks.
use std::collections::HashMap;
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
        let air_source_names = &self.source_names;
        let tag_of = |fun: &Fun, symbol: &str| self.tag_of(fun, symbol);
        let is_hyp_kind =
            |k: &str| matches!(k, "requires" | "type_invariant" | "fuel" | "trait_bound");
        // SSA versions are query-local. Preserve assignment identity in the display.
        let mut source_names = std::borrow::Cow::Borrowed(air_source_names);
        for (symbol, (base, version)) in &q.variable_versions {
            if let Some(name) = vir::air_names::source_symbol(&source_names, base) {
                source_names.to_mut().insert(
                    symbol.clone(),
                    vir::air_names::SourceName::Symbol(format!("{name} (version {version})")),
                );
            }
        }
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
                let QuantifierJoin { fun: fun_name, span, inside, site, role } =
                    self.quantifier(fun, qid);
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
            round: q.round,
            result: q.result,
            rounds: q.pressure.rounds,
            refutation: q.pressure.refutation,
            quantifiers,
            unparsed: q.pressure.unparsed,
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

#[cfg(test)]
mod tests {
    use super::{ResolvedTag, is_idle_axiom};

    fn tag(kind: &str) -> ResolvedTag {
        ResolvedTag { tag: "t".to_string(), kind: kind.to_string(), owner: None, span: None }
    }

    #[test]
    fn idle_axioms_are_the_ones_that_did_no_work() {
        // an axiom in scope that no lemma used and no core holds
        assert!(is_idle_axiom(&[tag("axiom")], 0, Some(false)));
        assert!(is_idle_axiom(&[tag("prelude")], 0, None));
        assert!(is_idle_axiom(&[tag("anonymous_axiom"), tag("axiom")], 0, None));
        // an axiom that did work, or that the core holds, is listed
        assert!(!is_idle_axiom(&[tag("axiom")], 1, Some(false)));
        assert!(!is_idle_axiom(&[tag("axiom")], 0, Some(true)));
        // hypotheses and the goal are listed whatever they did
        assert!(!is_idle_axiom(&[tag("requires")], 0, Some(false)));
        assert!(!is_idle_axiom(&[tag("fuel")], 0, None));
        assert!(!is_idle_axiom(&[tag("query")], 0, Some(false)));
        // a merged row counts as idle only if every tag of it does
        assert!(!is_idle_axiom(&[tag("axiom"), tag("requires")], 0, None));
        // a row without tags is listed rather than lost in the count
        assert!(!is_idle_axiom(&[], 0, None));
    }
}
