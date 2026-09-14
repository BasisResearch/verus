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

/// One `check-sat` under `-V nl-frontier`, as cvc5 reported it: solver
/// terms, tag symbols and qids, not yet joined to source.
#[derive(Clone, Debug)]
pub struct QueryNlFrontier {
    pub desc: String,
    pub span: String,
    /// `body`, `recommends`, `expanded`, ...: a recommends rerun or an
    /// expanded recheck shares the body check's `desc` and `span`
    pub kind: &'static str,
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
    /// Friendly function name -> the function's span, when recorded (see
    /// `with_function_spans`).
    function_spans: HashMap<String, String>,
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
            function_spans: HashMap::new(),
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

    /// The recorded source names, with this query's SSA versions added:
    /// versions are query-local, and a display must keep assignment identity.
    fn names_with_versions<'a>(
        &'a self,
        variable_versions: &air::context::VariableVersions,
    ) -> std::borrow::Cow<'a, vir::air_names::SourceNames> {
        let mut source_names = std::borrow::Cow::Borrowed(&self.source_names);
        for (symbol, (base, version)) in variable_versions {
            if let Some(name) = vir::air_names::source_symbol(&source_names, base) {
                source_names.to_mut().insert(
                    symbol.clone(),
                    vir::air_names::SourceName::Symbol(format!("{name} (version {version})")),
                );
            }
        }
        source_names
    }

    pub(crate) fn resolve(&self, fun: &Fun, q: QueryProvenance) -> ResolvedQueryProvenance {
        let is_hyp_kind =
            |k: &str| matches!(k, "requires" | "type_invariant" | "fuel" | "trait_bound");
        let source_names = self.names_with_versions(&q.variable_versions);
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

    /// Join a query's nonlinear frontier to source: atoms and arguments in
    /// source spelling, host tags and quantifiers joined, and each atom's
    /// best location.
    pub(crate) fn resolve_nl_frontier(
        &self,
        fun: &Fun,
        q: QueryNlFrontier,
    ) -> ResolvedQueryNlFrontier {
        let f = q.frontier;
        let names = self.names_with_versions(&f.variable_versions);
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
                },
            )]),
            axiom_owners: HashMap::new(),
            source_names: HashMap::new(),
            function_spans: HashMap::from([("crate::area".to_string(), def_span.to_string())]),
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
}
