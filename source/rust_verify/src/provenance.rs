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

    pub(crate) fn resolve(&self, fun: &Fun, q: QueryProvenance) -> ResolvedQueryProvenance {
        const PRELUDE_QID_PREFIX: &str = "prelude_";
        /// The prelude writes this one by hand, so it has no `qid_map` entry.
        const FUEL_DEFAULTS_QID: &str = "prelude_fuel_defaults";
        let hyp_map = &self.hypotheses;
        let qid_map = &self.quantifiers;
        let axiom_owners = &self.axiom_owners;
        let air_source_names = &self.source_names;
        let tag_of = |fun: &Fun, symbol: &str| -> ResolvedTag {
            let mut r = ResolvedTag {
                tag: symbol.to_string(),
                kind: String::new(),
                owner: None,
                span: None,
            };
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
        };
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
                let span_short = |s: &Option<String>| -> Option<String> {
                    s.as_ref().map(|s| {
                        s.rsplit('/')
                            .next()
                            .unwrap_or(s)
                            .split(" (#")
                            .next()
                            .unwrap_or(s)
                            .to_string()
                    })
                };
                let (fun_name, span, inside, role) = match qid_map.get(qid) {
                    Some(info) => (
                        Some(info.fun.clone()),
                        info.span.clone(),
                        info.tag.as_ref().map(|t| tag_of(fun, &t.to_symbol())),
                        info.role,
                    ),
                    None => (
                        qid.starts_with(PRELUDE_QID_PREFIX).then(|| "prelude".to_string()),
                        None,
                        None,
                        (qid.as_str() == FUEL_DEFAULTS_QID).then_some("fuel_defaults"),
                    ),
                };
                let site = quantifier_site(&inside, &span_short(&span));
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
