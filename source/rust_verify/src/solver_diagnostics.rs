//! What cvc5 said about each check that failed, joined back to source and
//! printed after verification, one block per failed check:
//!
//! ```text
//! === verus-diagnostics begin ===
//! function: crate::m::f
//! ...
//! === verus-diagnostics end ===
//! ```
//!
//! The blocks go to stderr and nothing else prints those two lines, so a
//! reader (or a harness) can cut them out with a line filter. Under JSON
//! diagnostics (`--error-format=json`, as cargo runs Verus) each block is
//! one note diagnostic instead, its message the block, so it shows as
//! `note: === verus-diagnostics begin ===` followed by the rest.
//!
//! What a block holds depends on how the check failed. A check that ran out
//! of budget says which quantifiers fed themselves and which were
//! instantiated most. A goal reported as failing says which nonlinear terms
//! the solver could not settle and which equalities it held between the
//! goal's terms, and where the work went only when a loop or one of the
//! crate's own quantifiers dominated it. Every section is capped, so a block
//! stays a screenful.
//!
//! Nothing here changes what is verified. The solver keeps its records
//! without spending budget on them, and they are read only after a check has
//! failed (see `air::diagnostics`).

use air::diagnostics::{
    EgraphReply, FailureDiagnostics, InstCycles, InstPressure, MatchingLoop, NlFrontier,
};
use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;
use vir::air_names::{SourceName, SourceNames, render_smt_arith, render_term, source_symbol};
use vir::ast::Fun;
use vir::ast_util::fun_as_friendly_rust_name;
use vir::sst::QuantRole;

/// The first line of every block.
pub const BEGIN: &str = "=== verus-diagnostics begin ===";
/// The last line of every block.
pub const END: &str = "=== verus-diagnostics end ===";

const MAX_LOOPS: usize = 3;
const MAX_CYCLES: usize = 3;
const MAX_LADDER: usize = 4;
const MAX_QUANTIFIERS: usize = 5;
const MAX_CULPRITS: usize = 5;
const MAX_NL_ATOMS: usize = 4;
const MAX_EQUALITIES: usize = 6;
/// A rendered term longer than this is cut, with `…` marking the cut.
const MAX_TERM: usize = 160;
/// The same for one rung of a matching loop's ladder, several to a line.
const MAX_RUNG: usize = 60;
/// How cvc5 names the witnesses it makes for a quantifier (a `forall` in a
/// goal, an `exists` in a hypothesis), and what a block calls them.
const SKOLEM_PREFIX: (&str, &str) = ("@quantifiers_skolemize_", "sk");

/// How Verus reported the failed check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Outcome {
    /// "Resource limit (rlimit) exceeded"
    ResourceLimit,
    /// An assertion, precondition or postcondition reported as failing.
    Failed,
}

/// One failed check, as the verifier saw it.
pub(crate) struct FailedQuery {
    pub fun: Fun,
    /// What the check was (`context.desc`), e.g. "function body check".
    pub desc: String,
    /// The span of the function the check is about.
    pub span: String,
    /// Where the first failure was reported, when Verus pointed at one.
    pub failed_at: Option<String>,
    pub outcome: Outcome,
    pub diagnostics: FailureDiagnostics,
}

/// Where a quantifier came from, by `:qid`.
struct Quantifier {
    fun: String,
    span: Option<String>,
    role: Option<QuantRole>,
}

/// What the solver's names mean in source: the quantifiers by `:qid`, the
/// symbols the encoders recorded, and each function's span.
pub(crate) struct Joiner {
    quantifiers: HashMap<String, Quantifier>,
    names: SourceNames,
    function_spans: HashMap<String, String>,
    cwd: Option<String>,
    /// `krate::`, which the crate's own names are shown without
    own_prefix: String,
}

impl Joiner {
    /// Read the crate's quantifiers and recorded names, once every module's
    /// context has been merged into `global`.
    pub(crate) fn capture(
        global: &vir::context::GlobalCtx,
        functions: &[vir::ast::Function],
    ) -> Self {
        let quantifiers = global
            .qid_map
            .borrow()
            .iter()
            .map(|(qid, info)| {
                let q = Quantifier {
                    fun: fun_as_friendly_rust_name(&info.fun),
                    span: info.user.as_ref().map(|user| user.span.as_string.clone()),
                    role: info.role.clone(),
                };
                (qid.clone(), q)
            })
            .collect();
        let function_spans = functions
            .iter()
            .map(|f| (fun_as_friendly_rust_name(&f.x.name), f.span.as_string.clone()))
            .collect();
        let cwd = std::env::current_dir().ok().map(|d| d.to_string_lossy().into_owned() + "/");
        let own_prefix =
            format!("{}::", vir::def::krate_to_string_ignore_stable_id(&global.crate_name));
        // the crate's own items read as source inside the crate writes them
        let mut names = global.air_source_names.borrow().clone();
        for name in names.values_mut() {
            match name {
                SourceName::Symbol(n) | SourceName::Function { name: n, .. } => {
                    if let Some(rest) = n.strip_prefix(&own_prefix) {
                        *n = rest.to_string();
                    }
                }
                _ => {}
            }
        }
        Joiner { quantifiers, names, function_spans, cwd, own_prefix }
    }

    /// A function's name, without the crate's own name for its own items.
    fn fun_name<'a>(&self, name: &'a str) -> &'a str {
        name.strip_prefix(&self.own_prefix).unwrap_or(name)
    }

    /// Whether `qid` is a quantifier the user wrote in this crate. Only
    /// written ones count: `qid_map` files every quantifier made while a
    /// function was being encoded under that function, trait-impl and box
    /// axioms included.
    fn own(&self, qid: &str) -> bool {
        Self::user_written(qid)
            && self.quantifiers.get(qid).is_some_and(|q| q.fun.starts_with(&self.own_prefix))
    }

    /// Whether `qid` stands for something written in source that the user
    /// can act on: a quantifier the user wrote, or one Verus made for a
    /// definition or contract of this crate. Otherwise it is part of the
    /// encoding (boxing, datatype accessors and constructors, trait impls,
    /// the prelude, vstd's definitions).
    fn meaningful(&self, qid: &str) -> bool {
        Self::user_written(qid)
            || self
                .quantifiers
                .get(qid)
                .is_some_and(|q| q.role.is_some() && q.fun.starts_with(&self.own_prefix))
    }

    /// A span as `path:line:col`, relative to the working directory when it
    /// is under it.
    fn short_span(&self, span: &str) -> String {
        // `/dir/file.rs:12:5: 12:20 (#0)`
        let start = span.split(": ").next().unwrap_or(span);
        let start = start.split(" (#").next().unwrap_or(start);
        match &self.cwd {
            Some(cwd) => start.strip_prefix(cwd.as_str()).unwrap_or(start).to_string(),
            None => start.to_string(),
        }
    }

    /// Whether the user wrote the quantifier `qid` (a `forall` or `exists`
    /// in source, a broadcast lemma), as opposed to one Verus generated.
    fn user_written(qid: &str) -> bool {
        qid.starts_with(air::profiler::USER_QUANT_PREFIX)
    }

    /// The quantifier `qid` in prose, with where it is written when known.
    fn quantifier(&self, qid: &str) -> String {
        match self.quantifiers.get(qid) {
            Some(Quantifier { span: Some(span), fun, .. }) => {
                format!("the quantifier at {} (in `{}`)", self.short_span(span), self.fun_name(fun))
            }
            Some(Quantifier { fun: full, role: Some(role), .. }) => {
                let fun = self.fun_name(full);
                let at = |what: String| match self.function_spans.get(full) {
                    Some(span) => format!("{what} (at {})", self.short_span(span)),
                    None => what,
                };
                match role {
                    QuantRole::Definition => at(format!("the definition of `{fun}`")),
                    QuantRole::DefinitionUnfold => {
                        at(format!("the unfolding of recursive `{fun}` (costs fuel)"))
                    }
                    QuantRole::DefinitionBase => at(format!("recursive `{fun}` at zero fuel")),
                    QuantRole::Contract => at(format!("the requires/ensures of `{fun}`")),
                    QuantRole::ReturnTypeInvariant => {
                        at(format!("the return type invariant of `{fun}`"))
                    }
                }
            }
            Some(Quantifier { fun, .. }) => {
                format!("a Verus-generated axiom for `{}` ({qid})", self.fun_name(fun))
            }
            None if qid.starts_with("prelude_") => format!("the prelude axiom `{qid}`"),
            None => format!("the Verus-generated axiom `{qid}`"),
        }
    }

    /// The recorded names, with each SSA symbol of this check named as its
    /// variable: `x` for its first version, `x (version 2)` after it was
    /// assigned twice.
    fn query_names<'a>(
        &'a self,
        versions: &air::diagnostics::VariableVersions,
    ) -> Cow<'a, SourceNames> {
        let mut names = Cow::Borrowed(&self.names);
        for (symbol, (base, version)) in versions {
            if let Some(name) = source_symbol(&names, base) {
                let name = if *version == 0 { name } else { format!("{name} (version {version})") };
                names.to_mut().insert(symbol.clone(), SourceName::Symbol(name));
            }
        }
        names
    }
}

/// `text` cut to `MAX_TERM` characters.
fn clip(text: String) -> String {
    clip_to(text, MAX_TERM)
}

/// `text` cut to `max` characters, cvc5's skolem names shortened first.
fn clip_to(text: String, max: usize) -> String {
    let text = text.replace(SKOLEM_PREFIX.0, SKOLEM_PREFIX.1);
    if text.chars().count() <= max {
        text
    } else {
        let cut: String = text.chars().take(max).collect();
        format!("{cut}…")
    }
}

/// A number as cvc5 prints it (`-5`, `1/2`), or as SMT-LIB spells it
/// (`(- 5)`, `(/ 1 2)`), in the first form.
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

/// Every failed check's block, in source order.
pub(crate) fn render_all(queries: &mut Vec<FailedQuery>, joiner: &Joiner) -> Vec<String> {
    queries.sort_by(|a, b| {
        (a.failed_at.as_ref().unwrap_or(&a.span), &a.desc)
            .cmp(&(b.failed_at.as_ref().unwrap_or(&b.span), &b.desc))
    });
    queries.iter().map(|query| render(query, joiner)).collect()
}

/// One failed check's block, delimiters included.
pub(crate) fn render(query: &FailedQuery, joiner: &Joiner) -> String {
    let d = &query.diagnostics;
    let names = joiner.query_names(&d.variable_versions);
    let mut out = String::new();
    let o = &mut out;
    let _ = writeln!(o, "{BEGIN}");
    let _ = writeln!(o, "function: {}", joiner.fun_name(&fun_as_friendly_rust_name(&query.fun)));
    let _ = writeln!(o, "check: {}", query.desc);
    let at = query.failed_at.as_ref().unwrap_or(&query.span);
    let _ = writeln!(o, "at: {}", joiner.short_span(at));
    let reason = d.unknown_reason.as_ref();
    let incomplete = reason.and_then(|r| r.incomplete_id.as_deref());
    let outcome = match (query.outcome, d.result.as_str()) {
        (Outcome::ResourceLimit, _) => "the solver ran out of its resource budget (rlimit)".into(),
        (Outcome::Failed, "unknown") => format!(
            "the solver gave up{}, so the goal is unproved, not refuted",
            incomplete.map(|i| format!(" (incomplete: {i})")).unwrap_or_default()
        ),
        (Outcome::Failed, _) => {
            "the solver found a model of the hypotheses in which the goal is false".into()
        }
    };
    let _ = writeln!(o, "outcome: {outcome}");
    if let Some(effort) = d.check_effort.as_ref().filter(|e| e.unparsed.is_none()) {
        let rounds = if effort.inst_rounds == 1 { "round" } else { "rounds" };
        let _ = writeln!(
            o,
            "effort: {} resource units, {} quantifier instantiations in {} {rounds}",
            effort.resource_units, effort.instantiations, effort.inst_rounds
        );
    }

    // What to show depends on how the check failed. Out of budget, the
    // question is where the solver's work went: loops and the quantifiers
    // instantiated most. Failed (cvc5 answers `unknown` for most failed
    // goals once quantifiers are in scope, `sat` for the rest), the question
    // is what the solver knew: the nonlinear terms it could not settle and
    // the equalities it held; the work only if a loop or one of the crate's
    // own quantifiers dominated it.
    let mut next: Vec<String> = Vec::new();
    let out_of_budget = query.outcome == Outcome::ResourceLimit;
    let looped = d.matching_loops.as_ref().is_some_and(|m| !m.loops.is_empty());
    if let Some(loops) = &d.matching_loops {
        matching_loops(o, joiner, &names, &loops.loops, &mut next);
    }
    if let Some(cycles) = &d.inst_cycles {
        instance_cycles(o, joiner, cycles, &mut next);
    }
    if let Some(pressure) = &d.inst_pressure {
        instantiations(o, joiner, pressure, out_of_budget || looped, &mut next);
    }
    if let Some(reason) = reason {
        culprits(o, joiner, &reason.culprit_qids);
    }
    // Out of budget, the nonlinear terms left unsettled are where the solver
    // stopped, not why it ran out, so they are shown for failed goals only.
    if !out_of_budget {
        if let Some(frontier) = &d.nl_frontier {
            nonlinear(o, &names, frontier, &mut next);
        }
        if let Some(egraph) = &d.egraph {
            equalities(o, &names, egraph);
        }
    }
    if out_of_budget && next.is_empty() {
        next.push(
            "no loop or single quantifier stands out: the budget went to many small \
             instantiations, so split the proof into smaller lemmas, or hide the definitions \
             it does not need"
                .to_string(),
        );
    }
    let mut seen = HashSet::new();
    for step in next.iter().filter(|s| seen.insert(s.as_str())) {
        let _ = writeln!(o, "next: {step}");
    }
    let _ = writeln!(o, "{END}");
    out
}

/// The quantifiers that fed themselves. Only a quantifier the user wrote can
/// drive a loop; the prelude's and Verus's own axioms climb when a written
/// one feeds them terms, so they are listed only when no written one looped.
fn matching_loops(
    o: &mut String,
    joiner: &Joiner,
    names: &SourceNames,
    loops: &[MatchingLoop],
    next: &mut Vec<String>,
) {
    let (written, others): (Vec<&MatchingLoop>, Vec<&MatchingLoop>) =
        loops.iter().partition(|l| Joiner::user_written(&l.qid));
    // A loop among Verus's own axioms is shown only when no written one
    // looped, and only when cvc5 is fairly sure of it: they climb whenever
    // a written quantifier feeds them terms.
    let others: Vec<&MatchingLoop> = others.into_iter().filter(|l| l.confidence != "low").collect();
    let shown = if written.is_empty() { &others } else { &written };
    // one source quantifier can carry several `:qid`s: keep its first loop
    let mut seen = HashSet::new();
    let shown: Vec<&MatchingLoop> =
        shown.iter().copied().filter(|l| seen.insert(joiner.quantifier(&l.qid))).collect();
    if shown.is_empty() {
        return;
    }
    let render_to = |terms: &[String], max: usize| -> String {
        clip_to(terms.iter().map(|t| render_term(names, t)).collect::<Vec<_>>().join(", "), max)
    };
    let render = |terms: &[String]| render_to(terms, MAX_TERM);
    let _ = writeln!(o, "matching loops (a quantifier whose instances trigger itself again):");
    for l in shown.iter().take(MAX_LOOPS) {
        let growth = match l.growth.as_str() {
            "linear-depth" => format!("terms grow {:.1} deeper per round", l.depth_per_round),
            "exponential-fanout" => {
                format!("instances multiply by {:.2} per step", l.fanout_per_step)
            }
            other => other.to_string(),
        };
        let _ = writeln!(
            o,
            "  - {}: {} instances over {} rounds; {growth}; confidence {}",
            joiner.quantifier(&l.qid),
            l.instantiations,
            l.rounds,
            l.confidence
        );
        if !l.trigger.is_empty() {
            let _ = writeln!(o, "    trigger: {}", render(&l.trigger));
        }
        if !l.shape.is_empty() && !l.step.is_empty() {
            let _ = writeln!(o, "    each instance: {}  ->  {}", render(&l.shape), render(&l.step));
        }
        if !l.ladder.is_empty() {
            let mut rungs: Vec<String> =
                l.ladder.iter().take(MAX_LADDER - 1).map(|r| render_to(r, MAX_RUNG)).collect();
            if l.ladder.len() >= MAX_LADDER {
                if l.ladder_length > MAX_LADDER as u64 || l.ladder.len() > MAX_LADDER {
                    rungs.push("…".to_string());
                }
                rungs.push(render_to(&l.ladder[l.ladder.len() - 1], MAX_RUNG));
            } else if l.ladder_length > l.ladder.len() as u64 {
                rungs.push("…".to_string());
            }
            let _ = writeln!(o, "    instances: {}", rungs.join("; "));
        }
        if !l.via.is_empty() {
            let via: Vec<String> = l.via.iter().map(|q| joiner.quantifier(q)).collect();
            let _ = writeln!(o, "    through: {}", via.join("; "));
        }
    }
    if shown.len() > MAX_LOOPS {
        let _ = writeln!(o, "  ({} more)", shown.len() - MAX_LOOPS);
    }
    if !written.is_empty() && !others.is_empty() {
        let _ = writeln!(
            o,
            "  ({} Verus-generated or prelude axioms climbed along with these)",
            others.len()
        );
    }
    if !written.is_empty() {
        next.push(
            "give the looping quantifier a trigger its own instances cannot match (#[trigger]), \
             or move it into a lemma and call the lemma where it is needed"
                .to_string(),
        );
    }
}

/// The quantifiers instantiated most.
/// Quantifiers whose instances trigger one another in a cycle of two or more
/// (a single self-feeding quantifier is a matching loop, listed above), when
/// the cycle holds one of the crate's own quantifiers. Verus can give one
/// source quantifier several `:qid`s, so members are listed by where they are
/// written, once each.
fn instance_cycles(o: &mut String, joiner: &Joiner, cycles: &InstCycles, next: &mut Vec<String>) {
    if cycles.unparsed.is_some() {
        return;
    }
    let mut shown: Vec<(Vec<String>, usize, &air::diagnostics::InstCycle)> = Vec::new();
    let mut elsewhere = 0;
    for c in cycles.cycles.iter().filter(|c| c.qids.len() >= 2) {
        if !c.qids.iter().any(|q| joiner.own(q)) {
            elsewhere += usize::from(c.qids.iter().any(|q| Joiner::user_written(q)));
            continue;
        }
        let mut labels: Vec<String> = Vec::new();
        let mut generated = 0;
        for qid in &c.qids {
            if joiner.meaningful(qid) {
                let label = joiner.quantifier(qid);
                if !labels.contains(&label) {
                    labels.push(label);
                }
            } else {
                generated += 1;
            }
        }
        shown.push((labels, generated, c));
    }
    if shown.is_empty() {
        return;
    }
    let _ = writeln!(o, "quantifiers whose instances trigger each other in a cycle:");
    for (labels, generated, c) in shown.iter().take(MAX_CYCLES) {
        let _ = writeln!(
            o,
            "  - {} instances, {} times one fed another:",
            c.instantiations, c.repetitions
        );
        for label in labels {
            let _ = writeln!(o, "      {label}");
        }
        if *generated > 0 {
            let _ = writeln!(o, "      and {generated} Verus-generated or prelude axioms");
        }
    }
    if shown.len() > MAX_CYCLES {
        let _ = writeln!(o, "  ({} more)", shown.len() - MAX_CYCLES);
    }
    if elsewhere > 0 {
        let _ = writeln!(o, "  ({elsewhere} more among vstd's or other crates' quantifiers)");
    }
    next.push(
        "break the cycle: give one of its quantifiers a trigger the others' instances do not \
         produce, or prove the needed instance with an explicit lemma call"
            .to_string(),
    );
}

/// The quantifiers instantiated most, by where they are written (a source
/// quantifier with several `:qid`s is one row). Verus's generated axioms
/// (boxing, datatype accessors, the prelude) are summed in one line: they
/// climb because a written quantifier feeds them. Listed always when `all`;
/// otherwise only when one of the crate's own quantifiers took most of the
/// instances.
fn instantiations(
    o: &mut String,
    joiner: &Joiner,
    pressure: &InstPressure,
    all: bool,
    next: &mut Vec<String>,
) {
    if pressure.unparsed.is_some() || pressure.quantifiers.is_empty() {
        return;
    }
    let total: u64 = pressure.quantifiers.iter().map(|q| q.instantiations).sum();
    // label -> (instances, duplicates, whether it is the crate's own)
    let mut rows: Vec<(String, u64, u64, bool)> = Vec::new();
    let mut generated = 0;
    for q in pressure.quantifiers.iter().filter(|q| q.instantiations > 0) {
        if !q.named || !joiner.meaningful(&q.qid) {
            generated += q.instantiations;
            continue;
        }
        let label = joiner.quantifier(&q.qid);
        let duplicates = q.duplicate_eq + q.duplicate_ent + q.duplicate_lemma;
        match rows.iter_mut().find(|row| row.0 == label) {
            Some(row) => {
                row.1 += q.instantiations;
                row.2 += duplicates;
                row.3 |= joiner.own(&q.qid);
            }
            None => rows.push((label, q.instantiations, duplicates, joiner.own(&q.qid))),
        }
    }
    rows.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    let dominant = rows.first().filter(|top| top.3 && top.1 * 2 >= total);
    if rows.is_empty() || !(all || dominant.is_some()) {
        return;
    }
    let _ = writeln!(o, "most instantiated quantifiers ({total} instances in all):");
    for (label, count, duplicates, _) in rows.iter().take(MAX_QUANTIFIERS) {
        let dup = if *duplicates > 0 { format!(" (+{duplicates} duplicates)") } else { "".into() };
        let _ = writeln!(o, "  {count:>7}  {label}{dup}");
    }
    if rows.len() > MAX_QUANTIFIERS {
        let rest: u64 = rows[MAX_QUANTIFIERS..].iter().map(|row| row.1).sum();
        let _ =
            writeln!(o, "  ({} more quantifiers, {rest} instances)", rows.len() - MAX_QUANTIFIERS);
    }
    if generated > 0 {
        let _ = writeln!(o, "  ({generated} instances of Verus-generated and prelude axioms)");
    }
    // One of the crate's own quantifiers taking most of the work is worth a
    // look even when cvc5 saw no loop.
    if let Some((label, ..)) = dominant {
        next.push(format!(
            "{label} accounts for most instances; a more specific trigger, or a lemma called \
             explicitly, would cut them"
        ));
    }
}

/// The quantifiers no instantiation strategy claimed to have fully
/// processed: candidates for what the solver could not finish. Only the
/// crate's own are listed, once per place they are written: every check has
/// vstd's and the prelude's in scope, and under E-matching they are all
/// candidates.
fn culprits(o: &mut String, joiner: &Joiner, qids: &[String]) {
    let mut own: Vec<String> = Vec::new();
    for qid in qids.iter().filter(|q| joiner.own(q)) {
        let label = joiner.quantifier(qid);
        if !own.contains(&label) {
            own.push(label);
        }
    }
    if own.is_empty() {
        return;
    }
    let _ = writeln!(o, "this crate's quantifiers the solver could not finish with:");
    for label in own.iter().take(MAX_CULPRITS) {
        let _ = writeln!(o, "  - {label}");
    }
    if own.len() > MAX_CULPRITS {
        let _ = writeln!(o, "  ({} more)", own.len() - MAX_CULPRITS);
    }
}

/// The nonlinear terms whose value the solver could not reconcile with the
/// values of their factors.
fn nonlinear(o: &mut String, names: &SourceNames, f: &NlFrontier, next: &mut Vec<String>) {
    if f.unparsed.is_some() || f.atoms.is_empty() {
        return;
    }
    // Only bounds the hypotheses imply: the others hold in the branch the
    // solver happened to explore.
    let bounds = |lower: &Option<air::diagnostics::NlBound>,
                  upper: &Option<air::diagnostics::NlBound>| {
        let lower = lower.as_ref().filter(|b| b.fixed);
        let upper = upper.as_ref().filter(|b| b.fixed);
        let lo = lower
            .map(|b| format!("{}{}", smt_number(&b.value), if b.strict { " <" } else { " <=" }));
        let hi = upper
            .map(|b| format!("{}{}", if b.strict { "< " } else { "<= " }, smt_number(&b.value)));
        match (lo, hi) {
            (None, None) => String::new(),
            (lo, hi) => format!(
                ", known {}_{}",
                lo.map(|l| l + " ").unwrap_or_default(),
                hi.map(|h| " ".to_string() + &h).unwrap_or_default()
            ),
        }
    };
    let _ = writeln!(o, "nonlinear terms the solver could not settle:");
    for a in f.atoms.iter().take(MAX_NL_ATOMS) {
        let args: Vec<String> = a
            .args
            .iter()
            .map(|t| {
                format!(
                    "{} = {}{}",
                    clip(render_smt_arith(names, &t.term)),
                    smt_number(&t.value),
                    bounds(&t.lower, &t.upper)
                )
            })
            .collect();
        let _ = writeln!(
            o,
            "  - {}: the model gives it {}, but its factors give {} ({})",
            clip(render_smt_arith(names, &a.atom)),
            smt_number(&a.value),
            smt_number(&a.from_args),
            args.join("; ")
        );
    }
    if f.atoms.len() > MAX_NL_ATOMS || f.omitted > 0 {
        let more = f.atoms.len().saturating_sub(MAX_NL_ATOMS) as u64 + f.omitted;
        let _ = writeln!(o, "  ({more} more)");
    }
    next.push(
        "prove the nonlinear fact separately, with `by (nonlinear_arith)` and the bounds it \
         needs, or with a lemma from `vstd::arithmetic`"
            .to_string(),
    );
}

/// The equalities the solver held between the query's own terms when it
/// found its model.
fn equalities(o: &mut String, names: &SourceNames, egraph: &EgraphReply) {
    if egraph.error.is_some() {
        return;
    }
    let mut shown = Vec::new();
    let mut seen = HashSet::new();
    for e in egraph.equalities.iter().filter(|e| e.focus > 0) {
        let lhs = render_term(names, &e.lhs);
        let rhs = render_term(names, &e.rhs);
        if lhs == rhs || !seen.insert((lhs.clone(), rhs.clone())) {
            continue;
        }
        let branch = if e.level == "entailed" { "" } else { "  (in this branch only)" };
        shown.push(format!("  {}{branch}", clip(format!("{lhs} == {rhs}"))));
    }
    if shown.is_empty() {
        return;
    }
    let _ = writeln!(o, "equalities the solver held between the goal's terms:");
    for line in shown.iter().take(MAX_EQUALITIES) {
        let _ = writeln!(o, "{line}");
    }
    if shown.len() > MAX_EQUALITIES {
        let _ = writeln!(o, "  ({} more)", shown.len() - MAX_EQUALITIES);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numbers_read_as_cvc5_prints_them() {
        assert_eq!(smt_number("(- 5)"), "-5");
        assert_eq!(smt_number("(/ 1 2)"), "1/2");
        assert_eq!(smt_number("(- (- 3))"), "3");
        assert_eq!(smt_number("7"), "7");
    }

    #[test]
    fn long_terms_are_cut() {
        let long = "x".repeat(MAX_TERM + 10);
        assert_eq!(clip(long).chars().count(), MAX_TERM + 1);
        assert_eq!(clip("short".to_string()), "short");
    }
}
