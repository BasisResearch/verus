//! Observers the verifier ships, as opposed to the test observers.
//!
//! One object, [`ObligationObserver`], serves two `-V observers=` names:
//!
//! - `coverage`: for every query, each obligation it asserted (an `assert`,
//!   a postcondition, a loop invariant, a precondition of a call...) and what
//!   became of it: `proved`, `failed`, `unknown` (the solver gave up on the
//!   query) or `unchecked` (the query stopped before reaching it). With
//!   `-V axiom-usage-info` a proved query also names the axioms in its unsat
//!   core. This is the obligation-level counterpart of `verus-reach`, which
//!   says which functions are used; this says which of a function's
//!   obligations were actually discharged.
//! - `proof-state`: at each failing obligation, while the solver's
//!   counterexample is still live, which conjuncts of the failing assertion
//!   are false in it and what the counterexample gives each variable the
//!   assertion reads.
//!
//! Both need the query's assertions, which `AirObserver::on_query_lowered`
//! hands over after variables became versioned constants, and the answer,
//! which `QueryResultObserver` hands over. Neither knows which function a
//! query belongs to; the verifier does, so it drains the observer after each
//! query ([`ObligationObserver::take_query`]) and files the records under the
//! function, the way it files the other per-query solver reports. Terms stay
//! AIR text until the end of the crate, when [`resolve`] renders them as
//! source with the names the encoders recorded.

use air::ast::{AssertId, Expr, ExprX, MultiOp, Query, Stmt, StmtX};
use air::query_result_observer::CheckValidResult;
use serde::Serialize;
use std::any::Any;
use std::collections::BTreeSet;
use std::sync::Arc;

/// The observer names this module serves.
pub const COVERAGE: &str = "coverage";
pub const PROOF_STATE: &str = "proof-state";

/// A failing assertion's conjuncts are listed up to this many; the rest are
/// counted in `conjuncts_omitted`.
const MAX_CONJUNCTS: usize = 32;
/// Likewise the variables whose counterexample values are reported.
const MAX_VALUES: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Status {
    Proved,
    Failed,
    /// The solver gave up (resource limit or cancellation) before deciding it.
    Unknown,
    /// The query stopped before the solver decided it: an earlier failure
    /// ended the query (`--multiple-errors 0`), or the error budget ran out.
    Unchecked,
}

/// One assertion of a lowered query.
struct Assertion {
    id: Option<AssertId>,
    message: String,
    span: Option<String>,
    /// The asserted formula, over versioned constants.
    expr: Expr,
    status: Option<Status>,
}

/// The query being checked: its assertions, and the answers so far.
struct Pending {
    assertions: Vec<Assertion>,
    used_axioms: Option<Vec<String>>,
    failing: Vec<RawFailingAssert>,
}

/// One obligation, before its terms are rendered as source.
#[derive(Clone, Debug, Serialize)]
pub struct Obligation {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub assert_id: Option<String>,
    /// What Verus reports when it fails: "postcondition not satisfied", ...
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<String>,
    pub status: Status,
}

/// A conjunct of a failing assertion, and its value in the counterexample:
/// null when the solver could not evaluate it (a quantifier, say).
#[derive(Clone, Debug, Serialize)]
pub struct Conjunct {
    pub term: String,
    pub value: Option<bool>,
}

/// A variable the failing assertion reads, and its counterexample value.
#[derive(Clone, Debug, Serialize)]
pub struct Value {
    /// The versioned AIR constant (`x@2`): which assignment of `x` it is.
    pub symbol: String,
    /// The variable as the source names it, when the encoders recorded it.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    pub value: String,
}

#[derive(Clone, Debug)]
pub struct RawFailingAssert {
    assert_id: Option<String>,
    message: String,
    span: Option<String>,
    conjuncts: Vec<(String, Option<bool>)>,
    conjuncts_omitted: usize,
    values: Vec<(String, String)>,
    values_omitted: usize,
}

/// What the observer saw of one query, before rendering.
pub struct RawQuery {
    obligations: Vec<Obligation>,
    used_axioms: Option<Vec<String>>,
    failing: Vec<RawFailingAssert>,
}

/// Coverage of one query, as `func-details` publishes it under `obligations`.
#[derive(Clone, Debug, Serialize)]
pub struct QueryObligations {
    pub desc: String,
    pub span: String,
    /// `body`, `recommends`, `expanded`, ... as the other per-query records.
    pub kind: &'static str,
    pub obligations: Vec<Obligation>,
    /// Under `-V axiom-usage-info`, when the query was proved: the axioms in
    /// its unsat core, rendered as source where the encoders named them.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub used_axioms: Option<Vec<String>>,
}

/// The counterexample at one failing obligation, as `func-details` publishes
/// it under `failing_asserts`.
#[derive(Clone, Debug, Serialize)]
pub struct FailingAssert {
    pub desc: String,
    pub kind: &'static str,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub assert_id: Option<String>,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub span: Option<String>,
    /// False conjuncts first, then undecided, then true ones.
    pub conjuncts: Vec<Conjunct>,
    #[serde(skip_serializing_if = "is_zero")]
    pub conjuncts_omitted: usize,
    pub values: Vec<Value>,
    #[serde(skip_serializing_if = "is_zero")]
    pub values_omitted: usize,
}

fn is_zero(n: &usize) -> bool {
    *n == 0
}

/// A query's records, filed under its function until the end of the crate.
pub struct FiledQuery {
    pub desc: String,
    pub span: String,
    pub kind: &'static str,
    pub raw: RawQuery,
}

pub struct ObligationObserver {
    coverage: bool,
    proof_state: bool,
    pending: Option<Pending>,
}

impl ObligationObserver {
    /// `None` unless `names` asks for this observer and nothing else.
    pub fn from_names(names: &[String]) -> Option<Self> {
        let coverage = names.iter().any(|n| n == COVERAGE);
        let proof_state = names.iter().any(|n| n == PROOF_STATE);
        let others = names.iter().any(|n| n != COVERAGE && n != PROOF_STATE);
        ((coverage || proof_state) && !others).then(|| ObligationObserver {
            coverage,
            proof_state,
            pending: None,
        })
    }

    /// Close the query just checked and hand over what was seen of it.
    ///
    /// `failed` are the ids the verifier saw fail, which covers answers that
    /// reach it without the `Invalid` callback (no model, bit-vector checks).
    /// `truncated` says the verifier stopped checking obligations after the
    /// last failure (the `--multiple-errors` budget ran out), so a later
    /// `Valid` does not speak for them.
    pub fn take_query(
        &mut self,
        failed: &[AssertId],
        timed_out: bool,
        truncated: bool,
    ) -> Option<RawQuery> {
        let mut pending = self.pending.take()?;
        for a in pending.assertions.iter_mut() {
            if a.status.is_none() && a.id.as_ref().is_some_and(|id| failed.contains(id)) {
                a.status = Some(Status::Failed);
            }
        }
        if truncated {
            if let Some(last) =
                pending.assertions.iter().rposition(|a| a.status == Some(Status::Failed))
            {
                for a in pending.assertions[last + 1..].iter_mut() {
                    if a.status == Some(Status::Proved) {
                        a.status = Some(Status::Unchecked);
                    }
                }
            }
        }
        let rest = if timed_out { Status::Unknown } else { Status::Unchecked };
        let obligations = if self.coverage {
            pending
                .assertions
                .into_iter()
                .map(|a| Obligation {
                    assert_id: a.id.as_ref().map(air::def::assert_id_to_symbol),
                    message: a.message,
                    span: a.span,
                    status: a.status.unwrap_or(rest),
                })
                .collect()
        } else {
            Vec::new()
        };
        Some(RawQuery { obligations, used_axioms: pending.used_axioms, failing: pending.failing })
    }
}

/// The message and primary span of an assertion's error.
fn describe(message: &air::messages::ArcDynMessage) -> (String, Option<String>) {
    match message.downcast_ref::<vir::messages::MessageX>() {
        Some(m) => (m.note.clone(), m.spans.first().map(|s| s.as_string.clone())),
        None => (String::new(), None),
    }
}

fn collect_assertions(stmt: &Stmt, out: &mut Vec<Assertion>) {
    match &**stmt {
        StmtX::Assert(id, message, _, expr) => {
            let (message, span) = describe(message);
            out.push(Assertion { id: id.clone(), message, span, expr: expr.clone(), status: None });
        }
        StmtX::DeadEnd(s) | StmtX::Breakable(_, s) => collect_assertions(s, out),
        StmtX::Block(ss) | StmtX::Switch(ss) => {
            for s in ss.iter() {
                collect_assertions(s, out);
            }
        }
        StmtX::Assume(_)
        | StmtX::Havoc(_)
        | StmtX::Assign(..)
        | StmtX::Snapshot(_)
        | StmtX::Break(_) => {}
    }
}

/// The formula's top-level conjuncts, flattening nested conjunctions.
fn conjuncts(expr: &Expr, out: &mut Vec<Expr>) {
    match &**expr {
        ExprX::Multi(MultiOp::And, es) => {
            for e in es.iter() {
                conjuncts(e, out);
            }
        }
        _ => out.push(expr.clone()),
    }
}

/// The constants the formula reads, outside binders' own variables.
fn free_constants(expr: &Expr, bound: &mut Vec<String>, out: &mut BTreeSet<String>) {
    match &**expr {
        ExprX::Const(_) => {}
        ExprX::Var(x) => {
            if !bound.iter().any(|b| b == &**x) {
                out.insert(x.to_string());
            }
        }
        ExprX::Old(_, x) => {
            out.insert(x.to_string());
        }
        ExprX::Apply(_, es) | ExprX::Multi(_, es) | ExprX::Array(es) => {
            for e in es.iter() {
                free_constants(e, bound, out);
            }
        }
        ExprX::ApplyFun(_, f, es) => {
            free_constants(f, bound, out);
            for e in es.iter() {
                free_constants(e, bound, out);
            }
        }
        ExprX::Unary(_, e) | ExprX::LabeledAxiom(_, _, e) | ExprX::LabeledAssertion(_, _, _, e) => {
            free_constants(e, bound, out)
        }
        ExprX::Binary(_, a, b) => {
            free_constants(a, bound, out);
            free_constants(b, bound, out);
        }
        ExprX::IfElse(a, b, c) => {
            free_constants(a, bound, out);
            free_constants(b, bound, out);
            free_constants(c, bound, out);
        }
        ExprX::Bind(bind, e) => {
            let names: Vec<String> = match &**bind {
                air::ast::BindX::Let(bs) => {
                    for b in bs.iter() {
                        free_constants(&b.a, bound, out);
                    }
                    bs.iter().map(|b| b.name.to_string()).collect()
                }
                air::ast::BindX::Quant(_, bs, _, _) | air::ast::BindX::Lambda(bs, _, _) => {
                    bs.iter().map(|b| b.name.to_string()).collect()
                }
                air::ast::BindX::Choose(bs, _, _, cond) => {
                    let names: Vec<String> = bs.iter().map(|b| b.name.to_string()).collect();
                    let depth = bound.len();
                    bound.extend(names.iter().cloned());
                    free_constants(cond, bound, out);
                    bound.truncate(depth);
                    names
                }
            };
            let depth = bound.len();
            bound.extend(names);
            free_constants(e, bound, out);
            bound.truncate(depth);
        }
    }
}

fn term_text(expr: &Expr) -> String {
    let printer = air::printer::Printer::new(
        Arc::new(air::messages::AirMessageInterface {}),
        true,
        air::context::SmtSolver::Cvc5,
    );
    air::printer::NodeWriter::new()
        .node_to_string_indent(&String::new(), &printer.expr_to_node(expr))
}

impl air::air_observer::AirObserver for ObligationObserver {
    fn on_query_lowered(
        &mut self,
        query: &Query,
        _snapshots: &air::ast::Snapshots,
        _local_vars: &[air::ast::Decl],
    ) {
        let mut assertions = Vec::new();
        collect_assertions(&query.assertion, &mut assertions);
        self.pending = Some(Pending { assertions, used_axioms: None, failing: Vec::new() });
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

impl air::query_result_observer::QueryResultObserver for ObligationObserver {
    fn on_check_valid_result(&mut self, result: &mut CheckValidResult) {
        let proof_state = self.proof_state;
        let Some(pending) = &mut self.pending else { return };
        match result {
            CheckValidResult::Valid { usage_info, .. } => {
                for a in pending.assertions.iter_mut() {
                    if a.status.is_none() {
                        a.status = Some(Status::Proved);
                    }
                }
                if let air::context::UsageInfo::UsedAxioms(axioms) = usage_info {
                    pending.used_axioms = Some(axioms.iter().map(|a| a.to_string()).collect());
                }
            }
            CheckValidResult::Timeout { .. } => {
                for a in pending.assertions.iter_mut() {
                    if a.status.is_none() {
                        a.status = Some(Status::Unknown);
                    }
                }
            }
            CheckValidResult::Invalid { model_defs, eval_bool_expr, assert_id, error } => {
                // The undecided assertion the solver's label named. Ids are
                // not unique (loop invariants have none, a function's
                // postconditions share one), so the error's primary span
                // decides between assertions with the same id.
                let (_, error_span) = describe(error);
                let undecided = |a: &Assertion| a.status.is_none() && &a.id == *assert_id;
                let Some(index) = pending
                    .assertions
                    .iter()
                    .position(|a| undecided(a) && error_span.is_some() && a.span == error_span)
                    .or_else(|| pending.assertions.iter().position(undecided))
                else {
                    return;
                };
                let a = &mut pending.assertions[index];
                a.status = Some(Status::Failed);
                if !proof_state {
                    return;
                }
                let mut parts = Vec::new();
                conjuncts(&a.expr, &mut parts);
                let mut evaluated: Vec<(String, Option<bool>)> =
                    parts.iter().map(|c| (term_text(c), eval_bool_expr(c))).collect();
                // false first: those are why the assertion failed
                evaluated.sort_by_key(|(_, v)| match v {
                    Some(false) => 0,
                    None => 1,
                    Some(true) => 2,
                });
                let conjuncts_omitted = evaluated.len().saturating_sub(MAX_CONJUNCTS);
                evaluated.truncate(MAX_CONJUNCTS);
                let mut symbols = BTreeSet::new();
                free_constants(&a.expr, &mut Vec::new(), &mut symbols);
                let mut values: Vec<(String, String)> = symbols
                    .into_iter()
                    .filter_map(|s| {
                        let def = model_defs.get(&Arc::new(s.clone()))?;
                        def.params.is_empty().then(|| (s, def.body.to_string()))
                    })
                    .collect();
                let values_omitted = values.len().saturating_sub(MAX_VALUES);
                values.truncate(MAX_VALUES);
                pending.failing.push(RawFailingAssert {
                    assert_id: a.id.as_ref().map(air::def::assert_id_to_symbol),
                    message: a.message.clone(),
                    span: a.span.clone(),
                    conjuncts: evaluated,
                    conjuncts_omitted,
                    values,
                    values_omitted,
                });
            }
        }
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

/// The source spelling of a versioned constant's variable: `x@2` reads as
/// `x`, when the encoders recorded `x@`.
fn variable_name(names: &vir::air_names::SourceNames, symbol: &str) -> Option<String> {
    let base = match symbol.rfind('@') {
        Some(at) => &symbol[..=at],
        None => symbol,
    };
    let rendered = vir::air_names::render_term(names, base);
    (rendered != base).then_some(rendered)
}

/// A term with each versioned constant (`i@1`) read as its variable (`i@`),
/// which the encoders recorded: the source has no versions.
fn render_unversioned(names: &vir::air_names::SourceNames, term: &str) -> String {
    let mut out = String::with_capacity(term.len());
    let mut chars = term.chars().peekable();
    while let Some(c) = chars.next() {
        out.push(c);
        if c == '@' {
            while chars.peek().is_some_and(|d| d.is_ascii_digit()) {
                chars.next();
            }
        }
    }
    vir::air_names::render_term(names, &out)
}

/// Render one function's filed queries as source.
pub fn resolve(
    names: &vir::air_names::SourceNames,
    queries: Vec<FiledQuery>,
) -> (Vec<QueryObligations>, Vec<FailingAssert>) {
    let mut obligations = Vec::new();
    let mut failing = Vec::new();
    for q in queries {
        let FiledQuery { desc, span, kind, raw } = q;
        if !raw.obligations.is_empty() {
            obligations.push(QueryObligations {
                desc: desc.clone(),
                span,
                kind,
                obligations: raw.obligations,
                used_axioms: raw.used_axioms.map(|axioms| {
                    axioms.iter().map(|a| vir::air_names::render_term(names, a)).collect()
                }),
            });
        }
        for f in raw.failing {
            failing.push(FailingAssert {
                desc: desc.clone(),
                kind,
                assert_id: f.assert_id,
                message: f.message,
                span: f.span,
                conjuncts: f
                    .conjuncts
                    .into_iter()
                    .map(|(term, value)| Conjunct { term: render_unversioned(names, &term), value })
                    .collect(),
                conjuncts_omitted: f.conjuncts_omitted,
                values: f
                    .values
                    .into_iter()
                    .map(|(symbol, value)| Value {
                        name: variable_name(names, &symbol),
                        value: vir::air_names::render_term(names, &value),
                        symbol,
                    })
                    .collect(),
                values_omitted: f.values_omitted,
            });
        }
    }
    (obligations, failing)
}

#[cfg(test)]
mod tests {
    use super::*;
    use air::ast::{BinaryOp, Constant, TypX};

    fn var(x: &str) -> Expr {
        Arc::new(ExprX::Var(Arc::new(x.to_string())))
    }

    #[test]
    fn names_select_the_observer_alone() {
        let names = |ns: &[&str]| ns.iter().map(|n| n.to_string()).collect::<Vec<_>>();
        assert!(ObligationObserver::from_names(&names(&["coverage"])).is_some());
        let both = ObligationObserver::from_names(&names(&["coverage", "proof-state"])).unwrap();
        assert!(both.coverage && both.proof_state);
        assert!(ObligationObserver::from_names(&names(&["coverage", "test"])).is_none());
        assert!(ObligationObserver::from_names(&names(&["test"])).is_none());
    }

    #[test]
    fn versions_are_dropped_before_rendering() {
        let names = vir::air_names::SourceNames::new();
        assert_eq!(render_unversioned(&names, "(<= i@12 n@)"), "(i@ <= n@)");
    }

    #[test]
    fn conjuncts_flatten_nested_ands() {
        let and = |es: Vec<Expr>| Arc::new(ExprX::Multi(MultiOp::And, Arc::new(es)));
        let e = and(vec![var("a"), and(vec![var("b"), var("c")])]);
        let mut out = Vec::new();
        conjuncts(&e, &mut out);
        assert_eq!(out.len(), 3);
    }

    #[test]
    fn free_constants_skip_bound_variables() {
        let binder =
            Arc::new(air::ast::BinderX { name: Arc::new("i".to_string()), a: Arc::new(TypX::Int) });
        let body = Arc::new(ExprX::Binary(BinaryOp::Le, var("i"), var("n@1")));
        let bind = Arc::new(air::ast::BindX::Quant(
            air::ast::Quant::Forall,
            Arc::new(vec![binder]),
            Arc::new(vec![]),
            None,
        ));
        let e = Arc::new(ExprX::Multi(
            MultiOp::And,
            Arc::new(vec![
                Arc::new(ExprX::Bind(bind, body)),
                var("x@0"),
                Arc::new(ExprX::Const(Constant::Bool(true))),
            ]),
        ));
        let mut out = BTreeSet::new();
        free_constants(&e, &mut Vec::new(), &mut out);
        assert_eq!(out.into_iter().collect::<Vec<_>>(), vec!["n@1", "x@0"]);
    }

    #[test]
    fn take_query_fills_statuses() {
        let mut o = ObligationObserver { coverage: true, proof_state: false, pending: None };
        let id = |n: u64| Some(Arc::new(vec![n]));
        let assertion = |n: u64, status| Assertion {
            id: id(n),
            message: String::new(),
            span: None,
            expr: var("x"),
            status,
        };
        let pending = |o: &mut ObligationObserver| {
            o.pending = Some(Pending {
                assertions: vec![
                    assertion(0, Some(Status::Proved)),
                    assertion(1, Some(Status::Failed)),
                    assertion(2, Some(Status::Proved)),
                    assertion(3, None),
                ],
                used_axioms: None,
                failing: Vec::new(),
            })
        };
        pending(&mut o);
        let statuses = |q: RawQuery| q.obligations.iter().map(|o| o.status).collect::<Vec<_>>();
        use Status::*;
        // the error budget ran out after #1: a later Valid does not speak for #2
        let q = o.take_query(&[], false, true).unwrap();
        assert_eq!(statuses(q), vec![Proved, Failed, Unchecked, Unchecked]);
        // #3 failed without an Invalid callback (no model)
        pending(&mut o);
        let q = o.take_query(&[Arc::new(vec![3])], false, false).unwrap();
        assert_eq!(statuses(q), vec![Proved, Failed, Proved, Failed]);
        // the solver gave up
        pending(&mut o);
        let q = o.take_query(&[], true, false).unwrap();
        assert_eq!(statuses(q), vec![Proved, Failed, Proved, Unknown]);
        assert!(o.take_query(&[], false, false).is_none());
    }
}
