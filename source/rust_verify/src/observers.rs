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

use air::ast::{AssertId, BinaryOp, BindX, Expr, ExprX, Ident, MultiOp, Query, Stmt, StmtX};
use air::query_result_observer::CheckValidResult;
use serde::Serialize;
use std::any::Any;
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;

/// The observer names this module serves.
pub const COVERAGE: &str = "coverage";
pub const PROOF_STATE: &str = "proof-state";

/// The observers the test suites register, one at a time.
pub const TEST_OBSERVERS: &[&str] = &["test", "air-only", "query-result-only", "vir-only"];

/// Whether `-V observers=` names a valid set: `coverage` and `proof-state`
/// in any combination, or a single test observer.
pub fn check_names(names: &[String]) -> Result<(), String> {
    let known = |n: &str| n == COVERAGE || n == PROOF_STATE || TEST_OBSERVERS.contains(&n);
    if names.is_empty() {
        return Err(format!("expected a list of observers ({COVERAGE}, {PROOF_STATE})"));
    }
    if let Some(bad) = names.iter().find(|n| !known(n)) {
        return Err(format!("unknown observer `{bad}`; expected {COVERAGE} and/or {PROOF_STATE}"));
    }
    let tests = names.iter().filter(|n| TEST_OBSERVERS.contains(&n.as_str())).count();
    if tests > 0 && names.len() > 1 {
        return Err(format!("a test observer cannot be combined with others: {}", names.join(",")));
    }
    Ok(())
}

/// A failing assertion's conjuncts are listed up to this many; the rest are
/// counted in `conjuncts_omitted`.
const MAX_CONJUNCTS: usize = 32;
/// At most this many conjuncts are evaluated in the counterexample (one
/// solver round trip each), so that false ones beyond the first
/// `MAX_CONJUNCTS` can still be listed first; the rest are omitted.
const MAX_EVALUATIONS: usize = 4 * MAX_CONJUNCTS;
/// Likewise the variables whose counterexample values are reported.
const MAX_VALUES: usize = 64;
/// How deeply temporaries and preconditions are expanded into their
/// definitions.
const MAX_TEMP_DEPTH: usize = 8;

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
    /// Each Verus temporary (`tmp%1`) the query defines exactly once, by
    /// `assume (= tmp%1 e)`, with its definition. `assert(a && b)` asserts
    /// such a temporary, so its conjuncts are those of the definition.
    temps: HashMap<String, Expr>,
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
    /// A temporary or a callee's precondition (`req%f(args)`) whose
    /// definition was not available, so it could not be split further.
    #[serde(skip_serializing_if = "std::ops::Not::not")]
    pub unexpanded: bool,
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
    /// (term, value, unexpanded)
    conjuncts: Vec<(String, Option<bool>, bool)>,
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
    /// Under proof-state: each precondition function the context declared
    /// (`req%f`), with its parameters and definition, from the axiom
    /// `forall params. req%f(params) == body`. A failing call's
    /// precondition splits into the conjuncts of its body.
    requires: HashMap<String, (Vec<Ident>, Expr)>,
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
            requires: HashMap::new(),
        })
    }

    /// Close the query just checked and hand over what was seen of it.
    ///
    /// `failed` are the ids of the failures that reached the verifier
    /// without the `Invalid` callback (no model: bit-vector and nonlinear
    /// checks, which carry no id at all). Such an answer has no error span,
    /// and ids are not unique (a function's postconditions share one; loop
    /// invariants and bit-vector asserts have none), so a failure is placed
    /// only when its id names exactly one undecided assertion; otherwise
    /// which one failed is unknown, and they stay undecided.
    /// `truncated` says the verifier stopped checking obligations after the
    /// first failure (the `--multiple-errors` budget ran out), so a later
    /// `Valid` does not speak for them.
    pub fn take_query(
        &mut self,
        failed: &[Option<AssertId>],
        timed_out: bool,
        truncated: bool,
    ) -> Option<RawQuery> {
        let mut pending = self.pending.take()?;
        for id in failed {
            let mut undecided =
                pending.assertions.iter_mut().filter(|a| a.status.is_none() && &a.id == id);
            if let (Some(a), None) = (undecided.next(), undecided.next()) {
                a.status = Some(Status::Failed);
            }
        }
        if truncated {
            // AIR's `only_check_earlier` disables every label after the
            // first failed one (in label order), so a later `Valid` speaks
            // only for the assertions before it.
            if let Some(first) =
                pending.assertions.iter().position(|a| a.status == Some(Status::Failed))
            {
                for a in pending.assertions[first + 1..].iter_mut() {
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

/// The temporaries `stmt` defines exactly once, with their definitions.
fn temp_definitions(stmt: &Stmt) -> HashMap<String, Expr> {
    fn walk(stmt: &Stmt, defs: &mut HashMap<String, Vec<Expr>>) {
        match &**stmt {
            StmtX::Assume(e) => {
                if let ExprX::Binary(air::ast::BinaryOp::Eq, lhs, rhs) = &**e {
                    if let ExprX::Var(x) = &**lhs {
                        if x.starts_with(vir::def::PREFIX_TEMP_VAR) {
                            defs.entry(x.to_string()).or_default().push(rhs.clone());
                        }
                    }
                }
            }
            StmtX::DeadEnd(s) | StmtX::Breakable(_, s) => walk(s, defs),
            StmtX::Block(ss) | StmtX::Switch(ss) => {
                for s in ss.iter() {
                    walk(s, defs);
                }
            }
            StmtX::Assert(..)
            | StmtX::Havoc(_)
            | StmtX::Assign(..)
            | StmtX::Snapshot(_)
            | StmtX::Break(_) => {}
        }
    }
    let mut defs = HashMap::new();
    walk(stmt, &mut defs);
    defs.into_iter()
        .filter_map(|(x, mut es)| (es.len() == 1).then(|| (x, es.pop().unwrap())))
        .collect()
}

/// A precondition function's definition, if `axiom` is the one Verus
/// declares for it: `forall params. req%f(params) == body` (or, with no
/// parameters, `req%f == body`).
fn requires_definition(axiom: &Expr) -> Option<(String, Vec<Ident>, Expr)> {
    let (params, eq): (Vec<Ident>, &Expr) = match &**axiom {
        ExprX::Bind(bind, body) => match &**bind {
            BindX::Quant(air::ast::Quant::Forall, bs, _, _) => {
                (bs.iter().map(|b| b.name.clone()).collect(), body)
            }
            _ => return None,
        },
        _ => (Vec::new(), axiom),
    };
    let ExprX::Binary(BinaryOp::Eq, lhs, body) = &**eq else { return None };
    let (f, args) = match &**lhs {
        ExprX::Apply(f, args) => (f, args.iter().collect::<Vec<_>>()),
        ExprX::Var(f) => (f, Vec::new()),
        _ => return None,
    };
    let is_param = |(a, p): (&&Expr, &Ident)| matches!(&***a, ExprX::Var(x) if x == p);
    (f.starts_with(vir::def::PREFIX_REQUIRES)
        && args.len() == params.len()
        && args.iter().zip(params.iter()).all(is_param))
    .then(|| (f.to_string(), params, body.clone()))
}

/// `body` with each parameter replaced by its argument; `None` when a
/// binder inside `body` shadows a parameter.
fn instantiate(params: &[Ident], args: &[Expr], body: &Expr) -> Option<Expr> {
    let mut shadowed = false;
    air::visitor::map_expr_visitor(body, &mut |e| {
        if let ExprX::Bind(bind, _) = &**e {
            let names: Vec<&Ident> = match &**bind {
                BindX::Let(bs) => bs.iter().map(|b| &b.name).collect(),
                BindX::Quant(_, bs, _, _)
                | BindX::Lambda(bs, _, _)
                | BindX::Choose(bs, _, _, _) => bs.iter().map(|b| &b.name).collect(),
            };
            shadowed |= names.iter().any(|n| params.contains(n));
        }
        e.clone()
    });
    if shadowed {
        return None;
    }
    Some(air::visitor::map_expr_visitor(body, &mut |e| match &**e {
        ExprX::Var(x) => match params.iter().position(|p| p == x) {
            Some(i) => args[i].clone(),
            None => e.clone(),
        },
        _ => e.clone(),
    }))
}

/// What a failing assertion's conjuncts may be read through.
struct Definitions<'a> {
    temps: &'a HashMap<String, Expr>,
    requires: &'a HashMap<String, (Vec<Ident>, Expr)>,
}

/// The formula's top-level conjuncts, flattening nested conjunctions,
/// reading a temporary as its definition and a callee's precondition as
/// its body at the call's arguments. Each comes with whether it is a
/// temporary or precondition that could not be read that way.
fn conjuncts(expr: &Expr, defs: &Definitions, depth: usize, out: &mut Vec<(Expr, bool)>) {
    let deeper = depth < MAX_TEMP_DEPTH;
    match &**expr {
        ExprX::Multi(MultiOp::And, es) => {
            for e in es.iter() {
                conjuncts(e, defs, depth, out);
            }
        }
        // a precondition's `axiom_location`, once labelled:
        // `%%global_location_label%%N => e`
        ExprX::Binary(BinaryOp::Implies, label, e) if matches!(&**label, ExprX::Var(l) if l.starts_with(air::def::GLOBAL_PREFIX_LABEL)) => {
            conjuncts(e, defs, depth, out)
        }
        ExprX::LabeledAxiom(_, _, e) => conjuncts(e, defs, depth, out),
        ExprX::Var(x) if deeper && defs.temps.contains_key(&**x) => {
            conjuncts(&defs.temps[&**x], defs, depth + 1, out)
        }
        ExprX::Var(x) if x.starts_with(vir::def::PREFIX_TEMP_VAR) => out.push((expr.clone(), true)),
        ExprX::Apply(f, args) if f.starts_with(vir::def::PREFIX_REQUIRES) => {
            let body = defs
                .requires
                .get(&**f)
                .filter(|_| deeper)
                .and_then(|(params, body)| instantiate(params, args, body));
            match body {
                Some(body) => conjuncts(&body, defs, depth + 1, out),
                None => out.push((expr.clone(), true)),
            }
        }
        _ => out.push((expr.clone(), false)),
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

/// Sorts of the encoding's own constants (type ids like `INT`, the `$`
/// decoration, fuel), whose counterexample values say nothing about the
/// program.
fn is_encoding_sort(typ: &air::ast::Typ) -> bool {
    use vir::def::{DECORATION, FUEL_ID, FUEL_TYPE, TYPE};
    matches!(&**typ, air::ast::TypX::Named(n)
        if [TYPE, DECORATION, FUEL_TYPE, FUEL_ID].contains(&n.as_str()))
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
    fn on_axiom_decl(&mut self, expr: &Expr) {
        if self.proof_state {
            if let Some((f, params, body)) = requires_definition(expr) {
                self.requires.insert(f, (params, body));
            }
        }
    }

    fn on_query_lowered(
        &mut self,
        query: &Query,
        _snapshots: &air::ast::Snapshots,
        _local_vars: &[air::ast::Decl],
    ) {
        let mut assertions = Vec::new();
        collect_assertions(&query.assertion, &mut assertions);
        let temps =
            if self.proof_state { temp_definitions(&query.assertion) } else { HashMap::new() };
        self.pending = Some(Pending { assertions, temps, used_axioms: None, failing: Vec::new() });
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
                let defs = Definitions { temps: &pending.temps, requires: &self.requires };
                conjuncts(&a.expr, &defs, 0, &mut parts);
                // each evaluation is a solver round trip; past the cap the
                // conjuncts are counted as omitted, not evaluated
                let mut evaluated: Vec<(String, Option<bool>, bool)> = parts
                    .iter()
                    .take(MAX_EVALUATIONS)
                    .map(|(c, unexpanded)| (term_text(c), eval_bool_expr(c), *unexpanded))
                    .collect();
                // false first: those are why the assertion failed
                evaluated.sort_by_key(|(_, v, _)| match v {
                    Some(false) => 0,
                    None => 1,
                    Some(true) => 2,
                });
                let conjuncts_omitted = parts.len().saturating_sub(MAX_CONJUNCTS);
                evaluated.truncate(MAX_CONJUNCTS);
                // what the conjuncts read, so an expanded temporary shows
                // the variables of its definition
                let mut symbols = BTreeSet::new();
                for (part, _) in parts.iter() {
                    free_constants(part, &mut Vec::new(), &mut symbols);
                }
                let mut values: Vec<(String, String)> = symbols
                    .into_iter()
                    .filter_map(|s| {
                        let def = model_defs.get(&Arc::new(s.clone()))?;
                        (def.params.is_empty() && !is_encoding_sort(&def.ret))
                            .then(|| (s, def.body.to_string()))
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
                    .map(|(term, value, unexpanded)| Conjunct {
                        term: render_unversioned(names, &term),
                        value,
                        unexpanded,
                    })
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
    fn observer_names_are_checked() {
        let names = |ns: &[&str]| ns.iter().map(|n| n.to_string()).collect::<Vec<_>>();
        assert!(check_names(&names(&["coverage", "proof-state"])).is_ok());
        assert!(check_names(&names(&["test"])).is_ok());
        assert!(
            check_names(&names(&["covrage"])).unwrap_err().contains("unknown observer `covrage`")
        );
        assert!(check_names(&names(&["coverage", ""])).is_err());
        assert!(check_names(&names(&["test", "coverage"])).is_err());
        assert!(check_names(&names(&["test", "vir-only"])).is_err());
        assert!(check_names(&[]).is_err());
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
        let (temps, requires) = (HashMap::new(), HashMap::new());
        let mut out = Vec::new();
        conjuncts(&e, &Definitions { temps: &temps, requires: &requires }, 0, &mut out);
        assert_eq!(out.len(), 3);
    }

    /// `assert(a && b)` asserts a temporary; its conjuncts are its
    /// definition's. A temporary defined on two branches is left alone.
    #[test]
    fn temporaries_read_as_their_definitions() {
        let and = |es: Vec<Expr>| Arc::new(ExprX::Multi(MultiOp::And, Arc::new(es)));
        let def = |x: &str, e: Expr| {
            Arc::new(StmtX::Assume(Arc::new(ExprX::Binary(BinaryOp::Eq, var(x), e))))
        };
        let block = |ss: Vec<Stmt>| Arc::new(StmtX::Block(Arc::new(ss)));
        let body = block(vec![
            def("tmp%1", and(vec![var("a@0"), var("tmp%2")])),
            def("tmp%2", and(vec![var("b@1"), var("c!")])),
            Arc::new(StmtX::Switch(Arc::new(vec![def("tmp%3", var("d")), def("tmp%3", var("e"))]))),
        ]);
        let temps = temp_definitions(&body);
        assert!(temps.contains_key("tmp%1") && !temps.contains_key("tmp%3"));
        let requires = HashMap::new();
        let defs = Definitions { temps: &temps, requires: &requires };
        let split = |e: Expr| {
            let mut out = Vec::new();
            conjuncts(&e, &defs, 0, &mut out);
            out.iter().map(|(c, unexpanded)| (term_text(c), *unexpanded)).collect::<Vec<_>>()
        };
        let s = |t: &str, u: bool| (t.to_string(), u);
        assert_eq!(split(var("tmp%1")), [s("a@0", false), s("b@1", false), s("c!", false)]);
        assert_eq!(split(var("tmp%3")), [s("tmp%3", true)]);
    }

    /// A failing call's precondition `req%f(args)` splits into the
    /// conjuncts of `f`'s requires at those arguments, read through the
    /// labels Verus puts on each requires clause.
    #[test]
    fn preconditions_read_as_their_definitions() {
        let int = Arc::new(TypX::Int);
        let binder =
            |x: &str| Arc::new(air::ast::BinderX { name: Arc::new(x.to_string()), a: int.clone() });
        let app =
            |f: &str, es: Vec<Expr>| Arc::new(ExprX::Apply(Arc::new(f.to_string()), Arc::new(es)));
        let bin = |op, a, b| Arc::new(ExprX::Binary(op, a, b));
        let labelled = |n: &str, e| {
            bin(BinaryOp::Implies, var(&format!("{}{}", air::def::GLOBAL_PREFIX_LABEL, n)), e)
        };
        let body = Arc::new(ExprX::Multi(
            MultiOp::And,
            Arc::new(vec![
                labelled("0", bin(BinaryOp::Gt, var("y!"), var("five"))),
                labelled("1", bin(BinaryOp::Lt, var("y!"), var("z!"))),
            ]),
        ));
        let axiom = Arc::new(ExprX::Bind(
            Arc::new(BindX::Quant(
                air::ast::Quant::Forall,
                Arc::new(vec![binder("y!"), binder("z!")]),
                Arc::new(vec![]),
                None,
            )),
            bin(BinaryOp::Eq, app("req%m!g.", vec![var("y!"), var("z!")]), body),
        ));
        let mut o = ObligationObserver::from_names(&["proof-state".to_string()]).unwrap();
        air::air_observer::AirObserver::on_axiom_decl(&mut o, &axiom);
        assert!(o.requires.contains_key("req%m!g."));
        let temps = HashMap::new();
        let defs = Definitions { temps: &temps, requires: &o.requires };
        let mut out = Vec::new();
        conjuncts(&app("req%m!g.", vec![var("a@1"), var("seven")]), &defs, 0, &mut out);
        let terms: Vec<(String, bool)> = out.iter().map(|(c, u)| (term_text(c), *u)).collect();
        assert_eq!(
            terms,
            [("(> a@1 five)".to_string(), false), ("(< a@1 seven)".to_string(), false)]
        );
        // a callee whose requires the context never declared stays whole
        let mut out = Vec::new();
        conjuncts(&app("req%m!h.", vec![var("a@1")]), &defs, 0, &mut out);
        assert_eq!(out.len(), 1);
        assert!(out[0].1);
    }

    /// A failing assertion with many conjuncts costs at most
    /// `MAX_EVALUATIONS` solver round trips; the rest are counted omitted.
    #[test]
    fn evaluations_are_capped() {
        use air::messages::MessageInterface;
        let n = MAX_EVALUATIONS + 10;
        let expr = Arc::new(ExprX::Multi(
            MultiOp::And,
            Arc::new((0..n).map(|i| var(&format!("c{i}"))).collect()),
        ));
        let mut o = ObligationObserver::from_names(&["proof-state".to_string()]).unwrap();
        o.pending = Some(Pending {
            assertions: vec![Assertion {
                id: None,
                message: String::new(),
                span: None,
                expr,
                status: None,
            }],
            temps: HashMap::new(),
            used_axioms: None,
            failing: Vec::new(),
        });
        let mut calls = 0;
        let mut eval = |_: &Expr| {
            calls += 1;
            Some(false)
        };
        let error = air::messages::AirMessageInterface {}
            .bare(air::messages::MessageLevel::Error, "assertion failed");
        air::query_result_observer::QueryResultObserver::on_check_valid_result(
            &mut o,
            &mut CheckValidResult::Invalid {
                model_defs: &HashMap::new(),
                eval_bool_expr: &mut eval,
                assert_id: &None,
                error: &error,
            },
        );
        assert_eq!(calls, MAX_EVALUATIONS);
        let f = &o.pending.as_ref().unwrap().failing[0];
        assert_eq!(f.conjuncts.len(), MAX_CONJUNCTS);
        assert_eq!(f.conjuncts_omitted, n - MAX_CONJUNCTS);
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
        let mut o = ObligationObserver {
            coverage: true,
            proof_state: false,
            pending: None,
            requires: HashMap::new(),
        };
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
                temps: HashMap::new(),
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
        // two failures before the budget ran out: the last round disabled
        // everything after the first, #1, so #2 was never proved either
        o.pending = Some(Pending {
            temps: HashMap::new(),
            assertions: vec![
                assertion(0, Some(Status::Proved)),
                assertion(1, Some(Status::Failed)),
                assertion(2, Some(Status::Proved)),
                assertion(3, Some(Status::Failed)),
                assertion(4, Some(Status::Proved)),
            ],
            used_axioms: None,
            failing: Vec::new(),
        });
        let q = o.take_query(&[], false, true).unwrap();
        assert_eq!(statuses(q), vec![Proved, Failed, Unchecked, Failed, Unchecked]);
        // #3 failed without an Invalid callback (no model)
        pending(&mut o);
        let q = o.take_query(&[id(3)], false, false).unwrap();
        assert_eq!(statuses(q), vec![Proved, Failed, Proved, Failed]);
        // the solver gave up
        pending(&mut o);
        let q = o.take_query(&[], true, false).unwrap();
        assert_eq!(statuses(q), vec![Proved, Failed, Proved, Unknown]);
        // two undecided postconditions share the id that failed without a
        // model: which one failed is not known
        o.pending = Some(Pending {
            temps: HashMap::new(),
            assertions: vec![assertion(5, None), assertion(5, None), assertion(6, None)],
            used_axioms: None,
            failing: Vec::new(),
        });
        let q = o.take_query(&[id(5), id(6)], false, false).unwrap();
        assert_eq!(statuses(q), vec![Unchecked, Unchecked, Failed]);
        // a bit-vector assert has no id, and fails without a model
        o.pending = Some(Pending {
            temps: HashMap::new(),
            assertions: vec![Assertion { id: None, ..assertion(0, None) }],
            used_axioms: None,
            failing: Vec::new(),
        });
        let q = o.take_query(&[None], false, false).unwrap();
        assert_eq!(statuses(q), vec![Failed]);
        assert!(o.take_query(&[], false, false).is_none());
    }
}
