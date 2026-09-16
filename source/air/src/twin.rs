//! Edits of one query, and the comparison of two checks
//! (`counterfactual_twin`).
//!
//! A twin is a query with one edit applied: a hypothesis or axiom removed or
//! added, a function's fuel changed, or assertions reordered. The resident
//! worker checks the query and its twin as two ordinary queries on the same
//! declaration prefix, each in its own scope, and compares what cvc5 reports
//! about the two checks: their answers, their instantiations per quantifier
//! and inference, and (in difficulty mode) the difficulty and unsat-core
//! membership of each input assertion.
//!
//! This module holds the edits that are plain AIR and the comparison. Edits
//! that know Verus's encoding, such as fuel, live with the worker. Nothing
//! here talks to a solver.

use crate::ast::{
    AssertId, Axiom, BindX, Binders, DeclX, Expr, ExprX, Ident, Quant, Query, QueryX, Stmt, StmtX,
    Triggers, Typ,
};
use crate::context::{BranchProfile, DifficultyGradient, InstPressure};
use crate::def::ProvenanceTag;
use crate::messages::MessageInterface;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

/// The provenance tag an axiom added by a twin carries: `ax_twin_added`.
pub const TWIN_ADDED: &str = "twin_added";

/// Every name an axiom answers to: its provenance tag as the wire spells it
/// (`hyp_3`, `ax_<ident>`), the identifier inside an axiom tag, and the
/// `:qid` of the quantifier it is or guards, bare and as the tag an untagged
/// axiom gets from it.
pub fn axiom_names(axiom: &Axiom) -> Vec<String> {
    let mut names = Vec::new();
    if let Some(tag) = &axiom.tag {
        names.push(tag.to_symbol());
        if let ProvenanceTag::Axiom(ident) = tag {
            names.push(ident.to_string());
        }
    }
    if let Some(qid) = crate::smt_verify::axiom_qid(&axiom.expr) {
        names.push(ProvenanceTag::Axiom(qid.clone()).to_symbol());
        names.push(qid.to_string());
    }
    names.sort();
    names.dedup();
    names
}

/// Whether `axiom` answers to `name` (see `axiom_names`). Surrounding `|`
/// quotes, as cvc5 prints some symbols, are ignored.
pub fn axiom_named(axiom: &Axiom, name: &str) -> bool {
    let name = name.trim().trim_matches('|');
    !name.is_empty() && axiom_names(axiom).iter().any(|n| n == name)
}

/// An axiom an edit touched, by its tag and the `:qid` it is or guards.
#[derive(Clone, Debug)]
pub struct AxiomRef {
    pub tag: Option<ProvenanceTag>,
    pub qid: Option<Ident>,
}

impl AxiomRef {
    pub fn of(axiom: &Axiom) -> Self {
        AxiomRef { tag: axiom.tag.clone(), qid: crate::smt_verify::axiom_qid(&axiom.expr) }
    }
}

/// `query` without the local axioms `name` names, and the axioms removed.
pub fn remove_local_axioms(query: &Query, name: &str) -> (Query, Vec<AxiomRef>) {
    let mut removed = Vec::new();
    let local = query
        .local
        .iter()
        .filter(|decl| match &***decl {
            DeclX::Axiom(axiom) if axiom_named(axiom, name) => {
                removed.push(AxiomRef::of(axiom));
                false
            }
            _ => true,
        })
        .cloned()
        .collect();
    (Arc::new(QueryX { local: Arc::new(local), assertion: query.assertion.clone() }), removed)
}

/// `query` with `axiom` as one more local declaration, after the others.
pub fn with_local_axiom(query: &Query, axiom: Axiom) -> Query {
    let mut local = (*query.local).clone();
    local.push(Arc::new(DeclX::Axiom(axiom)));
    Arc::new(QueryX { local: Arc::new(local), assertion: query.assertion.clone() })
}

/// `query` with the local axioms `edit` maps to `Some` replaced, and those
/// it maps to `None` kept. Returns how many were replaced.
pub fn replace_local_axioms(
    query: &Query,
    edit: &mut dyn FnMut(&Axiom) -> Option<Axiom>,
) -> (Query, usize) {
    let mut replaced = 0;
    let local = query
        .local
        .iter()
        .map(|decl| match &**decl {
            DeclX::Axiom(axiom) => match edit(axiom) {
                Some(new) => {
                    replaced += 1;
                    Arc::new(DeclX::Axiom(new))
                }
                None => decl.clone(),
            },
            _ => decl.clone(),
        })
        .collect();
    (Arc::new(QueryX { local: Arc::new(local), assertion: query.assertion.clone() }), replaced)
}

/// An axiom from caller text: one AIR expression, as the AIR parser reads
/// it (SMT-LIB-like: `(forall ((x Int)) (! (= (f x) 0) :pattern ((f x))))`).
/// It is only parsed here; whether it type-checks against a query's
/// declarations is for the check that asserts it to find out.
pub fn parse_axiom(
    message_interface: Arc<dyn MessageInterface>,
    text: &str,
) -> Result<Axiom, String> {
    let not_one = |_| format!("not one AIR expression: {text}");
    let mut parser = sise::Parser::new(text);
    let node = sise::parse_tree(&mut parser).map_err(not_one)?;
    parser.finish().map_err(not_one)?;
    let expr = crate::parser::Parser::new(message_interface).node_to_expr(&node)?;
    Ok(Axiom {
        named: None,
        tag: Some(ProvenanceTag::Axiom(Arc::new(TWIN_ADDED.to_string()))),
        expr,
    })
}

/// One AIR expression from caller text, as the AIR parser reads it. It is
/// only parsed here; whether it type-checks against a query's declarations is
/// for the check that asserts it to find out.
pub fn parse_expr(
    message_interface: Arc<dyn MessageInterface>,
    text: &str,
) -> Result<Expr, String> {
    let not_one = |_| format!("not one AIR term: {text}");
    let mut parser = sise::Parser::new(text);
    let node = sise::parse_tree(&mut parser).map_err(not_one)?;
    parser.finish().map_err(not_one)?;
    crate::parser::Parser::new(message_interface).node_to_expr(&node)
}

/// The variables and triggers of the first universal quantifier named `qid`
/// under `expr`.
pub fn quantifier_of(expr: &Expr, qid: &str) -> Option<(Binders<Typ>, Triggers)> {
    let mut found = None;
    crate::visitor::map_expr_visitor(expr, &mut |e| {
        if let ExprX::Bind(bind, _) = &**e {
            if let BindX::Quant(Quant::Forall, binders, triggers, Some(q)) = &**bind {
                if found.is_none() && q.as_str() == qid {
                    found = Some((binders.clone(), triggers.clone()));
                }
            }
        }
        e.clone()
    });
    found
}

/// The variables and triggers of the first universal quantifier named `qid`
/// that `query`'s own declarations or its assertion assert.
pub fn quantifier_in_query(query: &Query, qid: &str) -> Option<(Binders<Typ>, Triggers)> {
    for decl in query.local.iter() {
        if let DeclX::Axiom(axiom) = &**decl {
            if let Some(found) = quantifier_of(&axiom.expr, qid) {
                return Some(found);
            }
        }
    }
    let mut found = None;
    crate::visitor::map_stmt_expr_visitor(&query.assertion, &mut |e| {
        if found.is_none() {
            found = quantifier_of(e, qid);
        }
        e.clone()
    });
    found
}

/// `expr` with the triggers of every universal quantifier named `qid`
/// replaced by `triggers`, and how many it replaced.
pub fn set_triggers(expr: &Expr, qid: &str, triggers: &Triggers) -> (Expr, usize) {
    let mut replaced = 0;
    let expr = crate::visitor::map_expr_visitor(expr, &mut |e| match &**e {
        ExprX::Bind(bind, body) => match &**bind {
            BindX::Quant(Quant::Forall, binders, _, Some(q)) if q.as_str() == qid => {
                replaced += 1;
                let bind = BindX::Quant(
                    Quant::Forall,
                    binders.clone(),
                    triggers.clone(),
                    Some(q.clone()),
                );
                Arc::new(ExprX::Bind(Arc::new(bind), body.clone()))
            }
            _ => e.clone(),
        },
        _ => e.clone(),
    });
    (expr, replaced)
}

/// Every variable `expr` binds, at any depth.
pub fn bound_variables(expr: &Expr) -> BTreeSet<Ident> {
    let mut names = BTreeSet::new();
    crate::visitor::map_expr_visitor(expr, &mut |e| {
        if let ExprX::Bind(bind, _) = &**e {
            let binders: Vec<Ident> = match &**bind {
                BindX::Let(binders) => binders.iter().map(|b| b.name.clone()).collect(),
                BindX::Quant(_, binders, _, _)
                | BindX::Lambda(binders, _, _)
                | BindX::Choose(binders, _, _, _) => {
                    binders.iter().map(|b| b.name.clone()).collect()
                }
            };
            names.extend(binders);
        }
        e.clone()
    });
    names
}

/// `expr` with each variable `renaming` maps renamed, in its binders and
/// wherever it occurs. AIR lets no name be bound twice along a path and no
/// bound name stand for a declaration, so a renaming of names `expr` binds
/// needs no capture check; it is how an axiom of the declaration prefix is
/// asserted again inside a query whose own locals it would otherwise
/// shadow.
pub fn rename_bound(expr: &Expr, renaming: &BTreeMap<Ident, Ident>) -> Expr {
    let rename = |binders: &Binders<Typ>| -> Binders<Typ> {
        Arc::new(
            binders
                .iter()
                .map(|b| match renaming.get(&b.name) {
                    Some(to) => Arc::new(crate::ast::BinderX { name: to.clone(), a: b.a.clone() }),
                    None => b.clone(),
                })
                .collect(),
        )
    };
    crate::visitor::map_expr_visitor(expr, &mut |e| match &**e {
        ExprX::Var(x) => match renaming.get(x) {
            Some(to) => Arc::new(ExprX::Var(to.clone())),
            None => e.clone(),
        },
        ExprX::Bind(bind, body) => {
            let bind = match &**bind {
                BindX::Let(binders) => BindX::Let(Arc::new(
                    binders
                        .iter()
                        .map(|b| match renaming.get(&b.name) {
                            Some(to) => Arc::new(crate::ast::BinderX {
                                name: to.clone(),
                                a: b.a.clone(),
                            }),
                            None => b.clone(),
                        })
                        .collect(),
                )),
                BindX::Quant(quant, binders, triggers, qid) => {
                    BindX::Quant(*quant, rename(binders), triggers.clone(), qid.clone())
                }
                BindX::Lambda(binders, triggers, qid) => {
                    BindX::Lambda(rename(binders), triggers.clone(), qid.clone())
                }
                BindX::Choose(binders, triggers, qid, cond) => BindX::Choose(
                    rename(binders),
                    triggers.clone(),
                    qid.clone(),
                    cond.clone(),
                ),
            };
            Arc::new(ExprX::Bind(Arc::new(bind), body.clone()))
        }
        _ => e.clone(),
    })
}

/// Whether `expr` holds a universal quantifier named `qid`.
pub fn holds_quantifier(expr: &Expr, qid: &str) -> bool {
    quantifier_of(expr, qid).is_some()
}

/// `axiom` with the quantifier named `qid` retriggered, and whether it held
/// one.
pub fn retrigger_axiom(axiom: &Axiom, qid: &str, triggers: &Triggers) -> (Axiom, usize) {
    let (expr, replaced) = set_triggers(&axiom.expr, qid, triggers);
    (Axiom { named: axiom.named.clone(), tag: axiom.tag.clone(), expr }, replaced)
}

/// `query` with the quantifier named `qid` retriggered wherever its own
/// declarations or its assertion hold it, and how many it replaced. A
/// quantifier a declaration before the query asserts is not reached here.
pub fn retrigger_query(query: &Query, qid: &str, triggers: &Triggers) -> (Query, usize) {
    let mut replaced = 0;
    let local = query
        .local
        .iter()
        .map(|decl| match &**decl {
            DeclX::Axiom(axiom) => {
                let (axiom, n) = retrigger_axiom(axiom, qid, triggers);
                replaced += n;
                Arc::new(DeclX::Axiom(axiom))
            }
            _ => decl.clone(),
        })
        .collect();
    let assertion = crate::visitor::map_stmt_expr_visitor(&query.assertion, &mut |e| {
        let (e, n) = set_triggers(e, qid, triggers);
        replaced += n;
        e
    });
    (Arc::new(QueryX { local: Arc::new(local), assertion }), replaced)
}

/// `query` with every goal switched off: each `Assert` of `e` keeps its id
/// and message and asserts `(and %%twin_off%% e)`, where `%%twin_off%%` is
/// a fresh unconstrained boolean, while every `Assume` (including the fact
/// an assertion leaves behind) stays. Nothing proves the switch, so the
/// check is valid exactly when the hypotheses and the body's assumptions
/// contradict each other wherever a goal is reached; a twin that adds an
/// axiom checks this to tell a vacuous context from a proof. Stronger than
/// checking the hypotheses alone: it also finds an axiom that contradicts
/// what a call's postcondition or an earlier assertion assumed. The goal
/// stays in the formula (`false` in its place would be rewritten away with
/// it) so that its terms still seed the quantifiers' triggers.
pub fn goals_off(query: &Query) -> Query {
    let switch = Arc::new(crate::def::TWIN_OFF.to_owned());
    let mut local = (*query.local).clone();
    local.push(Arc::new(DeclX::Const(switch.clone(), crate::ast_util::bool_typ())));
    Arc::new(QueryX {
        local: Arc::new(local),
        assertion: goals_off_in(&query.assertion, &crate::ast_util::ident_var(&switch)),
    })
}

fn goals_off_in(stmt: &Stmt, switch: &Expr) -> Stmt {
    let recur = |s: &Stmt| goals_off_in(s, switch);
    match &**stmt {
        StmtX::Assert(id, error, filter, e) => {
            let off = crate::ast_util::mk_and(&vec![switch.clone(), e.clone()]);
            Arc::new(StmtX::Assert(id.clone(), error.clone(), filter.clone(), off))
        }
        StmtX::Block(stmts) => Arc::new(StmtX::Block(Arc::new(stmts.iter().map(recur).collect()))),
        StmtX::Switch(stmts) => {
            Arc::new(StmtX::Switch(Arc::new(stmts.iter().map(recur).collect())))
        }
        StmtX::DeadEnd(s) => Arc::new(StmtX::DeadEnd(recur(s))),
        StmtX::Breakable(label, s) => Arc::new(StmtX::Breakable(label.clone(), recur(s))),
        _ => stmt.clone(),
    }
}

/// `stmt` without the `Assume`s `drop` selects, and how many were removed.
pub fn remove_assumes(stmt: &Stmt, drop: &dyn Fn(&Expr) -> bool) -> (Stmt, usize) {
    let mut removed = 0;
    let stmt = remove_assumes_in(stmt, drop, &mut removed);
    (stmt, removed)
}

fn remove_assumes_in(stmt: &Stmt, drop: &dyn Fn(&Expr) -> bool, removed: &mut usize) -> Stmt {
    match &**stmt {
        StmtX::Block(stmts) => {
            let mut out = Vec::with_capacity(stmts.len());
            for s in stmts.iter() {
                if let StmtX::Assume(e) = &**s {
                    if drop(e) {
                        *removed += 1;
                        continue;
                    }
                }
                out.push(remove_assumes_in(s, drop, removed));
            }
            Arc::new(StmtX::Block(Arc::new(out)))
        }
        StmtX::Assume(e) if drop(e) => {
            *removed += 1;
            Arc::new(StmtX::Block(Arc::new(Vec::new())))
        }
        StmtX::DeadEnd(s) => Arc::new(StmtX::DeadEnd(remove_assumes_in(s, drop, removed))),
        StmtX::Breakable(label, s) => {
            Arc::new(StmtX::Breakable(label.clone(), remove_assumes_in(s, drop, removed)))
        }
        StmtX::Switch(stmts) => Arc::new(StmtX::Switch(Arc::new(
            stmts.iter().map(|s| remove_assumes_in(s, drop, removed)).collect(),
        ))),
        _ => stmt.clone(),
    }
}

/// One assertion that can move: its `Assert` at `start` in its block, and
/// `len` statements with the fact it leaves behind (`Assume` of the same
/// expression right after it), if any.
struct Movable {
    start: usize,
    len: usize,
}

/// `query` with the assertions `order` names moved into that order. They
/// must be sibling statements of one block; they take the positions they
/// held between them, in the given order, each with the fact it leaves
/// behind. Everything else stays where it was, so an assertion that moves
/// past an assignment sees the variable's value at its new place, as the
/// same move in source would.
pub fn reorder_asserts(query: &Query, order: &[AssertId]) -> Result<Query, String> {
    if order.len() < 2 {
        return Err("reorder_asserts needs at least two assertions".to_string());
    }
    for (i, id) in order.iter().enumerate() {
        if order[..i].contains(id) {
            return Err(format!("assertion {} is named twice", assert_id_text(id)));
        }
    }
    let mut done = false;
    let assertion = reorder_in(&query.assertion, order, &mut done)?;
    if !done {
        return Err(format!(
            "no block holds all of {} as sibling assertions; name assertions of one block, as check_session and provenance_bisect report their assert_id",
            order.iter().map(assert_id_text).collect::<Vec<_>>().join(", ")
        ));
    }
    Ok(Arc::new(QueryX { local: query.local.clone(), assertion }))
}

/// `[3, 1]` -> `3.1`.
pub fn assert_id_text(id: &AssertId) -> String {
    id.iter().map(|n| n.to_string()).collect::<Vec<_>>().join(".")
}

fn reorder_in(stmt: &Stmt, order: &[AssertId], done: &mut bool) -> Result<Stmt, String> {
    match &**stmt {
        StmtX::Block(stmts) => {
            let mut found: HashMap<usize, Movable> = HashMap::new();
            for (i, s) in stmts.iter().enumerate() {
                if let StmtX::Assert(Some(id), _, _, asserted) = &**s {
                    if let Some(k) = order.iter().position(|wanted| wanted == id) {
                        if found.contains_key(&k) {
                            return Err(format!(
                                "assertion {} appears twice in one block",
                                assert_id_text(id)
                            ));
                        }
                        let fact = matches!(
                            stmts.get(i + 1).map(|n| &**n),
                            Some(StmtX::Assume(assumed)) if crate::bisect::same_expr(asserted, assumed)
                        );
                        found.insert(k, Movable { start: i, len: if fact { 2 } else { 1 } });
                    }
                }
            }
            if found.len() == order.len() {
                *done = true;
                let mut slots: Vec<usize> = found.values().map(|m| m.start).collect();
                slots.sort();
                // slot j (the j-th earliest position) gets order[j]
                let by_start: HashMap<usize, usize> =
                    slots.iter().enumerate().map(|(j, start)| (*start, j)).collect();
                let mut out = Vec::with_capacity(stmts.len());
                let mut i = 0;
                while i < stmts.len() {
                    match by_start.get(&i) {
                        Some(&j) => {
                            let moved = &found[&j];
                            out.extend(stmts[moved.start..moved.start + moved.len].iter().cloned());
                            let here = found.values().find(|m| m.start == i).expect("slot");
                            i += here.len;
                        }
                        None => {
                            out.push(stmts[i].clone());
                            i += 1;
                        }
                    }
                }
                return Ok(Arc::new(StmtX::Block(Arc::new(out))));
            }
            if !found.is_empty() {
                return Err(format!(
                    "only {} of the {} assertions are siblings in the block holding {}",
                    found.len(),
                    order.len(),
                    assert_id_text(&order[*found.keys().min().expect("non-empty")])
                ));
            }
            let mut out = Vec::with_capacity(stmts.len());
            for s in stmts.iter() {
                out.push(if *done { s.clone() } else { reorder_in(s, order, done)? });
            }
            Ok(Arc::new(StmtX::Block(Arc::new(out))))
        }
        StmtX::DeadEnd(s) => Ok(Arc::new(StmtX::DeadEnd(reorder_in(s, order, done)?))),
        StmtX::Breakable(label, s) => {
            Ok(Arc::new(StmtX::Breakable(label.clone(), reorder_in(s, order, done)?)))
        }
        StmtX::Switch(stmts) => {
            let mut out = Vec::with_capacity(stmts.len());
            for s in stmts.iter() {
                out.push(if *done { s.clone() } else { reorder_in(s, order, done)? });
            }
            Ok(Arc::new(StmtX::Switch(Arc::new(out))))
        }
        _ => Ok(stmt.clone()),
    }
}

// ---------------------------------------------------------------------------
// Comparing two checks.

/// The key unnamed quantifiers share: cvc5 numbers them by order of
/// appearance, which two checks need not share.
pub const UNNAMED: &str = "(unnamed)";

/// One inference's instances of one quantifier in each check.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct InferenceDelta {
    /// cvc5's inference id, e.g. `QUANTIFIERS_INST_E_MATCHING`.
    pub inference: String,
    pub base: u64,
    pub twin: u64,
}

/// One quantifier's instances in each check.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct QuantDelta {
    /// The `:qid`, or `UNNAMED` for every quantifier without one.
    pub qid: String,
    pub base: u64,
    pub twin: u64,
    /// Attempts rejected as duplicates (same term vector, entailed, or same
    /// lemma), when `(get-info :inst-pressure)` answered.
    pub base_duplicates: u64,
    pub twin_duplicates: u64,
    /// By inference, when `(get-info :branch-profile)` answered; largest
    /// change first.
    pub inferences: Vec<InferenceDelta>,
}

impl QuantDelta {
    pub fn delta(&self) -> i64 {
        self.twin as i64 - self.base as i64
    }
}

/// How the instantiations of two checks differ, aligned by `(qid, inference)`.
#[derive(Clone, Debug, Default)]
pub struct InstDelta {
    pub base_total: u64,
    pub twin_total: u64,
    pub base_rounds: u64,
    pub twin_rounds: u64,
    /// Every quantifier either check instantiated or tried to, largest
    /// change first, then most instantiated, then by name.
    pub quantifiers: Vec<QuantDelta>,
    /// Whether both checks split their instances by inference.
    pub by_inference: bool,
}

/// What one check reported about its instantiations.
pub struct InstCounts<'a> {
    pub pressure: Option<&'a InstPressure>,
    pub profile: Option<&'a BranchProfile>,
}

#[derive(Default)]
struct Counts {
    added: u64,
    duplicates: u64,
    inferences: BTreeMap<String, u64>,
}

impl<'a> InstCounts<'a> {
    fn pressure(&self) -> Option<&'a InstPressure> {
        self.pressure.filter(|p| p.unparsed.is_none())
    }

    fn profile(&self) -> Option<&'a BranchProfile> {
        self.profile.filter(|p| p.unparsed.is_none())
    }

    /// How many instances the check added in all, when it reported them.
    pub fn total(&self) -> Option<u64> {
        self.counts().map(|(rows, _)| rows.values().map(|c| c.added).sum())
    }

    fn counts(&self) -> Option<(BTreeMap<String, Counts>, u64)> {
        let key =
            |qid: &str, named: bool| if named { qid.to_string() } else { UNNAMED.to_string() };
        let mut rows: BTreeMap<String, Counts> = BTreeMap::new();
        let rounds;
        match (self.pressure(), self.profile()) {
            (None, None) => return None,
            (Some(pressure), profile) => {
                rounds = pressure.rounds;
                for q in &pressure.quantifiers {
                    let row = rows.entry(key(&q.qid, q.named)).or_default();
                    row.added += q.instantiations;
                    row.duplicates += q.duplicate_eq + q.duplicate_ent + q.duplicate_lemma;
                }
                if let Some(profile) = profile {
                    for q in &profile.quantifiers {
                        let row = rows.entry(key(&q.qid, q.named)).or_default();
                        for (id, n) in &q.inferences {
                            *row.inferences.entry(id.clone()).or_default() += n;
                        }
                    }
                }
            }
            (None, Some(profile)) => {
                rounds = profile.rounds;
                for q in &profile.quantifiers {
                    let row = rows.entry(key(&q.qid, q.named)).or_default();
                    row.added += q.instantiations;
                    for (id, n) in &q.inferences {
                        *row.inferences.entry(id.clone()).or_default() += n;
                    }
                }
            }
        }
        Some((rows, rounds))
    }
}

/// Align two checks' instantiations by quantifier and inference. `None`
/// when either check reported none of its counters.
pub fn diff_instantiations(base: &InstCounts, twin: &InstCounts) -> Option<InstDelta> {
    let (base_rows, base_rounds) = base.counts()?;
    let (twin_rows, twin_rounds) = twin.counts()?;
    let by_inference = base.profile().is_some() && twin.profile().is_some();
    let empty = Counts::default();
    let mut qids: Vec<&String> = base_rows.keys().chain(twin_rows.keys()).collect();
    qids.sort();
    qids.dedup();
    let mut quantifiers: Vec<QuantDelta> = qids
        .into_iter()
        .map(|qid| {
            let b = base_rows.get(qid).unwrap_or(&empty);
            let t = twin_rows.get(qid).unwrap_or(&empty);
            let mut ids: Vec<&String> = b.inferences.keys().chain(t.inferences.keys()).collect();
            ids.sort();
            ids.dedup();
            let mut inferences: Vec<InferenceDelta> = if by_inference {
                ids.into_iter()
                    .map(|id| InferenceDelta {
                        inference: id.clone(),
                        base: b.inferences.get(id).copied().unwrap_or(0),
                        twin: t.inferences.get(id).copied().unwrap_or(0),
                    })
                    .collect()
            } else {
                Vec::new()
            };
            inferences.sort_by_key(|d| std::cmp::Reverse((d.twin as i64 - d.base as i64).abs()));
            QuantDelta {
                qid: qid.clone(),
                base: b.added,
                twin: t.added,
                base_duplicates: b.duplicates,
                twin_duplicates: t.duplicates,
                inferences,
            }
        })
        .collect();
    quantifiers.sort_by(|a, b| {
        b.delta()
            .abs()
            .cmp(&a.delta().abs())
            .then(b.base.max(b.twin).cmp(&a.base.max(a.twin)))
            .then(a.qid.cmp(&b.qid))
    });
    Some(InstDelta {
        base_total: base_rows.values().map(|c| c.added).sum(),
        twin_total: twin_rows.values().map(|c| c.added).sum(),
        base_rounds,
        twin_rounds,
        quantifiers,
        by_inference,
    })
}

/// One input assertion's difficulty in each check. `None` where the check
/// did not have the assertion, as after a removal or an addition.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TagDelta {
    /// Its provenance tags (several when hash-consing merged assertions).
    pub tags: Vec<String>,
    pub base: Option<u64>,
    pub twin: Option<u64>,
    pub base_in_core: Option<bool>,
    pub twin_in_core: Option<bool>,
}

impl TagDelta {
    pub fn delta(&self) -> i64 {
        self.twin.unwrap_or(0) as i64 - self.base.unwrap_or(0) as i64
    }
}

/// How two checks' difficulty gradients differ.
#[derive(Clone, Debug, Default)]
pub struct DifficultyDelta {
    /// Every tagged input assertion either check reported, largest change
    /// first.
    pub rows: Vec<TagDelta>,
    /// The base check's most difficult assertion, by its index in `rows`.
    pub hardest: Option<usize>,
    /// Whether both checks have an unsat core (both answered unsat).
    pub cores: bool,
    pub base_total: u64,
    pub twin_total: u64,
}

/// Align two difficulty gradients by their rows' tags. `None` when either
/// gradient did not parse or did not track difficulty.
pub fn diff_difficulty(
    base: &DifficultyGradient,
    twin: &DifficultyGradient,
) -> Option<DifficultyDelta> {
    if base.unparsed.is_some() || twin.unparsed.is_some() || !base.difficulty || !twin.difficulty {
        return None;
    }
    let key = |tags: &Vec<String>| {
        let mut tags = tags.clone();
        tags.sort();
        tags
    };
    let mut rows: BTreeMap<Vec<String>, TagDelta> = BTreeMap::new();
    for row in &base.rows {
        let entry = rows
            .entry(key(&row.tags))
            .or_insert_with(|| TagDelta { tags: key(&row.tags), ..Default::default() });
        entry.base = Some(entry.base.unwrap_or(0) + row.difficulty);
        entry.base_in_core = row.in_core.or(entry.base_in_core);
    }
    for row in &twin.rows {
        let entry = rows
            .entry(key(&row.tags))
            .or_insert_with(|| TagDelta { tags: key(&row.tags), ..Default::default() });
        entry.twin = Some(entry.twin.unwrap_or(0) + row.difficulty);
        entry.twin_in_core = row.in_core.or(entry.twin_in_core);
    }
    let mut rows: Vec<TagDelta> = rows.into_values().collect();
    rows.sort_by(|a, b| {
        b.delta()
            .abs()
            .cmp(&a.delta().abs())
            .then(b.base.unwrap_or(0).cmp(&a.base.unwrap_or(0)))
            .then(a.tags.cmp(&b.tags))
    });
    let hardest = rows
        .iter()
        .enumerate()
        .filter(|(_, r)| r.base.unwrap_or(0) > 0)
        .max_by(|(ia, a), (ib, b)| a.base.cmp(&b.base).then(ib.cmp(ia)))
        .map(|(i, _)| i);
    Some(DifficultyDelta {
        base_total: rows.iter().map(|r| r.base.unwrap_or(0)).sum(),
        twin_total: rows.iter().map(|r| r.twin.unwrap_or(0)).sum(),
        hardest,
        cores: base.core && twin.core,
        rows,
    })
}

/// Which input assertions were relevant in one check and not the other.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct RelevanceDelta {
    /// `unsat_core` when both checks answered unsat (relevant = in the
    /// core), else `difficulty` (relevant = some lemma work flowed through
    /// it, which misses assertions cvc5 substituted away).
    pub basis: &'static str,
    /// Indices into `DifficultyDelta::rows`.
    pub became_relevant: Vec<usize>,
    pub became_irrelevant: Vec<usize>,
}

pub fn relevance_delta(delta: &DifficultyDelta) -> RelevanceDelta {
    let relevant = |difficulty: Option<u64>, in_core: Option<bool>| {
        if delta.cores { in_core == Some(true) } else { difficulty.unwrap_or(0) > 0 }
    };
    let mut out = RelevanceDelta {
        basis: if delta.cores { "unsat_core" } else { "difficulty" },
        ..Default::default()
    };
    for (i, row) in delta.rows.iter().enumerate() {
        match (relevant(row.base, row.base_in_core), relevant(row.twin, row.twin_in_core)) {
            (false, true) => out.became_relevant.push(i),
            (true, false) => out.became_irrelevant.push(i),
            _ => {}
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{ExprX, MultiOp};
    use crate::context::{DifficultyRow, QuantInferences, QuantPressure};
    use crate::messages::AirMessageInterface;

    fn mi() -> Arc<dyn MessageInterface> {
        Arc::new(AirMessageInterface {})
    }

    fn query(text: &str) -> Query {
        let node = sise::parse_tree(&mut sise::Parser::new(text)).unwrap();
        let commands = crate::parser::Parser::new(mi()).nodes_to_commands(&[node]).unwrap();
        match &*commands[0] {
            crate::ast::CommandX::CheckValid(q) => q.clone(),
            _ => panic!("expected check-valid"),
        }
    }

    fn assert_ids(stmt: &Stmt, out: &mut Vec<String>) {
        match &**stmt {
            StmtX::Assert(Some(id), ..) => out.push(assert_id_text(id)),
            StmtX::Assume(_) => out.push("assume".to_string()),
            StmtX::Block(stmts) | StmtX::Switch(stmts) => {
                stmts.iter().for_each(|s| assert_ids(s, out))
            }
            StmtX::DeadEnd(s) | StmtX::Breakable(_, s) => assert_ids(s, out),
            _ => {}
        }
    }

    fn aid(v: &[u64]) -> AssertId {
        Arc::new(v.to_vec())
    }

    #[test]
    fn an_axiom_answers_to_its_tag_and_qid() {
        let q = query(
            "(check-valid
               (declare-fun f (Int) Int)
               (axiom (forall ((x Int)) (! (= (f x) x) :pattern ((f x)) :qid user_f_1 :skolemid skolem_user_f_1)))
               (block (assert true)))",
        );
        let DeclX::Axiom(axiom) = &*q.local[1] else { panic!() };
        assert!(axiom_named(axiom, "user_f_1"));
        assert!(axiom_named(axiom, "ax_user_f_1"));
        assert!(axiom_named(axiom, "|user_f_1|"));
        assert!(!axiom_named(axiom, "user_f"));
        let (twin, removed) = remove_local_axioms(&q, "user_f_1");
        assert_eq!(removed.len(), 1);
        assert_eq!(twin.local.len(), 1);
    }

    #[test]
    fn a_parsed_axiom_is_tagged_as_added() {
        let axiom = parse_axiom(mi(), "(forall ((x Int)) (> (f x) 0))").unwrap();
        assert_eq!(axiom.tag.as_ref().map(|t| t.to_symbol()).as_deref(), Some("ax_twin_added"));
        assert!(parse_axiom(mi(), "(> (f x) 0) extra").is_err());
    }

    #[test]
    fn asserts_move_with_their_facts() {
        // Verus spells assert(e) as an assert of e and an assume of e
        let q = query(
            "(check-valid
               (declare-const a Bool) (declare-const b Bool) (declare-const c Bool)
               (block
                 (assume a)
                 (assert aid_1 (\"a\") () a) (assume a)
                 (assert aid_2 (\"b\") () b) (assume b)
                 (assume c)
                 (assert aid_3 (\"c\") () c)))",
        );
        let twin = reorder_asserts(&q, &[aid(&[3]), aid(&[1])]).unwrap();
        let mut ids = Vec::new();
        assert_ids(&twin.assertion, &mut ids);
        assert_eq!(ids, ["assume", "3", "2", "assume", "assume", "1", "assume"]);
        assert!(reorder_asserts(&q, &[aid(&[3]), aid(&[9])]).is_err());
        assert!(reorder_asserts(&q, &[aid(&[3])]).is_err());
        assert!(reorder_asserts(&q, &[aid(&[3]), aid(&[3])]).is_err());
    }

    #[test]
    fn asserts_in_different_blocks_do_not_move() {
        let q = query(
            "(check-valid
               (declare-const a Bool) (declare-const b Bool)
               (block
                 (assert aid_1 (\"a\") () a)
                 (block (assert aid_2 (\"b\") () b))))",
        );
        let error = reorder_asserts(&q, &[aid(&[2]), aid(&[1])]).unwrap_err();
        assert!(error.contains("only 1 of the 2"), "{}", error);
    }

    #[test]
    fn goals_switch_off_and_assumptions_stay() {
        let q = query(
            "(check-valid
               (declare-const a Bool) (declare-const b Bool)
               (block (assume a) (assert aid_1 (\"a\") () a) (assume a) (block (assert b))))",
        );
        let off = goals_off(&q);
        let mut ids = Vec::new();
        assert_ids(&off.assertion, &mut ids);
        assert_eq!(ids, ["assume", "1", "assume"]);
        fn goals(stmt: &Stmt, out: &mut Vec<Expr>) {
            match &**stmt {
                StmtX::Assert(_, _, _, e) => out.push(e.clone()),
                StmtX::Block(stmts) => stmts.iter().for_each(|s| goals(s, out)),
                _ => {}
            }
        }
        let mut exprs = Vec::new();
        goals(&off.assertion, &mut exprs);
        assert_eq!(exprs.len(), 2);
        for e in &exprs {
            let ExprX::Multi(MultiOp::And, parts) = &**e else { panic!("{:?}", e) };
            assert!(matches!(&*parts[0], ExprX::Var(x) if x.as_str() == crate::def::TWIN_OFF));
            assert!(matches!(&*parts[1], ExprX::Var(_)));
        }
        // the switch is declared, and nothing constrains it
        assert_eq!(off.local.len(), q.local.len() + 1);
        assert!(matches!(&*off.local[2], DeclX::Const(x, _) if x.as_str() == crate::def::TWIN_OFF));
    }

    #[test]
    fn assumes_are_removed_where_they_are() {
        let q = query(
            "(check-valid
               (declare-const a Bool) (declare-const b Bool)
               (block (assume a) (block (assume b) (assume a)) (assert b)))",
        );
        let is_a = |e: &Expr| matches!(&**e, ExprX::Var(x) if x.as_str() == "a");
        let (stmt, removed) = remove_assumes(&q.assertion, &is_a);
        assert_eq!(removed, 2);
        let mut ids = Vec::new();
        assert_ids(&stmt, &mut ids);
        assert_eq!(ids, ["assume"]);
    }

    fn pressure(rows: &[(&str, u64, u64)]) -> InstPressure {
        InstPressure {
            rounds: 3,
            quantifiers: rows
                .iter()
                .map(|(qid, n, dup)| QuantPressure {
                    qid: qid.to_string(),
                    named: !qid.starts_with("quant_"),
                    instantiations: *n,
                    duplicate_eq: *dup,
                    ..Default::default()
                })
                .collect(),
            ..Default::default()
        }
    }

    fn profile(rows: &[(&str, &[(&str, u64)])]) -> BranchProfile {
        BranchProfile {
            rounds: 3,
            quantifiers: rows
                .iter()
                .map(|(qid, ids)| QuantInferences {
                    qid: qid.to_string(),
                    named: !qid.starts_with("quant_"),
                    instantiations: ids.iter().map(|(_, n)| n).sum(),
                    inferences: ids.iter().map(|(id, n)| (id.to_string(), *n)).collect(),
                })
                .collect(),
            ..Default::default()
        }
    }

    #[test]
    fn instantiations_align_by_quantifier_and_inference() {
        let (bp, bf) = (
            pressure(&[("loop", 700, 5), ("def", 12, 0), ("quant_0", 3, 0)]),
            profile(&[
                ("loop", &[("E_MATCHING", 690), ("CBQI_CONFLICT", 10)]),
                ("def", &[("E_MATCHING", 12)]),
                ("quant_0", &[("E_MATCHING", 3)]),
            ]),
        );
        let (tp, tf) = (
            pressure(&[("def", 10, 0), ("new", 4, 1), ("quant_7", 3, 0)]),
            profile(&[
                ("def", &[("E_MATCHING", 10)]),
                ("new", &[("E_MATCHING", 4)]),
                ("quant_7", &[("E_MATCHING", 3)]),
            ]),
        );
        let delta = diff_instantiations(
            &InstCounts { pressure: Some(&bp), profile: Some(&bf) },
            &InstCounts { pressure: Some(&tp), profile: Some(&tf) },
        )
        .unwrap();
        assert!(delta.by_inference);
        assert_eq!((delta.base_total, delta.twin_total), (715, 17));
        let qids: Vec<&str> = delta.quantifiers.iter().map(|q| q.qid.as_str()).collect();
        // unnamed quantifiers share one row, whatever cvc5 numbered them
        assert_eq!(qids, ["loop", "new", "def", UNNAMED]);
        let looping = &delta.quantifiers[0];
        assert_eq!((looping.base, looping.twin, looping.delta()), (700, 0, -700));
        assert_eq!(looping.base_duplicates, 5);
        assert_eq!(looping.inferences[0].inference, "E_MATCHING");
        assert_eq!((looping.inferences[0].base, looping.inferences[0].twin), (690, 0));
        assert_eq!(delta.quantifiers[3].delta(), 0);
    }

    #[test]
    fn a_missing_profile_leaves_counts_without_inferences() {
        let (bp, tp) = (pressure(&[("q", 2, 0)]), pressure(&[("q", 5, 0)]));
        let unsupported =
            BranchProfile { unparsed: Some("unsupported".into()), ..Default::default() };
        let delta = diff_instantiations(
            &InstCounts { pressure: Some(&bp), profile: Some(&unsupported) },
            &InstCounts { pressure: Some(&tp), profile: None },
        )
        .unwrap();
        assert!(!delta.by_inference);
        assert_eq!(delta.quantifiers[0].delta(), 3);
        assert!(delta.quantifiers[0].inferences.is_empty());
        assert!(
            diff_instantiations(
                &InstCounts { pressure: None, profile: None },
                &InstCounts { pressure: Some(&tp), profile: None },
            )
            .is_none()
        );
    }

    fn gradient(core: bool, rows: &[(&str, u64, bool)]) -> DifficultyGradient {
        DifficultyGradient {
            result: if core { "unsat" } else { "unknown" }.to_string(),
            difficulty: true,
            core,
            rows: rows
                .iter()
                .map(|(tag, d, in_core)| DifficultyRow {
                    tags: vec![tag.to_string()],
                    difficulty: *d,
                    in_core: core.then_some(*in_core),
                })
                .collect(),
            ..Default::default()
        }
    }

    #[test]
    fn difficulty_rows_align_by_tags() {
        let base =
            gradient(false, &[("query", 900, false), ("hyp_0", 40, false), ("ax_a", 5, false)]);
        let twin =
            gradient(true, &[("query", 20, true), ("hyp_0", 0, false), ("ax_twin_added", 3, true)]);
        let delta = diff_difficulty(&base, &twin).unwrap();
        assert!(!delta.cores);
        assert_eq!(delta.rows[0].tags, ["query"]);
        assert_eq!(delta.rows[delta.hardest.unwrap()].tags, ["query"]);
        assert_eq!((delta.base_total, delta.twin_total), (945, 23));
        let added = delta.rows.iter().find(|r| r.tags == ["ax_twin_added"]).unwrap();
        assert_eq!((added.base, added.twin), (None, Some(3)));
        // one side has no core, so relevance falls back to difficulty > 0
        let relevance = relevance_delta(&delta);
        assert_eq!(relevance.basis, "difficulty");
        let names =
            |ix: &[usize]| ix.iter().map(|&i| delta.rows[i].tags[0].clone()).collect::<Vec<_>>();
        assert_eq!(names(&relevance.became_relevant), ["ax_twin_added"]);
        let mut gone = names(&relevance.became_irrelevant);
        gone.sort();
        assert_eq!(gone, ["ax_a", "hyp_0"]);
    }

    #[test]
    fn relevance_reads_both_cores_when_both_are_unsat() {
        let base = gradient(true, &[("hyp_0", 4, true), ("hyp_1", 0, false)]);
        let twin = gradient(true, &[("hyp_0", 4, false), ("hyp_1", 0, true)]);
        let delta = diff_difficulty(&base, &twin).unwrap();
        let relevance = relevance_delta(&delta);
        assert_eq!(relevance.basis, "unsat_core");
        assert_eq!(delta.rows[relevance.became_relevant[0]].tags, ["hyp_1"]);
        assert_eq!(delta.rows[relevance.became_irrelevant[0]].tags, ["hyp_0"]);
    }

    #[test]
    fn branch_profile_replies_parse() {
        let p = crate::smt_verify::parse_branch_profile(
            "(:branch-profile (:resource-units 1234 :resource-limit 0 :rounds 4 :quantifiers ((loop :instantiations 4 :inferences ((QUANTIFIERS_INST_E_MATCHING 4))) (quant_0 :named false :instantiations 1 :inferences ((QUANTIFIERS_INST_CBQI_CONFLICT 1))) (|a b| :instantiations 0 :inferences ()))))",
        );
        assert_eq!(p.unparsed, None);
        assert_eq!((p.resource_units, p.resource_limit, p.rounds), (1234, 0, 4));
        assert_eq!(p.quantifiers.len(), 3);
        assert_eq!(p.quantifiers[0].inferences, [("QUANTIFIERS_INST_E_MATCHING".to_string(), 4)]);
        assert!(!p.quantifiers[1].named);
        assert_eq!(p.quantifiers[2].qid, "a b");
        let bad = crate::smt_verify::parse_branch_profile("(:branch-profile (:rounds x))");
        assert!(bad.unparsed.is_some());
    }
}
