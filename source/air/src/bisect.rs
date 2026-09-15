//! Toggle probes over one query, and the search that drives them
//! (`provenance_bisect`).
//!
//! A probe re-asks the solver about the query with some of its parts
//! switched off. Three kinds of part can be switched, each by one boolean
//! literal passed to `check-sat-assuming`, so the query's assertions are sent
//! once and never edited:
//!
//! - a *hypothesis*: a tagged `hyp_k` axiom of the query (a `requires`
//!   clause, type invariant, fuel setting or trait bound). It is asserted as
//!   `(=> guard h)`; a probe assumes `guard` to keep it, `(not guard)` to
//!   remove it.
//! - a *goal*: a labelled assertion, the thing the query has to prove. A probe
//!   removes it by assuming `(not label)`, the same toggle the multiple-error
//!   search uses. The goal is then no longer proved. Later goals still get
//!   it only through its fact (below), so a goal with no fact, such as a
//!   call's precondition or a postcondition, is simply not checked.
//! - a *fact*: what an assertion leaves behind. Verus spells `assert(e)` as an
//!   `Assert` of `e` followed by an `Assume` of `e`; that `Assume` becomes
//!   `(or drop e)`, and a probe assumes `(not drop)` to keep it, `drop` to
//!   remove it.
//!
//! Every probe of a query answers about a weaker query than the original (it
//! has fewer hypotheses or fewer goals), never about the original itself. The
//! search reports which parts, removed, change the answer; it never licenses
//! the original.
//!
//! Probes run in their own scope above the query's declaration prefix. The
//! scope is popped when the `Prober` is dropped, so the solver's committed
//! stack is the same afterwards. Hypotheses are guarded only inside that
//! scope, which also means the solver cannot substitute them away during
//! preprocessing the way it can in an ordinary check: a probe with nothing
//! removed can answer differently from the ordinary check near the resource
//! limit, and the search compares against the probe, not the check.
//!
//! An *ablation* prober (`Context::ablate_query`, for `ablate_to_witness`)
//! adds a fourth kind of part: an *axiom group*, every axiom of the query's
//! declaration prefix that one owner contributes (a function's definition, a
//! broadcast lemma, a broadcast group), each asserted as `(=> guard a)`.
//! Prefix axioms are asserted below the query's scope in an ordinary check,
//! so the prober asserts the whole prefix again in its own scope, above a
//! context popped back to the prelude. It also has a vacuity switch that
//! turns every goal into `false`: a probe with it on answers `valid` exactly
//! when the assumptions left in are contradictory on every path to a goal.

use crate::ast::{
    AssertId, Axiom, BinaryOp, BindX, Decl, DeclX, Expr, ExprX, Ident, MultiOp, Quant, Query,
    QueryX, Stmt, StmtX, TypX, TypeError, UnaryOp,
};
use crate::ast_util::{ident_var, mk_and, mk_implies, mk_not, mk_or};
use crate::context::{Context, SmtSolver};
use crate::def::{ABLATE_GUARD, ABLATE_VACUITY, BISECT_DROP, BISECT_GUARD, HypId, ProvenanceTag};
use crate::messages::ArcDynMessage;
use std::collections::HashMap;
use std::sync::Arc;

/// What a switchable part of a query is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum UnitKind {
    /// A tagged `hyp_k` axiom: `requires`, type invariant, fuel, trait bound.
    Hypothesis,
    /// A labelled assertion. Removed, it is not proved; later goals still get
    /// it only through its fact, if it has one.
    Goal,
    /// The assumption an assertion leaves behind for what follows it.
    Fact,
    /// Every prefix axiom of one owner, switched together (ablation only).
    Axiom,
}

/// One switchable part of a query.
#[derive(Clone, Debug)]
pub struct Unit {
    pub kind: UnitKind,
    /// A hypothesis's provenance tag, or the tag of the axiom in an axiom
    /// group that carries one (a broadcast lemma's, or a broadcast group's).
    pub tag: Option<ProvenanceTag>,
    /// A goal's `AssertId`, and for a fact the id of the assertion it follows.
    pub assert_id: Option<AssertId>,
    /// A goal's error message, and for a fact the one of its assertion. The
    /// message's spans say where the assertion is.
    pub error: Option<ArcDynMessage>,
    /// An axiom group's owner, as the caller of `ablate_query` named it.
    pub group: Option<String>,
    /// How many prefix axioms an axiom group switches.
    pub axioms: usize,
    /// The `:qid`s of the quantifiers in an axiom group's axioms.
    pub qids: Vec<String>,
    literal: Ident,
    /// Where the unit sits among its kind in the query, for a stable order.
    position: usize,
}

impl Unit {
    fn new(kind: UnitKind, literal: Ident, position: usize) -> Self {
        Unit {
            kind,
            tag: None,
            assert_id: None,
            error: None,
            group: None,
            axioms: 0,
            qids: Vec::new(),
            literal,
            position,
        }
    }

    /// The ordering the search splits along: axiom groups in prefix order,
    /// hypotheses by index, then goals and facts by `AssertId`, each fact
    /// right after its goal. A proof subtree (ids sharing a prefix) is
    /// therefore one contiguous run.
    fn sort_key(&self) -> (u8, Vec<u64>, u8, usize) {
        match self.kind {
            UnitKind::Axiom => (0, Vec::new(), 0, self.position),
            UnitKind::Hypothesis => {
                let index = match &self.tag {
                    Some(ProvenanceTag::Hyp(HypId(n))) => *n,
                    _ => u64::MAX,
                };
                (1, vec![index], 0, self.position)
            }
            UnitKind::Goal | UnitKind::Fact => {
                let path = match &self.assert_id {
                    Some(id) => (**id).clone(),
                    None => vec![u64::MAX],
                };
                (2, path, (self.kind == UnitKind::Fact) as u8, self.position)
            }
        }
    }
}

/// The `:qid` of the quantifier an axiom is, or guards, as the solver will
/// be told it.
pub fn axiom_qid(expr: &Expr) -> Option<Ident> {
    crate::smt_verify::axiom_qid(expr)
}

/// Every `:qid` of a quantifier inside `expr`, in first-seen order.
fn collect_qids(expr: &Expr, qids: &mut Vec<String>) {
    crate::visitor::map_expr_visitor(expr, &mut |e: &Expr| {
        if let ExprX::Bind(bind, _) = &**e {
            if let BindX::Quant(_, _, _, Some(qid)) = &**bind {
                if !qids.iter().any(|q| q == &**qid) {
                    qids.push((**qid).clone());
                }
            }
        }
        e.clone()
    });
}

/// Under `switch`, every goal of `expr` becomes `false`: each labelled
/// assertion `e` is rewritten to `(and (not switch) e)`. Walks the positions
/// `label_asserts` labels, so every goal it labels is rewritten.
fn goals_false_under(expr: &Expr, switch: &Ident) -> Expr {
    let recur = |e: &Expr| goals_false_under(e, switch);
    match &**expr {
        ExprX::Binary(op @ (BinaryOp::Implies | BinaryOp::Eq), lhs, rhs) => {
            Arc::new(ExprX::Binary(op.clone(), lhs.clone(), recur(rhs)))
        }
        ExprX::Multi(op @ (MultiOp::And | MultiOp::Or), exprs) => {
            Arc::new(ExprX::Multi(*op, Arc::new(exprs.iter().map(recur).collect())))
        }
        ExprX::Bind(bind, body) if matches!(&**bind, BindX::Quant(Quant::Forall, _, _, _)) => {
            Arc::new(ExprX::Bind(bind.clone(), recur(body)))
        }
        ExprX::LabeledAssertion(assert_id, error, filter, e) => {
            let off = mk_and(&vec![mk_not(&ident_var(switch)), recur(e)]);
            Arc::new(ExprX::LabeledAssertion(assert_id.clone(), error.clone(), filter.clone(), off))
        }
        ExprX::LabeledAxiom(labels, filter, e) => {
            Arc::new(ExprX::LabeledAxiom(labels.clone(), filter.clone(), recur(e)))
        }
        _ => expr.clone(),
    }
}

/// The units whose `AssertId` starts with `prefix`: one subtree of the proof.
/// Units without an id (hypotheses, some goals) are never under a prefix.
pub fn units_under_prefix(units: &[Unit], prefix: &[u64]) -> Vec<usize> {
    units
        .iter()
        .enumerate()
        .filter(|(_, u)| u.assert_id.as_ref().is_some_and(|id| id.starts_with(prefix)))
        .map(|(i, _)| i)
        .collect()
}

/// What one probe answered.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Answer {
    /// `unsat`: the (weakened) query is proved.
    Valid,
    /// `sat`: the solver found a counterexample.
    Invalid,
    /// `unknown`, with the solver's `:reason-unknown` (empty if it gave none).
    Unknown(String),
}

impl Answer {
    pub fn result(&self) -> &'static str {
        match self {
            Answer::Valid => "valid",
            Answer::Invalid => "invalid",
            Answer::Unknown(_) => "unknown",
        }
    }

    pub fn reason(&self) -> Option<&str> {
        match self {
            Answer::Unknown(reason) if !reason.is_empty() => Some(reason),
            _ => None,
        }
    }

    /// The classes a `Changed` search tells apart: the result, and for
    /// `unknown` whether the solver ran out of budget or gave up.
    pub fn class(&self) -> &'static str {
        match self {
            Answer::Valid => "valid",
            Answer::Invalid => "invalid",
            Answer::Unknown(reason) => {
                let reason = reason.as_str();
                if matches!(reason, "resourceout" | "timeout" | "canceled")
                    || reason.contains("resource limit")
                {
                    "resource_limit"
                } else if reason.contains("incomplete") {
                    "incomplete"
                } else {
                    "unknown"
                }
            }
        }
    }
}

/// A fact switch minted while rewriting the query.
struct Fact {
    switch: Ident,
    assert_id: Option<AssertId>,
    error: ArcDynMessage,
}

/// Whether two expressions are the same term. Verus asserts and then assumes
/// one expression, usually a temporary, so the cheap checks nearly always
/// decide.
fn same_expr(a: &Expr, b: &Expr) -> bool {
    Arc::ptr_eq(a, b)
        || match (&**a, &**b) {
            (ExprX::Var(x), ExprX::Var(y)) => x == y,
            (ExprX::Var(_), _) | (_, ExprX::Var(_)) => false,
            _ => format!("{:?}", a) == format!("{:?}", b),
        }
}

/// Give each fact an assertion leaves behind a switch: within a block, an
/// `Assert` of `e` immediately followed by an `Assume` of `e` has that
/// `Assume` rewritten to `(or switch e)`.
fn mark_facts(stmt: &Stmt, facts: &mut Vec<Fact>) -> Stmt {
    match &**stmt {
        StmtX::Block(stmts) => {
            let mut out = Vec::with_capacity(stmts.len());
            let mut i = 0;
            while i < stmts.len() {
                if let (StmtX::Assert(assert_id, error, _, asserted), Some(next)) =
                    (&*stmts[i], stmts.get(i + 1))
                {
                    if let StmtX::Assume(assumed) = &**next {
                        if same_expr(asserted, assumed) {
                            let switch = Arc::new(format!("{}{}", BISECT_DROP, facts.len()));
                            let kept = mk_or(&vec![ident_var(&switch), assumed.clone()]);
                            facts.push(Fact {
                                switch,
                                assert_id: assert_id.clone(),
                                error: error.clone(),
                            });
                            out.push(stmts[i].clone());
                            out.push(Arc::new(StmtX::Assume(kept)));
                            i += 2;
                            continue;
                        }
                    }
                }
                out.push(mark_facts(&stmts[i], facts));
                i += 1;
            }
            Arc::new(StmtX::Block(Arc::new(out)))
        }
        StmtX::DeadEnd(s) => Arc::new(StmtX::DeadEnd(mark_facts(s, facts))),
        StmtX::Breakable(label, s) => {
            Arc::new(StmtX::Breakable(label.clone(), mark_facts(s, facts)))
        }
        StmtX::Switch(stmts) => {
            Arc::new(StmtX::Switch(Arc::new(stmts.iter().map(|s| mark_facts(s, facts)).collect())))
        }
        _ => stmt.clone(),
    }
}

/// A query asserted with its parts switchable, in its own scope. Dropping it
/// pops the scope.
pub struct Prober<'c> {
    context: &'c mut Context,
    units: Vec<Unit>,
    checks: usize,
    /// The switch that turns every goal into `false` (ablation only).
    vacuity: Option<Ident>,
    /// The scope was opened with `Context::push`, so the AIR logs saw it too.
    air_scope: bool,
}

/// What a detailed probe read from the solver besides its answer.
#[derive(Clone, Debug, Default)]
pub struct ProbeDetail {
    /// cvc5's `(get-info :incomplete-id)` after an `unknown`, when it says.
    pub incomplete_id: Option<String>,
    /// Instances made during the probe, per `:qid`, from cvc5's
    /// `(get-info :inst-pressure)`. `None` when the solver cannot say.
    pub instantiations: Option<HashMap<String, u64>>,
}

/// Type-check and lower `query`, giving each fact an assertion leaves behind
/// its switch (declared among the query's locals).
fn prepare(context: &mut Context, query: &Query) -> Result<(Query, Vec<Fact>), TypeError> {
    let query = crate::typecheck::check_query(context, query)?;
    let (query, _, _, _) = crate::var_to_const::lower_query(&query, false);
    let mut facts = Vec::new();
    let assertion = mark_facts(&query.assertion, &mut facts);
    let mut local = (*query.local).clone();
    for fact in &facts {
        local.push(Arc::new(DeclX::Const(fact.switch.clone(), Arc::new(TypX::Bool))));
    }
    let query = Arc::new(QueryX { local: Arc::new(local), assertion });
    let message_interface = context.message_interface.clone();
    Ok((crate::block_to_assert::lower_query(&*message_interface, &query), facts))
}

impl Context {
    /// Assert `query` in a new scope with every hypothesis, goal and fact
    /// switchable (see the module documentation), ready for `Prober::probe`.
    /// The context must be ready for a query, at the query's declaration
    /// prefix; the query's resource budget is the context's current one.
    pub fn bisect_query(&mut self, query: &Query) -> Result<Prober<'_>, TypeError> {
        self.ensure_started();
        let (query, facts) = prepare(self, query)?;

        self.smt_log.log_push();
        self.push_name_scope();
        match assert_switchable(self, &query, facts, None) {
            Ok(mut units) => {
                units.sort_by_key(|u| u.sort_key());
                Ok(Prober { context: self, units, checks: 0, vacuity: None, air_scope: false })
            }
            Err(err) => {
                self.pop_name_scope();
                self.smt_log.log_pop();
                Err(err)
            }
        }
    }

    /// Assert the declaration `prefix` and then `query` in a new scope, with
    /// the prefix's axioms switchable in groups as well as the query's own
    /// hypotheses, goals and facts, and with a vacuity switch. `group_of`
    /// names the group of each prefix axiom; axioms it names `None` for, and
    /// every other declaration, are asserted as they are. The context must be
    /// ready for a query with none of `prefix` asserted (for a resident
    /// query, its journal popped back to the prelude); the query's resource
    /// budget is the context's current one.
    pub fn ablate_query(
        &mut self,
        prefix: &[Decl],
        group_of: &mut dyn FnMut(&Axiom) -> Option<String>,
        query: &Query,
    ) -> Result<Prober<'_>, TypeError> {
        self.push();
        let vacuity = Arc::new(ABLATE_VACUITY.to_string());
        let asserted = assert_groups(self, prefix, group_of).and_then(|mut units| {
            self.global(&Arc::new(DeclX::Const(vacuity.clone(), Arc::new(TypX::Bool))))?;
            let (query, facts) = prepare(self, query)?;
            units.extend(assert_switchable(self, &query, facts, Some(&vacuity))?);
            Ok(units)
        });
        match asserted {
            Ok(mut units) => {
                units.sort_by_key(|u| u.sort_key());
                Ok(Prober {
                    context: self,
                    units,
                    checks: 0,
                    vacuity: Some(vacuity),
                    air_scope: true,
                })
            }
            Err(err) => {
                self.pop();
                Err(err)
            }
        }
    }
}

/// Assert `prefix` into the current scope, each axiom `group_of` names a
/// group for guarded by that group's switch, returning one unit per group.
fn assert_groups(
    context: &mut Context,
    prefix: &[Decl],
    group_of: &mut dyn FnMut(&Axiom) -> Option<String>,
) -> Result<Vec<Unit>, TypeError> {
    let mut units: Vec<Unit> = Vec::new();
    let mut by_group: HashMap<String, usize> = HashMap::new();
    for decl in prefix {
        let group = match &**decl {
            DeclX::Axiom(axiom) => group_of(axiom).map(|group| (axiom, group)),
            _ => None,
        };
        let Some((axiom, group)) = group else {
            context.global(decl)?;
            continue;
        };
        let at = match by_group.get(&group) {
            Some(&at) => at,
            None => {
                let at = units.len();
                let literal = Arc::new(format!("{}{}", ABLATE_GUARD, at));
                context.global(&Arc::new(DeclX::Const(literal.clone(), Arc::new(TypX::Bool))))?;
                let mut unit = Unit::new(UnitKind::Axiom, literal, at);
                unit.group = Some(group.clone());
                units.push(unit);
                by_group.insert(group, at);
                at
            }
        };
        let unit = &mut units[at];
        unit.axioms += 1;
        collect_qids(&axiom.expr, &mut unit.qids);
        if unit.tag.is_none() {
            unit.tag = axiom.tag.clone();
        }
        context.global(&Arc::new(DeclX::Axiom(Axiom {
            named: axiom.named.clone(),
            tag: axiom.tag.clone(),
            expr: mk_implies(&ident_var(&unit.literal), &axiom.expr),
        })))?;
    }
    Ok(units)
}

/// Declare and assert the lowered `query` into the current scope with its
/// hypotheses guarded and its goal labels declared, returning the units.
/// Under `vacuity`, every goal becomes `false`.
fn assert_switchable(
    context: &mut Context,
    query: &Query,
    facts: Vec<Fact>,
    vacuity: Option<&Ident>,
) -> Result<Vec<Unit>, TypeError> {
    use crate::smt_verify::smt_add_decl;
    use crate::typecheck::add_decl;
    let mut units = Vec::new();
    for (position, decl) in query.local.iter().enumerate() {
        match &**decl {
            DeclX::Axiom(Axiom { named, tag: Some(tag @ ProvenanceTag::Hyp(_)), expr }) => {
                let guard = Arc::new(format!("{}{}", BISECT_GUARD, units.len()));
                let guard_decl = Arc::new(DeclX::Const(guard.clone(), Arc::new(TypX::Bool)));
                add_decl(context, &guard_decl, false)?;
                smt_add_decl(context, &guard_decl);
                let guarded = Arc::new(DeclX::Axiom(Axiom {
                    named: named.clone(),
                    tag: Some(tag.clone()),
                    expr: mk_implies(&ident_var(&guard), expr),
                }));
                add_decl(context, &guarded, false)?;
                smt_add_decl(context, &guarded);
                let mut unit = Unit::new(UnitKind::Hypothesis, guard, position);
                unit.tag = Some(tag.clone());
                collect_qids(expr, &mut unit.qids);
                units.push(unit);
            }
            _ => {
                add_decl(context, decl, false)?;
                smt_add_decl(context, decl);
            }
        }
    }

    let assertion = match &*query.assertion {
        StmtX::Assert(_, _, _, expr) => expr,
        _ => panic!("internal error: query not lowered"),
    };
    let mut assertion = crate::smt_verify::elim_zero_args_expr(assertion);
    if let Some(vacuity) = vacuity {
        assertion = goals_false_under(&assertion, vacuity);
    }
    let mut infos = Vec::new();
    let mut axiom_infos = Vec::new();
    let labeled =
        crate::smt_verify::label_asserts(context, &mut infos, &mut axiom_infos, &assertion);
    for info in &infos {
        context.smt_log.comment(&context.message_interface.get_note(&info.error));
        add_decl(context, &info.decl, false)?;
        smt_add_decl(context, &info.decl);
    }
    for (position, info) in infos.into_iter().enumerate() {
        let mut unit = Unit::new(UnitKind::Goal, info.label, position);
        unit.assert_id = info.assert_id;
        unit.error = Some(info.error);
        units.push(unit);
    }
    for (position, fact) in facts.into_iter().enumerate() {
        let mut unit = Unit::new(UnitKind::Fact, fact.switch, position);
        unit.assert_id = fact.assert_id;
        unit.error = Some(fact.error);
        units.push(unit);
    }
    let not_expr = Arc::new(ExprX::Unary(UnaryOp::Not, labeled));
    let query_tag = if context.emit_assert_ids { Some(ProvenanceTag::Query) } else { None };
    context.smt_log.log_assert(&None, &query_tag, &not_expr);
    Ok(units)
}

impl<'c> Prober<'c> {
    /// The switchable parts, in the order the search splits along.
    pub fn units(&self) -> &[Unit] {
        &self.units
    }

    /// How many probes have run.
    pub fn checks(&self) -> usize {
        self.checks
    }

    /// Ask the solver about the query with `disabled[i]` switching off
    /// `units()[i]`, under the query's resource budget. An `Err` carries
    /// solver output this could not read.
    pub fn probe(&mut self, disabled: &[bool]) -> Result<Answer, String> {
        self.run(disabled, false, false).map(|(answer, _)| answer)
    }

    /// `probe`, also reading what the solver says about the answer: for
    /// cvc5, the instances made per `:qid` and, after `unknown`, its
    /// `IncompleteId`. A solver that cannot say leaves the detail empty.
    pub fn probe_detailed(&mut self, disabled: &[bool]) -> Result<(Answer, ProbeDetail), String> {
        self.run(disabled, false, true)
    }

    /// `probe` with every goal replaced by `false` (ablation probers only):
    /// `valid` means the assumptions left under `disabled` contradict each
    /// other on every path to a goal.
    pub fn probe_vacuity(&mut self, disabled: &[bool]) -> Result<Answer, String> {
        if self.vacuity.is_none() {
            return Err("this prober has no vacuity switch".to_string());
        }
        self.run(disabled, true, false).map(|(answer, _)| answer)
    }

    fn run(
        &mut self,
        disabled: &[bool],
        vacuous: bool,
        detailed: bool,
    ) -> Result<(Answer, ProbeDetail), String> {
        assert_eq!(disabled.len(), self.units.len());
        let mut literals = Vec::new();
        for (unit, &off) in self.units.iter().zip(disabled) {
            let var = ident_var(&unit.literal);
            match (unit.kind, off) {
                (UnitKind::Hypothesis | UnitKind::Axiom, false) | (UnitKind::Fact, true) => {
                    literals.push(var)
                }
                (UnitKind::Hypothesis | UnitKind::Axiom, true)
                | (UnitKind::Fact, false)
                | (UnitKind::Goal, true) => literals.push(mk_not(&var)),
                (UnitKind::Goal, false) => {}
            }
        }
        if let Some(switch) = &self.vacuity {
            let var = ident_var(switch);
            literals.push(if vacuous { var } else { mk_not(&var) });
        }
        let context = &mut *self.context;
        let detailed = detailed && matches!(context.solver, SmtSolver::Cvc5);
        match context.solver {
            SmtSolver::Z3 => {
                context.smt_log.log_set_option("rlimit", &context.rlimit.to_string());
                context.set_z3_param_u32("rlimit", context.rlimit, false);
            }
            SmtSolver::Cvc5 => {
                let budget = crate::smt_verify::cvc5_query_budget(context);
                context.smt_log.log_set_option("reproducible-resource-limit", &budget.to_string());
            }
        }
        context.smt_log.log_check_sat_assuming(&literals);
        if detailed {
            // in the same batch, right after the answer it describes
            context.smt_log.log_get_info("inst-pressure");
        }
        let smt_data = context.smt_log.take_pipe_data();
        let smt_run_start_time = std::time::Instant::now();
        let output = context.get_smt_process().send_commands(smt_data);
        context.time_smt_run += smt_run_start_time.elapsed();
        self.checks += 1;
        match context.solver {
            SmtSolver::Z3 => {
                context.smt_log.log_set_option("rlimit", "0");
                context.set_z3_param_u32("rlimit", 0, false);
            }
            SmtSolver::Cvc5 => context.smt_log.log_set_option("reproducible-resource-limit", "0"),
        }
        let mut answer = None;
        let mut detail = ProbeDetail::default();
        for line in output {
            if detailed && line.starts_with("(:inst-pressure") {
                let pressure = crate::smt_verify::parse_inst_pressure(&line);
                if pressure.unparsed.is_none() {
                    detail.instantiations = Some(
                        pressure
                            .quantifiers
                            .iter()
                            .map(|q| (q.qid.clone(), q.instantiations))
                            .collect(),
                    );
                }
                continue;
            }
            // a cvc5 without the key
            if detailed && line == "unsupported" {
                continue;
            }
            let this = match line.as_str() {
                "unsat" => Answer::Valid,
                "sat" => Answer::Invalid,
                "unknown" => Answer::Unknown(String::new()),
                "cvc5 interrupted by timeout." => Answer::Unknown("timeout".to_string()),
                // provenance mode's solver dumps instantiations after each
                // check; probes do not read them
                _ if context.ignore_unexpected_smt || context.provenance => continue,
                _ => return Err(format!("unexpected SMT output: {}", line)),
            };
            if answer.replace(this).is_some() {
                return Err("two answers to one check-sat-assuming".to_string());
            }
        }
        let mut answer =
            answer.ok_or_else(|| "expected sat/unsat/unknown from SMT solver".to_string())?;
        if let Answer::Unknown(reason) = &mut answer {
            if reason.is_empty() || detailed {
                if reason.is_empty() {
                    context.smt_log.log_get_info("reason-unknown");
                }
                if detailed {
                    // cvc5 records it when check-sat returns
                    context.smt_log.log_get_info("incomplete-id");
                }
                let smt_data = context.smt_log.take_pipe_data();
                for line in context.get_smt_process().send_commands(smt_data) {
                    if let Some(r) =
                        line.strip_prefix("(:reason-unknown ").and_then(|s| s.strip_suffix(')'))
                    {
                        *reason = r.trim_matches('"').to_owned();
                    } else if let Some(id) =
                        line.strip_prefix("(:incomplete-id ").and_then(|s| s.strip_suffix(')'))
                    {
                        if id != "NONE" {
                            detail.incomplete_id = Some(id.to_owned());
                        }
                    }
                }
            }
        }
        Ok((answer, detail))
    }
}

impl<'c> Drop for Prober<'c> {
    fn drop(&mut self) {
        if self.air_scope {
            self.context.pop();
        } else {
            self.context.pop_name_scope();
            self.context.smt_log.log_pop();
        }
    }
}

// ---------------------------------------------------------------------------
// The search. It sees units only as indices and the solver only as a probe
// function, so it is tested without one.

/// What a flip search is looking for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    /// Probes answering `valid`: which removals make the rest provable.
    Valid,
    /// Probes answering anything but `valid`: which removals break a proof.
    NotValid,
    /// Probes answering in a different class (see `Answer::class`).
    Changed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// The smallest set of candidates whose removal reaches the target.
    Flip(Target),
    /// For a valid query, the smallest set of candidates that has to stay for
    /// it to remain valid when every other candidate is removed.
    Core,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Status {
    /// `set` is the answer; `minimal` says whether it was shown minimal.
    Found,
    /// The query already answers as the target asks: nothing to remove.
    AlreadyAtTarget,
    /// No removal that was tried reaches the target, including removing
    /// every candidate.
    Unreachable,
    /// Core mode asks what a proof needs, and the query is not valid.
    NotValid,
    /// No unit passed the filters.
    NoCandidates,
    /// The budget ran out before any set was established.
    BudgetExhausted,
}

/// One probe the search ran: which units were switched off, and the answer.
#[derive(Clone, Debug)]
pub struct ProbeRecord {
    pub disabled: Vec<usize>,
    pub answer: Answer,
}

#[derive(Clone, Debug)]
pub struct Outcome {
    /// The probe with nothing removed.
    pub before: Option<Answer>,
    pub status: Status,
    /// Flip: the units removed. Core: the units kept, every other candidate
    /// removed.
    pub set: Vec<usize>,
    /// The probe of `set` (flip: removed; core: every other candidate
    /// removed). `None` unless the status is `Found`.
    pub after: Option<Answer>,
    /// The probe with every candidate removed, when the search ran it.
    pub all_removed: Option<Answer>,
    /// Whether putting back any one member of `set` (flip), or removing any
    /// one (core), was probed and loses the result. Not a claim about sets the
    /// search did not try: probes need not be monotone.
    pub minimal: bool,
    /// Found only after removing everything failed, by trying one unit at a
    /// time: removals interact non-monotonically here.
    pub non_monotone: bool,
    /// Core only: keeping just the `core_start` hint kept the query valid,
    /// so the search shrank the hint rather than every candidate.
    pub hint_accepted: bool,
    pub probes: Vec<ProbeRecord>,
}

/// Runs probes, remembering answers, until the budget runs out.
struct Oracle<'p, E> {
    units: usize,
    budget: usize,
    probe: &'p mut dyn FnMut(&[bool]) -> Result<Answer, E>,
    memo: HashMap<Vec<usize>, Answer>,
    probes: Vec<ProbeRecord>,
}

impl<'p, E> Oracle<'p, E> {
    /// The answer with the sorted `disabled` units switched off, or `None`
    /// once the budget is spent.
    fn ask(&mut self, disabled: &[usize]) -> Result<Option<Answer>, E> {
        if let Some(answer) = self.memo.get(disabled) {
            return Ok(Some(answer.clone()));
        }
        if self.probes.len() >= self.budget {
            return Ok(None);
        }
        let mut mask = vec![false; self.units];
        for &i in disabled {
            mask[i] = true;
        }
        let answer = (self.probe)(&mask)?;
        self.memo.insert(disabled.to_vec(), answer.clone());
        self.probes.push(ProbeRecord { disabled: disabled.to_vec(), answer: answer.clone() });
        Ok(Some(answer))
    }
}

/// `set` without the members of `remove`, both sorted.
fn minus(set: &[usize], remove: &[usize]) -> Vec<usize> {
    set.iter().copied().filter(|x| remove.binary_search(x).is_err()).collect()
}

/// `set` in `n` contiguous chunks of near-equal size.
fn chunks(set: &[usize], n: usize) -> Vec<Vec<usize>> {
    let n = n.min(set.len()).max(1);
    (0..n).map(|i| set[i * set.len() / n..(i + 1) * set.len() / n].to_vec()).collect()
}

/// Delta debugging (Zeller's ddmin) for a smallest `set` on which `test`
/// holds, given that it holds on `set`. `test` answers `None` when the budget
/// is spent, and the set reached so far comes back with `false`. With `true`
/// the result is 1-minimal: `test` was run on the result minus each member
/// and failed every time (or the result has one member and the caller knows
/// `test` fails on the empty set).
fn ddmin<E>(
    mut set: Vec<usize>,
    test: &mut dyn FnMut(&[usize]) -> Result<Option<bool>, E>,
) -> Result<(Vec<usize>, bool), E> {
    let mut n = 2;
    while set.len() >= 2 {
        let parts = chunks(&set, n);
        let mut reduced = false;
        for part in &parts {
            match test(part)? {
                None => return Ok((set, false)),
                Some(true) => {
                    set = part.clone();
                    n = 2;
                    reduced = true;
                    break;
                }
                Some(false) => {}
            }
        }
        // With two parts each complement is the other part, already tested.
        if !reduced && parts.len() > 2 {
            for part in &parts {
                let complement = minus(&set, part);
                match test(&complement)? {
                    None => return Ok((set, false)),
                    Some(true) => {
                        set = complement;
                        n = (n - 1).max(2);
                        reduced = true;
                        break;
                    }
                    Some(false) => {}
                }
            }
        }
        if !reduced {
            if n >= set.len() {
                break;
            }
            n = (2 * n).min(set.len());
        }
    }
    Ok((set, true))
}

/// Search over `candidates` (indices into `units` many units, in the order to
/// split along) with at most `budget` probes. `probe(disabled)` asks with
/// `disabled[i]` switching off unit `i`. `before`, when given, is what a probe
/// with nothing disabled already answered; it counts toward the budget.
pub fn search<E>(
    mode: Mode,
    units: usize,
    candidates: &[usize],
    budget: usize,
    before: Option<Answer>,
    probe: &mut dyn FnMut(&[bool]) -> Result<Answer, E>,
) -> Result<Outcome, E> {
    search_ordered(mode, units, candidates, &[], &[], budget, before, probe)
}

/// `search`, with two hints. When removing every candidate misses a flip
/// target and single units are tried instead, the units of `order` are tried
/// first, in that order, and then the remaining candidates: an ablation
/// orders them by how often the solver instantiated them, so a matching
/// loop's lemma, the most instantiated by definition, comes up in the first
/// few probes. A core search first tries keeping only `core_start`, and when
/// that alone keeps the query valid, shrinks it instead of every candidate
/// (`Outcome::hint_accepted`). Neither hint changes what counts as an answer.
pub fn search_ordered<E>(
    mode: Mode,
    units: usize,
    candidates: &[usize],
    order: &[usize],
    core_start: &[usize],
    budget: usize,
    before: Option<Answer>,
    probe: &mut dyn FnMut(&[bool]) -> Result<Answer, E>,
) -> Result<Outcome, E> {
    let mut candidates = candidates.to_vec();
    candidates.sort();
    candidates.dedup();
    let mut oracle = Oracle { units, budget, probe, memo: HashMap::new(), probes: Vec::new() };
    if let Some(before) = before {
        oracle.memo.insert(Vec::new(), before.clone());
        oracle.probes.push(ProbeRecord { disabled: Vec::new(), answer: before });
    }
    let mut outcome = Outcome {
        before: None,
        status: Status::BudgetExhausted,
        set: Vec::new(),
        after: None,
        all_removed: None,
        minimal: false,
        non_monotone: false,
        hint_accepted: false,
        probes: Vec::new(),
    };
    let finish = |mut outcome: Outcome, oracle: Oracle<'_, E>| {
        if !candidates.is_empty() {
            outcome.all_removed = oracle.memo.get(&candidates).cloned();
        }
        outcome.probes = oracle.probes;
        Ok(outcome)
    };
    let Some(before) = oracle.ask(&[])? else { return finish(outcome, oracle) };
    outcome.before = Some(before.clone());
    match mode {
        Mode::Flip(target) => {
            let hits = |answer: &Answer| match target {
                Target::Valid => *answer == Answer::Valid,
                Target::NotValid => *answer != Answer::Valid,
                Target::Changed => answer.class() != before.class(),
            };
            if hits(&before) {
                outcome.status = Status::AlreadyAtTarget;
                return finish(outcome, oracle);
            }
            if candidates.is_empty() {
                outcome.status = Status::NoCandidates;
                return finish(outcome, oracle);
            }
            let Some(all) = oracle.ask(&candidates)? else { return finish(outcome, oracle) };
            let start = if hits(&all) {
                candidates.clone()
            } else {
                // Removing everything overshoots or introduces a new failure:
                // try each candidate alone before giving up.
                let mut single = None;
                let mut exhausted = false;
                let mut singles: Vec<usize> = Vec::with_capacity(candidates.len());
                for &c in order.iter().chain(candidates.iter()) {
                    if candidates.binary_search(&c).is_ok() && !singles.contains(&c) {
                        singles.push(c);
                    }
                }
                for &c in &singles {
                    match oracle.ask(&[c])? {
                        None => {
                            exhausted = true;
                            break;
                        }
                        Some(answer) if hits(&answer) => {
                            single = Some(vec![c]);
                            break;
                        }
                        Some(_) => {}
                    }
                }
                match single {
                    Some(set) => {
                        outcome.non_monotone = true;
                        set
                    }
                    None => {
                        outcome.status =
                            if exhausted { Status::BudgetExhausted } else { Status::Unreachable };
                        return finish(outcome, oracle);
                    }
                }
            };
            let (set, minimal) =
                ddmin(start, &mut |removed| Ok(oracle.ask(removed)?.map(|answer| hits(&answer))))?;
            outcome.after = oracle.memo.get(&set).cloned();
            outcome.status = Status::Found;
            outcome.set = set;
            outcome.minimal = minimal;
        }
        Mode::Core => {
            if before != Answer::Valid {
                outcome.status = Status::NotValid;
                return finish(outcome, oracle);
            }
            if candidates.is_empty() {
                outcome.status = Status::NoCandidates;
                return finish(outcome, oracle);
            }
            let mut keeps = |kept: &[usize]| -> Result<Option<bool>, E> {
                Ok(oracle.ask(&minus(&candidates, kept))?.map(|answer| answer == Answer::Valid))
            };
            let mut hint: Vec<usize> = core_start
                .iter()
                .copied()
                .filter(|c| candidates.binary_search(c).is_ok())
                .collect();
            hint.sort();
            hint.dedup();
            let (set, minimal) = match keeps(&[])? {
                None => (candidates.clone(), false),
                Some(true) => (Vec::new(), true),
                Some(false) if !hint.is_empty() && hint.len() < candidates.len() => {
                    match keeps(&hint)? {
                        None => (candidates.clone(), false),
                        Some(true) => {
                            outcome.hint_accepted = true;
                            ddmin(hint, &mut keeps)?
                        }
                        Some(false) => ddmin(candidates.clone(), &mut keeps)?,
                    }
                }
                Some(false) => ddmin(candidates.clone(), &mut keeps)?,
            };
            outcome.after = oracle.memo.get(&minus(&candidates, &set)).cloned();
            outcome.status = Status::Found;
            outcome.set = set;
            outcome.minimal = minimal;
        }
    }
    finish(outcome, oracle)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::Infallible;

    fn unknown() -> Answer {
        Answer::Unknown("resourceout".to_string())
    }

    fn run(mode: Mode, units: usize, budget: usize, probe: impl Fn(&[bool]) -> Answer) -> Outcome {
        let candidates: Vec<usize> = (0..units).collect();
        let mut probe = |disabled: &[bool]| -> Result<Answer, Infallible> { Ok(probe(disabled)) };
        search(mode, units, &candidates, budget, None, &mut probe).unwrap()
    }

    #[test]
    fn a_known_baseline_is_not_probed_again() {
        let calls = std::cell::Cell::new(0);
        let mut probe = |d: &[bool]| -> Result<Answer, Infallible> {
            calls.set(calls.get() + 1);
            Ok(if d[1] { Answer::Valid } else { unknown() })
        };
        let outcome =
            search(Mode::Flip(Target::Valid), 4, &[0, 1, 2, 3], 10, Some(unknown()), &mut probe)
                .unwrap();
        assert_eq!(outcome.set, vec![1]);
        assert_eq!(calls.get() + 1, outcome.probes.len());
    }

    #[test]
    fn one_culprit_is_found_in_logarithmically_many_probes() {
        let outcome =
            run(
                Mode::Flip(Target::Valid),
                40,
                64,
                |d| {
                    if d[7] { Answer::Valid } else { unknown() }
                },
            );
        assert_eq!(outcome.status, Status::Found);
        assert_eq!(outcome.set, vec![7]);
        assert!(outcome.minimal);
        assert_eq!(outcome.after, Some(Answer::Valid));
        // before, all removed, then about two probes per halving of 40
        assert!(outcome.probes.len() <= 2 + 2 * 6, "{}", outcome.probes.len());
    }

    #[test]
    fn culprits_that_must_all_go_are_all_reported() {
        let outcome = run(Mode::Flip(Target::Valid), 30, 100, |d| {
            if d[3] && d[21] && d[22] { Answer::Valid } else { unknown() }
        });
        assert_eq!(outcome.set, vec![3, 21, 22]);
        assert!(outcome.minimal);
    }

    #[test]
    fn either_of_two_culprits_is_enough() {
        let outcome = run(Mode::Flip(Target::Valid), 16, 100, |d| {
            if d[4] || d[12] { Answer::Valid } else { unknown() }
        });
        assert!(outcome.set == vec![4] || outcome.set == vec![12], "{:?}", outcome.set);
        assert!(outcome.minimal);
    }

    #[test]
    fn a_short_budget_returns_a_verified_superset() {
        let outcome =
            run(
                Mode::Flip(Target::Valid),
                64,
                4,
                |d| {
                    if d[40] { Answer::Valid } else { unknown() }
                },
            );
        assert_eq!(outcome.status, Status::Found);
        assert!(!outcome.minimal);
        assert!(outcome.set.contains(&40) && outcome.set.len() > 1);
        assert_eq!(outcome.after, Some(Answer::Valid));
        assert_eq!(outcome.all_removed, Some(Answer::Valid));
        assert_eq!(outcome.probes.len(), 4);
    }

    #[test]
    fn removal_that_breaks_a_proof() {
        // valid needs hypothesis 2, and one of 5 or 6
        let outcome = run(Mode::Flip(Target::NotValid), 10, 100, |d| {
            if !d[2] && (!d[5] || !d[6]) { Answer::Valid } else { Answer::Invalid }
        });
        assert_eq!(outcome.set, vec![2]);
        assert_eq!(outcome.after, Some(Answer::Invalid));
    }

    #[test]
    fn core_keeps_what_the_proof_needs() {
        let outcome =
            run(
                Mode::Core,
                12,
                100,
                |d| {
                    if !d[2] && !d[9] { Answer::Valid } else { Answer::Invalid }
                },
            );
        assert_eq!(outcome.status, Status::Found);
        assert_eq!(outcome.set, vec![2, 9]);
        assert!(outcome.minimal);
        assert_eq!(outcome.all_removed, Some(Answer::Invalid));
        assert_eq!(outcome.after, Some(Answer::Valid));
    }

    #[test]
    fn core_of_a_proof_that_needs_nothing_is_empty() {
        let outcome = run(Mode::Core, 5, 100, |_| Answer::Valid);
        assert_eq!(outcome.set, Vec::<usize>::new());
        assert!(outcome.minimal);
    }

    #[test]
    fn core_needs_a_valid_query() {
        let outcome = run(Mode::Core, 5, 100, |_| Answer::Invalid);
        assert_eq!(outcome.status, Status::NotValid);
        assert_eq!(outcome.probes.len(), 1);
    }

    #[test]
    fn nothing_to_do_when_already_at_target() {
        let outcome = run(Mode::Flip(Target::Valid), 5, 100, |_| Answer::Valid);
        assert_eq!(outcome.status, Status::AlreadyAtTarget);
    }

    #[test]
    fn non_monotone_removal_falls_back_to_single_units() {
        // removing 7 fixes it, but removing 8 as well breaks it again
        let outcome = run(Mode::Flip(Target::Valid), 10, 100, |d| {
            if d[7] && !d[8] { Answer::Valid } else { unknown() }
        });
        assert_eq!(outcome.status, Status::Found);
        assert!(outcome.non_monotone);
        assert_eq!(outcome.set, vec![7]);
    }

    #[test]
    fn single_units_are_tried_in_the_given_order_first() {
        // removing 37 fixes it, removing everything breaks it again
        let hits = |d: &[bool]| {
            if d[37] && !d[0] { Answer::Valid } else { unknown() }
        };
        // unit 40 is not a candidate, so an order naming it skips it
        let candidates: Vec<usize> = (0..40).collect();
        let flip = |order: &[usize]| {
            let mut probe = |d: &[bool]| -> Result<Answer, Infallible> { Ok(hits(d)) };
            search_ordered(
                Mode::Flip(Target::Valid),
                41,
                &candidates,
                order,
                &[],
                100,
                None,
                &mut probe,
            )
            .unwrap()
        };
        let outcome = flip(&[40, 37, 5]);
        assert_eq!(outcome.set, vec![37]);
        assert!(outcome.non_monotone);
        // before, all removed, then 37 straight away
        assert_eq!(outcome.probes.len(), 3);
        assert_eq!(outcome.probes[2].disabled, vec![37]);
        // without an order, every candidate before 37 is tried first
        let outcome = flip(&[]);
        assert_eq!(outcome.set, vec![37]);
        assert_eq!(outcome.probes.len(), 2 + 38);
    }

    #[test]
    fn a_core_starts_from_the_hint_when_it_keeps_the_proof() {
        // valid needs 3, 17 and 41 out of 60, scattered
        let needs = |d: &[bool]| {
            if !d[3] && !d[17] && !d[41] { Answer::Valid } else { Answer::Invalid }
        };
        let candidates: Vec<usize> = (0..60).collect();
        let core = |hint: &[usize], budget: usize| {
            let mut probe = |d: &[bool]| -> Result<Answer, Infallible> { Ok(needs(d)) };
            search_ordered(Mode::Core, 60, &candidates, &[], hint, budget, None, &mut probe)
                .unwrap()
        };
        let hinted = core(&[3, 17, 29, 41, 50], 100);
        assert!(hinted.hint_accepted);
        assert_eq!(hinted.set, vec![3, 17, 41]);
        assert!(hinted.minimal);
        let plain = core(&[], 100);
        assert!(!plain.hint_accepted);
        assert_eq!(plain.set, vec![3, 17, 41]);
        assert!(hinted.probes.len() < plain.probes.len());
        // a hint that loses the proof is dropped, and the search still finds the core
        let wrong = core(&[3, 17], 100);
        assert!(!wrong.hint_accepted);
        assert_eq!(wrong.set, vec![3, 17, 41]);
        // a hint of every candidate is no hint: the search is the plain one
        let every = core(&candidates, 100);
        assert!(!every.hint_accepted);
        assert_eq!(every.probes.len(), plain.probes.len());
        // the budget can run out on the hint's probe itself: every candidate
        // is then the core, as without a hint, and not minimal
        let starved = core(&[3, 17, 29, 41, 50], 2);
        assert_eq!(starved.status, Status::Found);
        assert!(!starved.hint_accepted);
        assert!(!starved.minimal);
        assert_eq!(starved.set, candidates);
    }

    #[test]
    fn unreachable_when_nothing_helps() {
        let outcome = run(Mode::Flip(Target::Valid), 4, 100, |_| unknown());
        assert_eq!(outcome.status, Status::Unreachable);
        assert_eq!(outcome.after, None);
        assert_eq!(outcome.all_removed, Some(unknown()));
        // before, all removed, then each unit alone
        assert_eq!(outcome.probes.len(), 2 + 4);
    }

    #[test]
    fn changed_compares_unknown_reasons() {
        let outcome = run(Mode::Flip(Target::Changed), 8, 100, |d| {
            if d[1] { Answer::Unknown("incomplete".to_string()) } else { unknown() }
        });
        assert_eq!(outcome.set, vec![1]);
        assert_eq!(outcome.after.as_ref().map(|a| a.class()), Some("incomplete"));
    }

    #[test]
    fn repeated_probes_are_not_rerun() {
        let calls = std::cell::Cell::new(0);
        let outcome = run(Mode::Flip(Target::Valid), 3, 100, |d| {
            calls.set(calls.get() + 1);
            if d[0] && d[2] { Answer::Valid } else { unknown() }
        });
        assert_eq!(outcome.set, vec![0, 2]);
        assert_eq!(calls.get(), outcome.probes.len());
    }
}
