use crate::ast::{
    Axiom, BinaryOp, BindX, Decl, DeclX, Expr, ExprX, Ident, MultiOp, Quant, Query, StmtX, TypX,
    UnaryOp,
};
use crate::ast_util::{ident_var, mk_and, mk_not};
use crate::context::{AssertionInfo, AxiomInfo, Context, ContextState, SmtSolver, ValidityResult};
use crate::def::{GLOBAL_PREFIX_LABEL, PREFIX_LABEL};
use crate::messages::{ArcDynMessage, Diagnostics};
pub use crate::model::{Model, ModelDef};
use std::collections::HashMap;
use std::sync::Arc;

pub(crate) fn label_asserts<'ctx>(
    context: &mut Context,
    infos: &mut Vec<AssertionInfo>,
    axiom_infos: &mut Vec<AxiomInfo>,
    expr: &Expr,
) -> Expr {
    match &**expr {
        ExprX::Binary(op @ BinaryOp::Implies, lhs, rhs)
        | ExprX::Binary(op @ BinaryOp::Eq, lhs, rhs) => {
            // asserts are on rhs of =>
            // (slight hack to also allow rhs of == for quantified function definitions)
            Arc::new(ExprX::Binary(
                op.clone(),
                lhs.clone(),
                label_asserts(context, infos, axiom_infos, rhs),
            ))
        }
        ExprX::Multi(op @ MultiOp::And, exprs) | ExprX::Multi(op @ MultiOp::Or, exprs) => {
            let mut exprs_vec: Vec<Expr> = Vec::new();
            for expr in exprs.iter() {
                exprs_vec.push(label_asserts(context, infos, axiom_infos, expr));
            }
            Arc::new(ExprX::Multi(*op, Arc::new(exprs_vec)))
        }
        ExprX::Bind(bind, body) => match &**bind {
            BindX::Quant(Quant::Forall, _, _, _) => Arc::new(ExprX::Bind(
                bind.clone(),
                label_asserts(context, infos, axiom_infos, body),
            )),
            _ => expr.clone(),
        },
        ExprX::LabeledAssertion(assert_id, error, filter, expr) => {
            // %%location_label%%N, and under cvc5 %%location_label%%N_aid_<id>:
            // the goal's provenance rides on the atom that is already on the
            // wire. Everything downstream matches the label by this string.
            let mut label_name = PREFIX_LABEL.to_string() + &infos.len().to_string();
            if context.emit_assert_ids {
                if let Some(id) = assert_id {
                    label_name = label_name + "_" + &crate::def::assert_id_to_symbol(id);
                }
            }
            let label = Arc::new(label_name);
            let decl = Arc::new(DeclX::Const(label.clone(), Arc::new(TypX::Bool)));
            let assertion_info = AssertionInfo {
                assert_id: assert_id.clone(),
                error: error.clone(),
                label: label.clone(),
                filter: filter.clone(),
                decl,
                disabled: false,
            };
            infos.push(assertion_info);
            let lhs = Arc::new(ExprX::Var(label));
            Arc::new(ExprX::Binary(
                BinaryOp::Implies,
                lhs,
                label_asserts(context, infos, axiom_infos, expr),
            ))
        }
        ExprX::LabeledAxiom(labels, filter, expr) => {
            let count = context.axiom_infos_count;
            context.axiom_infos_count += 1;
            let label = Arc::new(GLOBAL_PREFIX_LABEL.to_string() + &count.to_string());
            let decl = Arc::new(DeclX::Const(label.clone(), Arc::new(TypX::Bool)));
            let axiom_info = AxiomInfo {
                labels: labels.clone(),
                label: label.clone(),
                filter: filter.clone(),
                decl,
            };
            axiom_infos.push(axiom_info);
            let lhs = Arc::new(ExprX::Var(label));
            Arc::new(ExprX::Binary(
                BinaryOp::Implies,
                lhs,
                label_asserts(context, infos, axiom_infos, expr),
            ))
        }
        _ => expr.clone(),
    }
}

/// In SMT-LIB, functions applied to zero arguments are considered constants.
/// REVIEW: maybe AIR should follow this design for consistency.
pub(crate) fn elim_zero_args_expr(expr: &Expr) -> Expr {
    crate::visitor::map_expr_visitor(expr, &mut |expr| match &**expr {
        ExprX::Apply(x, es) if es.len() == 0 => Arc::new(ExprX::Var(x.clone())),
        _ => expr.clone(),
    })
}

pub(crate) fn smt_add_decl<'ctx>(context: &mut Context, decl: &Decl) {
    match &**decl {
        DeclX::Sort(_) | DeclX::Datatypes(_) | DeclX::Const(_, _) | DeclX::Fun(_, _, _) => {
            context.smt_log.log_decl(decl);
        }
        DeclX::Var(_, _) => {}
        DeclX::Axiom(Axiom { named, tag, expr }) => {
            let expr = elim_zero_args_expr(expr);
            let mut infos: Vec<AssertionInfo> = Vec::new();
            let mut axiom_infos: Vec<AxiomInfo> = Vec::new();
            let labeled_expr = label_asserts(context, &mut infos, &mut axiom_infos, &expr);
            for info in axiom_infos {
                crate::typecheck::add_decl(context, &info.decl, true).unwrap();
                context
                    .axiom_infos
                    .insert(info.label.clone(), Arc::new(info.clone()))
                    .expect("internal error: duplicate assert_info");
                smt_add_decl(context, &info.decl);
            }
            let tag = if context.emit_assert_ids {
                match tag {
                    Some(tag) => Some(tag.clone()),
                    None => Some(fallback_axiom_tag(context, &expr)),
                }
            } else {
                None
            };
            context.smt_log.log_assert(named, &tag, &labeled_expr);
        }
    }
}

/// The `:qid` of the quantifier an axiom is, or guards: `(forall ...)`, or
/// `(=> g (forall ...))` as fuel-guarded axioms are.
pub(crate) fn axiom_qid(expr: &Expr) -> Option<Ident> {
    match &**expr {
        ExprX::Bind(bind, _) => match &**bind {
            BindX::Quant(_, _, _, Some(qid)) => Some(qid.clone()),
            _ => None,
        },
        ExprX::Binary(BinaryOp::Implies, _, rhs) => axiom_qid(rhs),
        _ => None,
    }
}

/// A provenance tag for an axiom the producer did not tag: its quantifier's
/// `:qid` when it has one (Verus gives nearly every axiom one, and `qid_map`
/// joins it back to source), else a fresh `ax_anon_<n>`.
fn fallback_axiom_tag(context: &mut Context, expr: &Expr) -> crate::def::ProvenanceTag {
    let ident = match axiom_qid(expr) {
        Some(qid) => qid,
        None => {
            let n = context.anon_axiom_count;
            context.anon_axiom_count += 1;
            Arc::new(format!("anon_{}", n))
        }
    };
    crate::def::ProvenanceTag::Axiom(ident)
}

impl SmtSolver {
    /// The `(get-info :reason-unknown)` responses that mean "the solver hit its
    /// resource/time budget".  These vary across Z3 versions.
    pub fn reason_unknown_canceled_strs(&self) -> &'static [&'static str] {
        match self {
            SmtSolver::Z3 => &[
                "(:reason-unknown \"canceled\")",
                "(:reason-unknown \"max. resource limit exceeded\")",
            ],
            SmtSolver::Cvc5 => &["(:reason-unknown resourceout)", "(:reason-unknown timeout)"],
        }
    }

    pub fn reason_unknown_incomplete_str(&self) -> &str {
        match self {
            SmtSolver::Z3 => "(:reason-unknown \"(incomplete",
            SmtSolver::Cvc5 => "(:reason-unknown incomplete)",
        }
    }
}

/// The per-check cvc5 resource budget for this context's queries. Provenance
/// mode spends more of the budget on proof bookkeeping during search
/// (measured on toydb), so it gets twice as much. Instantiation replay runs
/// with full proofs (`--produce-proofs`), which slowed a first search about
/// 1.6x on toydb, so it gets the same, and difficulty mode pays for the same
/// preprocessing proofs plus solving under assumptions, so it does too.
pub(crate) fn cvc5_query_budget(context: &Context) -> u32 {
    if context.provenance || context.instantiation_replay || context.difficulty {
        context.rlimit.saturating_mul(2)
    } else {
        context.rlimit
    }
}

pub type ReportLongRunning<'a> =
    (std::time::Duration, Box<dyn FnMut(std::time::Duration, bool) -> () + 'a>);

const GET_VERSION_RESPONSE_PREFIX: &str = "(:version";

pub(crate) fn smt_check_assertion<'ctx>(
    context: &mut Context,
    diagnostics: &impl Diagnostics,
    mut infos: Vec<AssertionInfo>,
    air_model: Model,
    only_check_earlier: bool,
    report_long_running: Option<&mut ReportLongRunning>,
) -> ValidityResult {
    context.last_unknown_reason = None;
    // a check that returns before reading the reply must not leave the
    // previous check's pressure or difficulty behind for its caller to take
    context.last_inst_pressure = None;
    context.last_difficulty = None;
    context.last_branch_profile = None;
    let disabled_expr = if only_check_earlier {
        // disable all labels that come after the first known error
        let mut disabled: Vec<Expr> = Vec::new();
        let mut found_disabled = false;
        let mut found_enabled = false;
        for info in infos.iter_mut() {
            if found_disabled && !info.disabled {
                info.disabled = true;
                disabled.push(mk_not(&ident_var(&info.label)));
            }
            if info.disabled {
                found_disabled = true;
            } else {
                found_enabled = true;
            }
        }
        if only_check_earlier && !found_enabled {
            // no earlier assertions to check
            return ValidityResult::Valid(crate::context::UsageInfo::None);
        }
        Some(mk_and(&disabled))
    } else {
        None
    };

    context.smt_log.log_get_info("version");
    let smt_init_start_time = std::time::Instant::now();
    let smt_data = context.smt_log.take_pipe_data();
    let early_smt_output = context.get_smt_process().send_commands(smt_data);
    context.time_smt_init += smt_init_start_time.elapsed();
    for line in early_smt_output {
        if line.starts_with(GET_VERSION_RESPONSE_PREFIX) {
            if let Some(expected_version) = &context.expected_solver_version {
                let value: &str = &line[GET_VERSION_RESPONSE_PREFIX.len()..line.len() - 1];
                let version = value.trim_matches(&[' ', '"'][..]);
                if version != expected_version.as_str() {
                    let solver = context.solver.name();
                    diagnostics.report(&context.message_interface.unexpected_solver_version(
                        solver,
                        &expected_version,
                        version,
                    ));
                    panic!(
                        "The verifier expects {} version \"{}\", found version \"{}\"",
                        solver, expected_version, version
                    );
                }
            }
        } else if context.ignore_unexpected_smt {
            diagnostics.report(&context.message_interface.bare(
                crate::messages::MessageLevel::Warning,
                format!("warning: unexpected SMT output: {}", line).as_str(),
            ));
        } else {
            return ValidityResult::UnexpectedOutput(line);
        }
    }

    if let Some(disabled_expr) = disabled_expr {
        context.smt_log.log_assert(&None, &None, &disabled_expr);
    }

    match context.solver {
        SmtSolver::Z3 => {
            context.smt_log.log_set_option("rlimit", &context.rlimit.to_string());
            context.set_z3_param_u32("rlimit", context.rlimit, false);
        }
        SmtSolver::Cvc5 => {
            // `reproducible-resource-limit` (alias of `rlimit-per`) is one of the few
            // cvc5 options that may be set after initialisation; 0 means no limit.
            let budget = cvc5_query_budget(context);
            context.smt_log.log_set_option("reproducible-resource-limit", &budget.to_string());
        }
    }

    // Only the query's first check imports: later rounds share its scope.
    if let Some(certificate) = context.import_instantiations.take() {
        context.smt_log.log_import_instantiations(&certificate);
    }
    // Likewise an injected equality, which goes with the scope's pop.
    if let Some((lhs, rhs)) = context.inject_equality.take() {
        context.smt_log.log_node(&sise::TreeNode::List(vec![
            sise::TreeNode::Atom("assert".to_string()),
            sise::TreeNode::List(vec![sise::TreeNode::Atom("=".to_string()), lhs, rhs]),
        ]));
    }
    context.smt_log.log_word("check-sat");
    if context.difficulty {
        // in the same batch, right after the answer it describes and before
        // anything else can disturb the difficulty map or the unsat core
        context.smt_log.log_get_info("difficulty-gradient");
    }
    if context.nl_frontier {
        // in the same batch, right after the answer it describes
        context.smt_log.log_get_info("nl-frontier");
    }
    if context.inst_pressure {
        // in the same batch, right after the answer it describes
        context.smt_log.log_get_info("inst-pressure");
    }
    if context.branch_profile {
        // in the same batch, right after the answer it describes
        context.smt_log.log_get_info("branch-profile");
    }
    if context.provenance {
        // in the same batch: the tag lists arrive after the result and the
        // instantiation dump, before the sentinel
        context.smt_log.log_get_assertion_sources();
    }
    // The e-graph is read in the same batch too, after the tag lists and
    // before `get-info` or `get-model` can run. Only a query's first check
    // has focus terms, so later error rounds do not ask again.
    let egraph_asked = match (context.egraph_focus.take(), context.egraph_request) {
        (Some(focus), Some(request)) => {
            context.smt_log.log_get_egraph_equalities(&focus, request.limit, request.include_used);
            true
        }
        _ => false,
    };

    // Run SMT solver
    let smt_run_start_time = std::time::Instant::now();
    let smt_data = context.smt_log.take_pipe_data();
    let commands_handle = context.get_smt_process().send_commands_async(smt_data);
    let smt_output = if let Some((report_threshold, report_fn)) = report_long_running {
        match commands_handle.wait_timeout(*report_threshold) {
            Ok(smt_output) => smt_output,
            Err(handle) => {
                report_fn(smt_run_start_time.elapsed(), false);
                let smt_output = handle.wait();
                report_fn(smt_run_start_time.elapsed(), true);
                smt_output
            }
        }
    } else {
        commands_handle.wait()
    };
    context.time_smt_run += smt_run_start_time.elapsed();

    #[derive(PartialEq, Eq)]
    enum SmtOutput {
        Unsat,
        Sat,
        Unknown,
    }

    // Process SMT results
    let mut unsat = None;
    let mut provenance_lines: Vec<String> = Vec::new();
    let mut difficulty = None;
    let mut nl_frontier = None;
    let mut egraph_lines: Vec<String> = Vec::new();
    let mut inst_pressure = None;
    let mut branch_profile = None;
    for line in smt_output {
        // The e-graph reply, or the solver's refusal of the request, is the
        // batch's last: every line from its first on belongs to it.
        if !egraph_lines.is_empty()
            || (egraph_asked
                && unsat.is_some()
                && (line.starts_with("(egraph-equalities") || line.starts_with("(error")))
        {
            egraph_lines.push(line);
            continue;
        }
        // The keys come in the order they were asked, difficulty first, then
        // nl-frontier, inst-pressure and branch-profile, so a cvc5 without them answers
        // `unsupported` to each in turn and these branches take them in order.
        if context.difficulty && line.starts_with("(:difficulty-gradient ") {
            difficulty = Some(parse_difficulty_gradient(&line));
        } else if context.difficulty && difficulty.is_none() && line == "unsupported" {
            // a cvc5 without the key; say so rather than fail the query
            difficulty = Some(crate::context::DifficultyGradient {
                unparsed: Some(line),
                ..Default::default()
            });
        } else if context.nl_frontier && line.starts_with("(:nl-frontier ") {
            nl_frontier = Some(parse_nl_frontier(&line));
        } else if context.nl_frontier && nl_frontier.is_none() && line == "unsupported" {
            // a cvc5 without the key; say so rather than fail the query
            nl_frontier =
                Some(crate::context::NlFrontier { unparsed: Some(line), ..Default::default() });
        } else if context.inst_pressure && line.starts_with("(:inst-pressure ") {
            inst_pressure = Some(parse_inst_pressure(&line));
        } else if context.inst_pressure && inst_pressure.is_none() && line == "unsupported" {
            // a cvc5 without the key; say so rather than fail the query
            inst_pressure =
                Some(crate::context::InstPressure { unparsed: Some(line), ..Default::default() });
        } else if context.branch_profile && line.starts_with("(:branch-profile ") {
            branch_profile = Some(parse_branch_profile(&line));
        } else if context.branch_profile && branch_profile.is_none() && line == "unsupported" {
            // a cvc5 without the key; say so rather than fail the query
            branch_profile =
                Some(crate::context::BranchProfile { unparsed: Some(line), ..Default::default() });
        } else if line == "unsat" {
            assert!(unsat == None);
            unsat = Some(SmtOutput::Unsat);
        } else if line == "sat" {
            assert!(unsat == None);
            unsat = Some(SmtOutput::Sat);
        } else if line == "unknown" || line == "cvc5 interrupted by timeout." {
            assert!(unsat == None);
            unsat = Some(SmtOutput::Unknown);
        } else if context.provenance {
            // the instantiation dump and the sources reply; parsed below, never
            // an UnexpectedOutput
            provenance_lines.push(line);
        } else if context.ignore_unexpected_smt {
            diagnostics.report(&context.message_interface.bare(
                crate::messages::MessageLevel::Warning,
                format!("warning: unexpected SMT output: {}", line).as_str(),
            ));
        } else {
            return ValidityResult::UnexpectedOutput(line);
        }
    }

    match context.solver {
        SmtSolver::Z3 => {
            context.smt_log.log_set_option("rlimit", "0");
            context.set_z3_param_u32("rlimit", 0, false);
        }
        SmtSolver::Cvc5 => {
            context.smt_log.log_set_option("reproducible-resource-limit", "0");
        }
    }

    if context.provenance {
        context.last_provenance = Some(parse_provenance_lines(&provenance_lines));
    }
    context.last_nl_frontier = nl_frontier;
    context.last_difficulty = difficulty;
    context.last_inst_pressure = inst_pressure;
    context.last_branch_profile = branch_profile;
    if egraph_asked {
        context.last_egraph = Some(parse_egraph_lines(&egraph_lines));
    }

    let unsat = unsat.expect("expected sat/unsat/unknown from SMT solver");

    enum ResultDetermination<T> {
        Determined(ValidityResult),
        Undetermined(T),
    }

    let unsat_result = match unsat {
        SmtOutput::Unsat => ResultDetermination::Undetermined(true),
        SmtOutput::Sat => ResultDetermination::Undetermined(false),
        SmtOutput::Unknown => {
            context.smt_log.log_get_info("reason-unknown");
            if matches!(context.solver, SmtSolver::Cvc5) {
                // cvc5 records both when check-sat returns, so they describe
                // this answer. A cvc5 without the keys answers `unsupported`.
                context.smt_log.log_get_info("incomplete-id");
                context.smt_log.log_get_info("incomplete-culprits");
            }
            let smt_data = context.smt_log.take_pipe_data();
            let smt_output = context.get_smt_process().send_commands(smt_data);

            #[derive(PartialEq, Eq)]
            enum SmtReasonUnknown {
                Canceled,
                Incomplete,
                Unknown,
            }

            let mut reason = None;
            let mut unknown_reason = crate::context::UnknownReason::default();
            for line in smt_output {
                if let Some(id) =
                    line.strip_prefix("(:incomplete-id ").and_then(|s| s.strip_suffix(')'))
                {
                    if id != "NONE" {
                        unknown_reason.incomplete_id = Some(id.to_owned());
                    }
                    continue;
                }
                if line.starts_with("(:incomplete-culprits ") {
                    unknown_reason.culprit_qids = parse_incomplete_culprits(&line);
                    continue;
                }
                if line == "unsupported" && matches!(context.solver, SmtSolver::Cvc5) {
                    continue;
                }
                if let Some(r) =
                    line.strip_prefix("(:reason-unknown ").and_then(|s| s.strip_suffix(')'))
                {
                    unknown_reason.reason = r.trim_matches('"').to_owned();
                }
                if context.solver.reason_unknown_canceled_strs().iter().any(|s| line == *s) {
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Canceled);
                } else if line == "(:reason-unknown \"unknown\")" {
                    // it appears this sometimes happens when rlimit is exceeded
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Unknown);
                } else if line.starts_with(context.solver.reason_unknown_incomplete_str()) {
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Incomplete);
                } else if line
                    == "(:reason-unknown \"smt tactic failed to show goal to be sat/unsat (incomplete quantifiers)\")"
                {
                    // longer message shows up when there's no push/pop around the query
                    assert!(reason == None);
                    reason = Some(SmtReasonUnknown::Incomplete);
                } else if context.ignore_unexpected_smt {
                    diagnostics.report(&context.message_interface.bare(
                        crate::messages::MessageLevel::Warning,
                        format!("warning: unexpected SMT output: {}", line).as_str(),
                    ));
                } else {
                    return ValidityResult::UnexpectedOutput(line);
                }
            }

            context.last_unknown_reason = Some(unknown_reason);
            if context.matching_loops {
                // After the check, so it cannot perturb the check's budget.
                // Read before the next check-sat, whose presolve clears it.
                context.smt_log.log_get_info("matching-loops");
                let smt_data = context.smt_log.take_pipe_data();
                let lines = context.get_smt_process().send_commands(smt_data);
                context.last_matching_loops = Some(parse_matching_loops_lines(&lines));
            }

            match reason.expect("expected :reason-unknown") {
                SmtReasonUnknown::Canceled | SmtReasonUnknown::Unknown => {
                    context.state = ContextState::Canceled;
                    ResultDetermination::Determined(ValidityResult::Canceled)
                }
                SmtReasonUnknown::Incomplete => ResultDetermination::Undetermined(false),
            }
        }
    };

    match unsat_result {
        ResultDetermination::Determined(r) => r,
        ResultDetermination::Undetermined(true) => {
            context.state = ContextState::FoundResult;

            let usage_info = if context.usage_info_enabled {
                context.smt_log.log_word("get-unsat-core");

                let smt_data = context.smt_log.take_pipe_data();
                let smt_output = context.get_smt_process().send_commands(smt_data);

                let mut smt_output = smt_output.into_iter();
                let unsat_core_str =
                    smt_output.next().expect("expected one line in the unsat core output");
                assert!(smt_output.next().is_none());

                let fun_names: Vec<Ident> = unsat_core_str
                    .strip_prefix('(')
                    .expect("invalid unsat core")
                    .strip_suffix(')')
                    .expect("invalid unsat core")
                    .split_terminator(' ')
                    .map(|x| Arc::new(x.to_owned()))
                    .collect();
                crate::context::UsageInfo::UsedAxioms(fun_names)
            } else {
                crate::context::UsageInfo::None
            };

            ValidityResult::Valid(usage_info)
        }
        ResultDetermination::Undetermined(false) => {
            if context.single_check_query {
                // one obligation: nothing to localize, report it at the query level,
                // but keep the obligation's id when there is exactly one
                let assert_id = sole_enabled_assert_id(&infos);
                context.state = ContextState::FoundInvalid(infos, None);
                ValidityResult::Invalid(None, None, assert_id)
            } else {
                smt_get_model(context, infos, air_model)
            }
        }
    }
}

/// Parse cvc5's `(:nl-frontier (:result R :reason R :enabled B :checks N
/// :rounds N :punts N :last L :atoms (ATOM ...) :omitted N :truncated B))`.
/// Each ATOM is `(:atom T :kind K :current B :rounds N :value V :from-args V
/// [:lower BOUND] [:upper BOUND] :args ((:term T :value V [:lower BOUND]
/// [:upper BOUND]) ...) :hosts (HOST ...))`, each BOUND `(:value C :strict B
/// :fixed B)`, and each HOST `(:in input :term T :tags (T ...))` or `(:in
/// instance :term T :qid Q :count N)`. Values are as cvc5 prints them
/// (`-5`, `1/2`). Unknown keys are skipped; a reply that does not parse (a
/// malformed value, a key without one) is kept whole in `unparsed`.
pub(crate) fn parse_nl_frontier(line: &str) -> crate::context::NlFrontier {
    use sise::TreeNode;
    let mut out = crate::context::NlFrontier::default();
    let text = bar_symbols_as_strings(line);
    let mut parser = sise::Parser::new(&text);
    let fields = match sise::parse_tree(&mut parser) {
        Ok(TreeNode::List(items)) => match &items[..] {
            [TreeNode::Atom(key), TreeNode::List(fields)] if key == ":nl-frontier" => {
                fields.clone()
            }
            _ => Vec::new(),
        },
        _ => Vec::new(),
    };
    if fields.is_empty() {
        out.unparsed = Some(line.to_owned());
        return out;
    }
    let mut bad = false;
    for pair in fields.chunks(2) {
        match pair {
            [TreeNode::Atom(k), TreeNode::Atom(v)] => match k.as_str() {
                ":result" => out.result = v.clone(),
                ":reason" => out.reason = v.clone(),
                ":enabled" => out.enabled = v == "true",
                ":last" => out.last = v.clone(),
                ":truncated" => out.truncated = v == "true",
                ":checks" | ":rounds" | ":punts" | ":omitted" => {
                    let Some(n) = difficulty_count(v) else {
                        bad = true;
                        continue;
                    };
                    match k.as_str() {
                        ":checks" => out.checks = n,
                        ":rounds" => out.rounds = n,
                        ":punts" => out.punts = n,
                        _ => out.omitted = n,
                    }
                }
                _ => {}
            },
            [TreeNode::Atom(k), TreeNode::List(atoms)] if k == ":atoms" => {
                for atom in atoms {
                    match parse_nl_atom(atom) {
                        Some(a) => out.atoms.push(a),
                        None => bad = true,
                    }
                }
            }
            [_] => bad = true,
            _ => {}
        }
    }
    if bad {
        out.unparsed = Some(line.to_owned());
    }
    out
}

/// A reply subterm as text: lists re-joined, quoted symbols unquoted (see
/// `bar_symbols_as_strings`), unless whitespace or parentheses in one mean
/// only its bars keep it one symbol.
fn sexp_text(node: &sise::TreeNode) -> String {
    match node {
        sise::TreeNode::Atom(a) => match a.strip_prefix('"').and_then(|t| t.strip_suffix('"')) {
            Some(t) if t.contains(|c: char| c.is_whitespace() || c == '(' || c == ')') => {
                format!("|{t}|")
            }
            Some(t) => t.to_owned(),
            None => a.to_owned(),
        },
        sise::TreeNode::List(items) => {
            format!("({})", items.iter().map(sexp_text).collect::<Vec<_>>().join(" "))
        }
    }
}

/// `(:value C :strict B :fixed B)`
fn parse_nl_bound(node: &sise::TreeNode) -> Option<crate::context::NlBound> {
    let sise::TreeNode::List(items) = node else { return None };
    let mut b = crate::context::NlBound::default();
    for pair in items.chunks(2) {
        match pair {
            [sise::TreeNode::Atom(k), v] if k == ":value" => b.value = sexp_text(v),
            [sise::TreeNode::Atom(k), sise::TreeNode::Atom(v)] if k == ":strict" => {
                b.strict = v == "true"
            }
            [sise::TreeNode::Atom(k), sise::TreeNode::Atom(v)] if k == ":fixed" => {
                b.fixed = v == "true"
            }
            [_] => return None,
            _ => {}
        }
    }
    (!b.value.is_empty()).then_some(b)
}

/// `(:term T :value V [:lower BOUND] [:upper BOUND])`
fn parse_nl_term(node: &sise::TreeNode) -> Option<crate::context::NlTerm> {
    let sise::TreeNode::List(items) = node else { return None };
    let mut t = crate::context::NlTerm::default();
    for pair in items.chunks(2) {
        match pair {
            [sise::TreeNode::Atom(k), v] if k == ":term" => t.term = sexp_text(v),
            [sise::TreeNode::Atom(k), v] if k == ":value" => t.value = sexp_text(v),
            [sise::TreeNode::Atom(k), v] if k == ":lower" => t.lower = Some(parse_nl_bound(v)?),
            [sise::TreeNode::Atom(k), v] if k == ":upper" => t.upper = Some(parse_nl_bound(v)?),
            [_] => return None,
            _ => {}
        }
    }
    Some(t)
}

/// One ATOM of `(get-info :nl-frontier)`.
fn parse_nl_atom(node: &sise::TreeNode) -> Option<crate::context::NlAtom> {
    use sise::TreeNode;
    let TreeNode::List(items) = node else { return None };
    let mut a = crate::context::NlAtom::default();
    for pair in items.chunks(2) {
        match pair {
            [TreeNode::Atom(k), v] if k == ":atom" => a.atom = sexp_text(v),
            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":kind" => a.kind = v.clone(),
            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":current" => a.current = v == "true",
            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":rounds" => {
                a.rounds = difficulty_count(v)?
            }
            [TreeNode::Atom(k), v] if k == ":value" => a.value = sexp_text(v),
            [TreeNode::Atom(k), v] if k == ":from-args" => a.from_args = sexp_text(v),
            [TreeNode::Atom(k), v] if k == ":lower" => a.lower = Some(parse_nl_bound(v)?),
            [TreeNode::Atom(k), v] if k == ":upper" => a.upper = Some(parse_nl_bound(v)?),
            [TreeNode::Atom(k), TreeNode::List(args)] if k == ":args" => {
                for arg in args {
                    a.args.push(parse_nl_term(arg)?);
                }
            }
            [TreeNode::Atom(k), TreeNode::List(hosts)] if k == ":hosts" => {
                for host in hosts {
                    let TreeNode::List(fields) = host else { return None };
                    let mut h = crate::context::NlHost::default();
                    for pair in fields.chunks(2) {
                        match pair {
                            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":in" => {
                                h.input = v == "input"
                            }
                            [TreeNode::Atom(k), v] if k == ":term" => h.term = sexp_text(v),
                            [TreeNode::Atom(k), TreeNode::List(tags)] if k == ":tags" => {
                                h.tags = tags.iter().map(sexp_text).collect()
                            }
                            [TreeNode::Atom(k), v] if k == ":qid" => {
                                let qid = sexp_text(v);
                                h.qid = (qid != "none").then_some(qid);
                            }
                            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":count" => {
                                h.count = difficulty_count(v)?
                            }
                            [_] => return None,
                            _ => {}
                        }
                    }
                    a.hosts.push(h);
                }
            }
            [_] => return None,
            _ => {}
        }
    }
    (!a.atom.is_empty()).then_some(a)
}

/// A count from a solver reply. cvc5 prints arbitrary-precision integers, so
/// one too large for u64 saturates rather than fails.
fn difficulty_count(v: &str) -> Option<u64> {
    (!v.is_empty() && v.bytes().all(|b| b.is_ascii_digit()))
        .then(|| v.parse::<u64>().unwrap_or(u64::MAX))
}

/// cvc5 quotes a symbol that needs it as `|...|`, which sise cannot read, so
/// spell each one as a sise string. A symbol that cannot be a sise string
/// (it holds `"` or `\`) is left alone, and the reply stays unparsed.
fn bar_symbols_as_strings(line: &str) -> String {
    let mut out = String::with_capacity(line.len());
    let mut rest = line;
    while let Some(start) = rest.find('|') {
        out.push_str(&rest[..start]);
        let tail = &rest[start + 1..];
        match tail.find('|') {
            Some(end)
                if tail[..end].chars().all(|c| matches!(c, ' '..='~') && c != '"' && c != '\\') =>
            {
                out.push('"');
                out.push_str(&tail[..end]);
                out.push('"');
                rest = &tail[end + 1..];
            }
            _ => {
                out.push_str(&rest[start..]);
                rest = "";
            }
        }
    }
    out.push_str(rest);
    out
}

/// Parse cvc5's `(:difficulty-gradient (:result R :difficulty B :core B
/// :rows (ROW ...) :untagged (:asserted N :difficulty N [:in-core N])
/// :unmatched-difficulty N))`, where each ROW is `(:tags (T ...) :difficulty
/// N [:in-core B])`. Unknown keys are skipped; a reply that does not parse
/// is kept whole in `unparsed`.
pub(crate) fn parse_difficulty_gradient(line: &str) -> crate::context::DifficultyGradient {
    use sise::TreeNode;
    let mut out = crate::context::DifficultyGradient::default();
    let fields = match read_smt_sexp(line) {
        Some(TreeNode::List(items)) => match &items[..] {
            [TreeNode::Atom(key), TreeNode::List(fields)] if key == ":difficulty-gradient" => {
                fields.clone()
            }
            _ => Vec::new(),
        },
        _ => Vec::new(),
    };
    if fields.is_empty() {
        out.unparsed = Some(line.to_owned());
        return out;
    }
    let mut bad = false;
    for pair in fields.chunks(2) {
        match pair {
            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":result" => out.result = v.clone(),
            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":difficulty" => {
                out.difficulty = v == "true";
            }
            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":core" => out.core = v == "true",
            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":unmatched-difficulty" => {
                match difficulty_count(v) {
                    Some(n) => out.unmatched_difficulty = n,
                    None => bad = true,
                }
            }
            [TreeNode::Atom(k), TreeNode::List(rows)] if k == ":rows" => {
                for row in rows {
                    match parse_difficulty_row(row) {
                        Some(r) => out.rows.push(r),
                        None => bad = true,
                    }
                }
            }
            [TreeNode::Atom(k), TreeNode::List(untagged)] if k == ":untagged" => {
                for pair in untagged.chunks(2) {
                    let [TreeNode::Atom(k), TreeNode::Atom(v)] = pair else {
                        bad = true;
                        continue;
                    };
                    let Some(n) = difficulty_count(v) else {
                        bad = true;
                        continue;
                    };
                    match k.as_str() {
                        ":asserted" => out.untagged_asserted = n,
                        ":difficulty" => out.untagged_difficulty = n,
                        ":in-core" => out.untagged_in_core = Some(n),
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
    if bad {
        out.unparsed = Some(line.to_owned());
    }
    out
}

/// One `(:tags (T ...) :difficulty N [:in-core B])` row of
/// `(get-info :difficulty-gradient)`.
fn parse_difficulty_row(row: &sise::TreeNode) -> Option<crate::context::DifficultyRow> {
    use sise::TreeNode;
    let TreeNode::List(items) = row else { return None };
    let mut r = crate::context::DifficultyRow::default();
    for pair in items.chunks(2) {
        match pair {
            [TreeNode::Atom(k), TreeNode::List(tags)] if k == ":tags" => {
                for tag in tags {
                    let TreeNode::Atom(tag) = tag else { return None };
                    r.tags.push(tag.to_owned());
                }
            }
            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":difficulty" => {
                r.difficulty = difficulty_count(v)?;
            }
            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":in-core" => {
                r.in_core = Some(v == "true");
            }
            _ => {}
        }
    }
    Some(r)
}

/// Parse cvc5's `(:inst-pressure (:rounds R :refutation B :quantifiers (ROW
/// ...)))`, where each ROW is `(qid :key value ...)`. Unknown keys are
/// skipped; a reply that does not parse is kept whole in `unparsed`.
pub(crate) fn parse_inst_pressure(line: &str) -> crate::context::InstPressure {
    use sise::TreeNode;
    let mut out = crate::context::InstPressure::default();
    let fields = match read_smt_sexp(line) {
        Some(TreeNode::List(items)) => match &items[..] {
            [TreeNode::Atom(key), TreeNode::List(fields)] if key == ":inst-pressure" => {
                fields.clone()
            }
            _ => Vec::new(),
        },
        _ => Vec::new(),
    };
    if fields.is_empty() {
        out.unparsed = Some(line.to_owned());
        return out;
    }
    for pair in fields.chunks(2) {
        match pair {
            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":rounds" => {
                out.rounds = v.parse().unwrap_or(0);
            }
            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":refutation" => {
                out.refutation = v == "true";
            }
            [TreeNode::Atom(k), TreeNode::List(rows)] if k == ":quantifiers" => {
                for row in rows {
                    match parse_quant_pressure(row) {
                        Some(q) => out.quantifiers.push(q),
                        None => out.unparsed = Some(line.to_owned()),
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// Read one SMT-LIB s-expression as a sise tree. sise cannot read cvc5's
/// symbols: a quoted one is `|...|`, and a simple one may hold characters
/// sise's atoms lack (`^`). A quoted symbol becomes an atom without its
/// bars; a string literal keeps its quotes. `None` when the text is not
/// exactly one balanced expression.
fn read_smt_sexp(text: &str) -> Option<sise::TreeNode> {
    use sise::TreeNode;
    let mut stack: Vec<Vec<TreeNode>> = vec![Vec::new()];
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '(' => stack.push(Vec::new()),
            ')' => {
                let list = stack.pop()?;
                stack.last_mut()?.push(TreeNode::List(list));
            }
            '|' => {
                let mut symbol = String::new();
                loop {
                    match chars.next()? {
                        '|' => break,
                        c => symbol.push(c),
                    }
                }
                stack.last_mut()?.push(TreeNode::Atom(symbol));
            }
            '"' => {
                // `""` inside a string is an escaped quote
                let mut literal = String::from('"');
                loop {
                    let c = chars.next()?;
                    literal.push(c);
                    if c == '"' {
                        if chars.peek() == Some(&'"') {
                            literal.push(chars.next()?);
                        } else {
                            break;
                        }
                    }
                }
                stack.last_mut()?.push(TreeNode::Atom(literal));
            }
            c if c.is_whitespace() => {}
            c => {
                let mut atom = String::from(c);
                while let Some(&c) = chars.peek() {
                    if c.is_whitespace() || matches!(c, '(' | ')' | '|' | '"') {
                        break;
                    }
                    atom.push(c);
                    chars.next();
                }
                stack.last_mut()?.push(TreeNode::Atom(atom));
            }
        }
    }
    let mut top = stack.pop()?;
    if !stack.is_empty() || top.len() != 1 {
        return None;
    }
    top.pop()
}

/// One `(qid :key value ...)` row of `(get-info :inst-pressure)`.
fn parse_quant_pressure(row: &sise::TreeNode) -> Option<crate::context::QuantPressure> {
    use sise::TreeNode;
    let TreeNode::List(items) = row else { return None };
    let (TreeNode::Atom(qid), rest) = items.split_first()? else { return None };
    let mut q =
        crate::context::QuantPressure { qid: qid.to_owned(), named: true, ..Default::default() };
    for pair in rest.chunks(2) {
        let [TreeNode::Atom(k), TreeNode::Atom(v)] = pair else { return None };
        if k == ":named" {
            q.named = v != "false";
            continue;
        }
        let n: u64 = v.parse().ok()?;
        match k.as_str() {
            ":instantiations" => q.instantiations = n,
            ":duplicate-eq" => q.duplicate_eq = n,
            ":duplicate-ent" => q.duplicate_ent = n,
            ":duplicate-lemma" => q.duplicate_lemma = n,
            ":conflict" => q.conflict = n,
            ":propagate" => q.propagate = n,
            ":first-round" => q.first_round = Some(n),
            ":last-round" => q.last_round = Some(n),
            ":refutation" => q.refutation = Some(n),
            _ => {}
        }
    }
    Some(q)
}

/// Parse cvc5's `(:branch-profile (:resource-units N :resource-limit N
/// :rounds N :quantifiers (ROW ...)))`, where each ROW is `(qid [:named
/// false] :instantiations N :inferences ((ID N) ...))`. Unknown keys are
/// skipped; a reply that does not parse is kept whole in `unparsed`.
pub(crate) fn parse_branch_profile(line: &str) -> crate::context::BranchProfile {
    use sise::TreeNode;
    let mut out = crate::context::BranchProfile::default();
    let fields = match read_smt_sexp(line) {
        Some(TreeNode::List(items)) => match &items[..] {
            [TreeNode::Atom(key), TreeNode::List(fields)] if key == ":branch-profile" => {
                fields.clone()
            }
            _ => Vec::new(),
        },
        _ => Vec::new(),
    };
    if fields.is_empty() {
        out.unparsed = Some(line.to_owned());
        return out;
    }
    let mut bad = false;
    for pair in fields.chunks(2) {
        match pair {
            [TreeNode::Atom(k), TreeNode::Atom(v)] => {
                let Some(n) = difficulty_count(v) else {
                    bad = true;
                    continue;
                };
                match k.as_str() {
                    ":resource-units" => out.resource_units = n,
                    ":resource-limit" => out.resource_limit = n,
                    ":rounds" => out.rounds = n,
                    _ => {}
                }
            }
            [TreeNode::Atom(k), TreeNode::List(rows)] if k == ":quantifiers" => {
                for row in rows {
                    match parse_quant_inferences(row) {
                        Some(q) => out.quantifiers.push(q),
                        None => bad = true,
                    }
                }
            }
            [_] => bad = true,
            _ => {}
        }
    }
    if bad {
        out.unparsed = Some(line.to_owned());
    }
    out
}

/// One `(qid [:named false] :instantiations N :inferences ((ID N) ...))` row
/// of `(get-info :branch-profile)`.
fn parse_quant_inferences(row: &sise::TreeNode) -> Option<crate::context::QuantInferences> {
    use sise::TreeNode;
    let TreeNode::List(items) = row else { return None };
    let (TreeNode::Atom(qid), rest) = items.split_first()? else { return None };
    let mut q =
        crate::context::QuantInferences { qid: qid.to_owned(), named: true, ..Default::default() };
    for pair in rest.chunks(2) {
        match pair {
            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":named" => q.named = v != "false",
            [TreeNode::Atom(k), TreeNode::Atom(v)] if k == ":instantiations" => {
                q.instantiations = difficulty_count(v)?
            }
            [TreeNode::Atom(k), TreeNode::List(ids)] if k == ":inferences" => {
                for id in ids {
                    let TreeNode::List(pair) = id else { return None };
                    let [TreeNode::Atom(name), TreeNode::Atom(n)] = &pair[..] else { return None };
                    q.inferences.push((name.to_owned(), difficulty_count(n)?));
                }
            }
            [_] => return None,
            _ => {}
        }
    }
    Some(q)
}

/// Parse what provenance mode adds to a `check-sat` batch's output: the
/// `--dump-instantiations` forms (`(instantiations <qid> (<terms>)...)`,
/// `(skolem ...)`, or `none`) and the `(get-assertion-sources :tags-only)`
/// reply (`((<tags>) ...)`). Anything else is kept verbatim in `unparsed`.
pub(crate) fn parse_provenance_lines(lines: &Vec<String>) -> crate::context::ProvenanceInfo {
    use sise::TreeNode as Node;
    let mut info = crate::context::ProvenanceInfo::default();
    if lines.is_empty() {
        return info;
    }
    let text = format!("({})", lines.join("\n"));
    let mut parser = sise::Parser::new(text.as_str());
    let forms = match sise::parse_tree(&mut parser) {
        Ok(Node::List(forms)) => forms,
        _ => {
            info.unparsed = lines.clone();
            return info;
        }
    };
    for form in forms {
        match &form {
            Node::Atom(a) if a == "none" => {}
            Node::List(items) => match items.first() {
                Some(Node::Atom(head)) if head == "instantiations" => {
                    let qid = match items.get(1) {
                        Some(Node::Atom(q)) => q.clone(),
                        _ => {
                            info.unparsed.push(crate::printer::node_to_string(&form));
                            continue;
                        }
                    };
                    let vectors = items[2..]
                        .iter()
                        .map(|v| crate::printer::node_to_string(v))
                        .collect::<Vec<String>>();
                    info.instantiations.push((qid, vectors));
                }
                Some(Node::Atom(head)) if head == "skolem" => {}
                Some(Node::List(_)) | None if items.iter().all(|i| matches!(i, Node::List(_))) => {
                    // the tags-only reply: a list of tag lists
                    for tags in items.iter() {
                        if let Node::List(tags) = tags {
                            info.sources.push(
                                tags.iter().map(|t| crate::printer::node_to_string(t)).collect(),
                            );
                        }
                    }
                }
                _ => info.unparsed.push(crate::printer::node_to_string(&form)),
            },
            Node::Atom(_) => info.unparsed.push(crate::printer::node_to_string(&form)),
        }
    }
    info
}

/// The `:qid`s of a cvc5 `(:incomplete-culprits (q ...))` reply, each without
/// the `|...|` quoting cvc5 adds to symbols that need it. Anything else parses
/// to no culprits.
pub(crate) fn parse_incomplete_culprits(line: &str) -> Vec<String> {
    let Some(body) =
        line.strip_prefix("(:incomplete-culprits (").and_then(|s| s.strip_suffix("))"))
    else {
        return Vec::new();
    };
    let mut qids = Vec::new();
    let mut rest = body.trim_start();
    while !rest.is_empty() {
        let (qid, tail) = if let Some(quoted) = rest.strip_prefix('|') {
            match quoted.find('|') {
                Some(end) => (&quoted[..end], &quoted[end + 1..]),
                None => break,
            }
        } else {
            let end = rest.find(char::is_whitespace).unwrap_or(rest.len());
            (&rest[..end], &rest[end..])
        };
        qids.push(qid.to_owned());
        rest = tail.trim_start();
    }
    qids
}

/// Parse cvc5's `(get-info :matching-loops)` reply:
/// `(:matching-loops (:rounds n :instantiations n :dropped n
/// :max-inst-rounds b :loops ((loop :qid q :key value ...) ...)))`.
/// Keys it does not know, and replies of another shape, are kept verbatim
/// in `unparsed` rather than failed on.
pub(crate) fn parse_matching_loops_lines(lines: &Vec<String>) -> crate::context::MatchingLoopsInfo {
    use crate::context::{MatchingLoop, MatchingLoopsInfo};
    use sise::TreeNode as Node;
    let mut info = MatchingLoopsInfo::default();
    let text = unquote_symbols(&lines.join("\n"));
    let mut parser = sise::Parser::new(text.as_str());
    let body = match sise::parse_tree(&mut parser) {
        Ok(Node::List(reply)) => match reply.as_slice() {
            [Node::Atom(key), Node::List(body)] if key == ":matching-loops" => body.clone(),
            _ => {
                info.unparsed = lines.clone();
                return info;
            }
        },
        _ => {
            info.unparsed = lines.clone();
            return info;
        }
    };
    let text_of = |n: &Node| node_to_line(n);
    let symbol = |n: &Node| text_of(n);
    let num = |n: &Node| text_of(n).parse::<u64>().ok();
    let dec = |n: &Node| text_of(n).parse::<f64>().ok();
    let flag = |n: &Node| text_of(n) == "true";
    let terms = |n: &Node| match n {
        Node::List(items) => items.iter().map(|t| text_of(t)).collect(),
        _ => vec![],
    };
    // `:key value` pairs
    let pairs = |items: &[Node]| -> Vec<(String, Node)> {
        items
            .chunks(2)
            .filter_map(|kv| match kv {
                [Node::Atom(k), v] if k.starts_with(':') => Some((k.clone(), v.clone())),
                _ => None,
            })
            .collect()
    };
    let unknown = |k: &str, v: &Node, unparsed: &mut Vec<String>| {
        unparsed.push(format!("{k} {}", text_of(v)));
    };
    for (key, value) in pairs(&body) {
        match (key.as_str(), &value) {
            (":rounds", v) => info.rounds = num(v).unwrap_or(0),
            (":instantiations", v) => info.instantiations = num(v).unwrap_or(0),
            (":dropped", v) => info.dropped = num(v).unwrap_or(0),
            (":max-inst-rounds", v) => info.max_inst_rounds = flag(v),
            (":loops", Node::List(loops)) => {
                for form in loops {
                    let items = match form {
                        Node::List(items) if matches!(items.first(), Some(Node::Atom(h)) if h == "loop") => {
                            &items[1..]
                        }
                        _ => {
                            info.unparsed.push(text_of(form));
                            continue;
                        }
                    };
                    let mut l = MatchingLoop::default();
                    for (k, v) in pairs(items) {
                        match k.as_str() {
                            ":qid" => l.qid = symbol(&v),
                            ":confidence" => l.confidence = text_of(&v),
                            ":growth" => l.growth = text_of(&v),
                            ":edges" => l.edges_confirmed = text_of(&v) == "confirmed",
                            ":stable" => l.stable = flag(&v),
                            ":instantiations" => l.instantiations = num(&v).unwrap_or(0),
                            ":rounds" => l.rounds = num(&v).unwrap_or(0),
                            ":first-round" => l.first_round = num(&v).unwrap_or(0),
                            ":last-round" => l.last_round = num(&v).unwrap_or(0),
                            ":chain" => l.chain = num(&v).unwrap_or(0),
                            ":self-fed" => l.self_fed = num(&v).unwrap_or(0),
                            ":depth-per-rung" => l.depth_per_rung = dec(&v).unwrap_or(0.0),
                            ":depth-per-round" => l.depth_per_round = dec(&v).unwrap_or(0.0),
                            ":fanout-per-round" => l.fanout_per_round = dec(&v).unwrap_or(0.0),
                            ":fanout-per-step" => l.fanout_per_step = dec(&v).unwrap_or(0.0),
                            ":via" => {
                                l.via = match &v {
                                    Node::List(qs) => qs.iter().map(|q| symbol(q)).collect(),
                                    _ => vec![],
                                }
                            }
                            ":trigger" => l.trigger = terms(&v),
                            ":context" => l.context = terms(&v),
                            ":shape" => l.shape = terms(&v),
                            ":step" => l.step = terms(&v),
                            ":ladder" => {
                                l.ladder = match &v {
                                    Node::List(rungs) => rungs.iter().map(|r| terms(r)).collect(),
                                    _ => vec![],
                                }
                            }
                            ":ladder-length" => l.ladder_length = num(&v).unwrap_or(0),
                            ":per-round" => {
                                l.per_round = match &v {
                                    Node::List(ns) => ns.iter().filter_map(|n| num(n)).collect(),
                                    _ => vec![],
                                }
                            }
                            _ => unknown(&k, &v, &mut info.unparsed),
                        }
                    }
                    info.loops.push(l);
                }
            }
            (k, v) => unknown(k, v, &mut info.unparsed),
        }
    }
    info
}

/// One node on one line. The pretty printer breaks long terms across lines,
/// and the resolver compares terms by their text. A quoted symbol that
/// `unquote_symbols` had to carry as a sise string gets its bars back.
fn node_to_line(n: &sise::TreeNode) -> String {
    match n {
        sise::TreeNode::Atom(a) => {
            match a.strip_prefix("\"|").and_then(|a| a.strip_suffix("|\"")) {
                Some(quoted) => format!("|{}|", quoted.replace("\\\"", "\"")),
                None => a.clone(),
            }
        }
        sise::TreeNode::List(items) => {
            format!("({})", items.iter().map(node_to_line).collect::<Vec<_>>().join(" "))
        }
    }
}

/// cvc5 prints a symbol between bars when SMT-LIB needs it quoted, which
/// sise cannot read. A quoted symbol sise can read bare loses its bars; any
/// other becomes the sise string `"|...|"` (characters sise strings cannot
/// hold become `?`), so one odd symbol does not cost the whole reply. String
/// literals are copied as they are, so a bar inside one is left alone.
fn unquote_symbols(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find(&['|', '"'][..]) {
        out.push_str(&rest[..start]);
        let open = &rest[start..start + 1];
        let after = &rest[start + 1..];
        let Some(end) = after.find(open) else {
            out.push_str(&rest[start..]);
            return out;
        };
        let inner = &after[..end];
        if open == "\"" {
            out.push_str(&rest[start..start + end + 2]);
        } else if !inner.is_empty() && inner.chars().all(sise::is_atom_chr) {
            out.push_str(inner);
        } else {
            out.push_str("\"|");
            for c in inner.chars() {
                match c {
                    '"' => out.push_str("\\\""),
                    c if sise::is_atom_string_chr(c) => out.push(c),
                    _ => out.push('?'),
                }
            }
            out.push_str("|\"");
        }
        rest = &after[end + 1..];
    }
    out.push_str(rest);
    out
}

/// Parse cvc5's reply to `(get-egraph-equalities)`: `(egraph-equalities
/// (summary :classes n ...) (equality <lhs> <rhs> :level l :used b :focus n
/// :because (<lit> ...))*)`, or the `(error "...")` it gives instead.
pub(crate) fn parse_egraph_lines(lines: &[String]) -> crate::context::EgraphReply {
    use sise::TreeNode as Node;
    /// The `:key value` pairs the summary and each equality spell fields as.
    fn fields<'a>(items: &'a [Node]) -> impl Iterator<Item = (&'a str, &'a Node)> + 'a {
        items.chunks(2).filter_map(|pair| match pair {
            [Node::Atom(key), value] if key.starts_with(':') => Some((key.as_str(), value)),
            _ => None,
        })
    }
    fn number(node: &Node) -> u64 {
        match node {
            Node::Atom(a) => a.parse().unwrap_or(0),
            Node::List(_) => 0,
        }
    }
    /// A term on one line, as SMT-LIB spells it. The terms go back to the
    /// solver and are hashed into equality ids, so they carry no layout.
    fn one_line(node: &Node) -> String {
        match node {
            Node::Atom(a) => a.clone(),
            Node::List(items) => {
                format!("({})", items.iter().map(one_line).collect::<Vec<_>>().join(" "))
            }
        }
    }
    let mut reply = crate::context::EgraphReply::default();
    let text = format!("({})", lines.join("\n"));
    let mut parser = sise::Parser::new(text.as_str());
    let forms = match sise::parse_tree(&mut parser) {
        Ok(Node::List(forms)) => forms,
        _ => Vec::new(),
    };
    let mut recognised = false;
    for form in forms.iter() {
        let Node::List(items) = form else { continue };
        match items.first() {
            Some(Node::Atom(head)) if head == "egraph-equalities" => {
                recognised = true;
                for item in &items[1..] {
                    let Node::List(parts) = item else { continue };
                    match parts.first() {
                        Some(Node::Atom(head)) if head == "summary" => {
                            for (key, value) in fields(&parts[1..]) {
                                match key {
                                    ":classes" => reply.classes = number(value),
                                    ":candidates" => reply.candidates = number(value),
                                    ":focus" => reply.focus = number(value),
                                    ":focus-found" => reply.focus_found = number(value),
                                    ":used-omitted" => reply.used_omitted = number(value),
                                    ":too-large" => reply.too_large = number(value),
                                    _ => {}
                                }
                            }
                        }
                        Some(Node::Atom(head)) if head == "equality" && parts.len() >= 3 => {
                            let mut equality = crate::context::EgraphEquality {
                                lhs: one_line(&parts[1]),
                                rhs: one_line(&parts[2]),
                                level: "unknown".to_string(),
                                used: false,
                                used_by: Vec::new(),
                                focus: 0,
                                because: Vec::new(),
                                because_hidden: 0,
                            };
                            for (key, value) in fields(&parts[3..]) {
                                match (key, value) {
                                    (":level", Node::Atom(level)) => equality.level = level.clone(),
                                    (":used", Node::Atom(used)) => equality.used = used == "true",
                                    (":used-by", Node::List(qids)) => {
                                        equality.used_by = qids.iter().map(one_line).collect()
                                    }
                                    (":focus", value) => equality.focus = number(value) as u32,
                                    (":because", Node::List(lits)) => {
                                        equality.because = lits.iter().map(one_line).collect()
                                    }
                                    (":because-hidden", value) => {
                                        equality.because_hidden = number(value)
                                    }
                                    _ => {}
                                }
                            }
                            reply.equalities.push(equality);
                        }
                        _ => {}
                    }
                }
            }
            Some(Node::Atom(head)) if head == "error" && !recognised => {
                reply.error = Some(match items.get(1) {
                    Some(Node::Atom(message)) => message.trim_matches('"').to_string(),
                    _ => crate::printer::node_to_string(form),
                });
            }
            _ => {}
        }
    }
    if recognised {
        reply.error = None;
    } else if reply.error.is_none() {
        reply.error = Some(format!("unrecognised e-graph reply: {}", lines.join(" ")));
    }
    reply
}

/// At most this many focus terms go with one e-graph request, in at most
/// this many printed bytes; the smallest are kept.
const EGRAPH_FOCUS_TERMS: usize = 4000;
const EGRAPH_FOCUS_BYTES: usize = 1 << 20;
/// A term of more nodes than this is not a focus term. Printing each focus
/// term apart would otherwise cost the square of the query's depth.
const EGRAPH_FOCUS_TERM_NODES: usize = 64;

/// The query's own terms, which focus `(get-egraph-equalities)` on the
/// classes the query is about: variables and non-Boolean applications that
/// cvc5 can parse at the query's scope, so none that mentions a bound
/// variable, a closure, or an assertion label. Boolean connectives and
/// relations are left out; cvc5 does not list Boolean classes.
fn egraph_focus_terms(expr: &Expr, printer: &crate::printer::Printer) -> Vec<sise::TreeNode> {
    /// Collect `expr`'s focus terms into `out`. Returns its size in nodes if
    /// it names no bound variable and can be printed at the query's scope.
    fn walk(expr: &Expr, bound: &mut Vec<Ident>, out: &mut Vec<Expr>) -> Option<usize> {
        // Every child is walked, whether or not an earlier one was closed.
        fn all(sizes: Vec<Option<usize>>) -> Option<usize> {
            sizes.into_iter().sum::<Option<usize>>().map(|size| size + 1)
        }
        let (size, boolean) = match &**expr {
            ExprX::Const(_) => return Some(1),
            ExprX::Var(x) => {
                if bound.contains(x) {
                    return None;
                }
                let label = x.starts_with(PREFIX_LABEL) || x.starts_with(GLOBAL_PREFIX_LABEL);
                (Some(1), label)
            }
            ExprX::Old(..) => return None,
            ExprX::Apply(_, args) => {
                (all(args.iter().map(|arg| walk(arg, bound, out)).collect()), false)
            }
            ExprX::ApplyFun(_, fun, args) => {
                walk(fun, bound, out);
                for arg in args.iter() {
                    walk(arg, bound, out);
                }
                return None;
            }
            ExprX::Array(args) => {
                for arg in args.iter() {
                    walk(arg, bound, out);
                }
                return None;
            }
            ExprX::Unary(op, arg) => (
                all(vec![walk(arg, bound, out)]),
                matches!(
                    op,
                    UnaryOp::Not
                        | UnaryOp::FloatIsNormal
                        | UnaryOp::FloatIsSubnormal
                        | UnaryOp::FloatIsZero
                        | UnaryOp::FloatIsInfinite
                        | UnaryOp::FloatIsNaN
                        | UnaryOp::FloatIsNegative
                        | UnaryOp::FloatIsPositive
                ),
            ),
            ExprX::Binary(op, lhs, rhs) => (
                all(vec![walk(lhs, bound, out), walk(rhs, bound, out)]),
                matches!(
                    op,
                    BinaryOp::Implies
                        | BinaryOp::Eq
                        | BinaryOp::Le
                        | BinaryOp::Ge
                        | BinaryOp::Lt
                        | BinaryOp::Gt
                        | BinaryOp::Relation(..)
                        | BinaryOp::BitULt
                        | BinaryOp::BitUGt
                        | BinaryOp::BitULe
                        | BinaryOp::BitUGe
                        | BinaryOp::BitSLt
                        | BinaryOp::BitSGt
                        | BinaryOp::BitSLe
                        | BinaryOp::BitSGe
                        | BinaryOp::FloatEq
                        | BinaryOp::FloatLt
                        | BinaryOp::FloatGt
                        | BinaryOp::FloatLe
                        | BinaryOp::FloatGe
                ),
            ),
            ExprX::Multi(op, args) => (
                all(args.iter().map(|arg| walk(arg, bound, out)).collect()),
                matches!(op, MultiOp::And | MultiOp::Or | MultiOp::Xor | MultiOp::Distinct),
            ),
            ExprX::IfElse(cond, lhs, rhs) => (
                all(vec![walk(cond, bound, out), walk(lhs, bound, out), walk(rhs, bound, out)]),
                false,
            ),
            ExprX::Bind(bind, body) => {
                let depth = bound.len();
                match &**bind {
                    BindX::Let(binders) => {
                        // a let's definitions are outside its own bindings
                        for binder in binders.iter() {
                            walk(&binder.a, bound, out);
                        }
                        bound.extend(binders.iter().map(|binder| binder.name.clone()));
                        walk(body, bound, out);
                    }
                    BindX::Quant(_, binders, _, _) | BindX::Lambda(binders, _, _) => {
                        bound.extend(binders.iter().map(|binder| binder.name.clone()));
                        walk(body, bound, out);
                    }
                    BindX::Choose(binders, _, _, cond) => {
                        bound.extend(binders.iter().map(|binder| binder.name.clone()));
                        walk(cond, bound, out);
                        walk(body, bound, out);
                    }
                }
                bound.truncate(depth);
                return None;
            }
            ExprX::LabeledAxiom(_, _, inner) | ExprX::LabeledAssertion(_, _, _, inner) => {
                walk(inner, bound, out);
                return None;
            }
        };
        if let Some(nodes) = size {
            if !boolean && nodes <= EGRAPH_FOCUS_TERM_NODES {
                out.push(expr.clone());
            }
        }
        size
    }
    let mut terms: Vec<Expr> = Vec::new();
    walk(expr, &mut Vec::new(), &mut terms);
    let mut seen = std::collections::HashSet::new();
    let mut printed: Vec<(String, sise::TreeNode)> = Vec::new();
    for term in terms {
        let node = printer.expr_to_node(&term);
        let text = crate::printer::node_to_string(&node);
        if seen.insert(text.clone()) {
            printed.push((text, node));
        }
    }
    printed.sort_by(|a, b| a.0.len().cmp(&b.0.len()).then_with(|| a.0.cmp(&b.0)));
    let mut bytes = 0;
    printed
        .into_iter()
        .take(EGRAPH_FOCUS_TERMS)
        .take_while(|(text, _)| {
            bytes += text.len() + 1;
            bytes <= EGRAPH_FOCUS_BYTES
        })
        .map(|(_, node)| node)
        .collect()
}

pub(crate) fn smt_get_rlimit_count(context: &mut Context) -> Result<u64, ValidityResult> {
    assert!(matches!(context.solver, SmtSolver::Z3)); // the CVC5 output format for statistics is different

    context.smt_log.log_get_info("all-statistics");
    let smt_data = context.smt_log.take_pipe_data();
    let smt_output = context.get_smt_process().send_commands(smt_data);
    let statistics = crate::parser::parse_sexpression(&smt_output);
    let stats_map = statistics
        .as_list()
        .unwrap()
        .chunks(2)
        .map(|chunk| {
            let [key, value] = chunk else {
                return Err(ValidityResult::UnexpectedOutput(format!(
                    "expected key-value pair in statistics"
                )));
            };
            let Some((key, value)) = key
                .as_atom()
                .map(|key| &key.as_str()[1..])
                .and_then(|key| value.as_atom().map(|value| (key, value.as_str())))
            else {
                return Err(ValidityResult::UnexpectedOutput(format!(
                    "expected key-value pair in statistics"
                )));
            };
            Ok((key, value))
        })
        .collect::<Result<HashMap<&str, &str>, ValidityResult>>()?;
    // `rlimit-count` may be absent (e.g. a prelude-free bit_vector query with nothing yet to count);
    // treat it as zero. This is resource accounting only, never the verification result.
    let rlimit_count = match stats_map.get("rlimit-count") {
        None => 0,
        Some(value) => {
            let Some(count) = value.parse().ok() else {
                return Err(ValidityResult::UnexpectedOutput(format!(
                    "expected rlimit-count in smt statistics"
                )));
            };
            count
        }
    };
    Ok(rlimit_count)
}

/// The id of the one labelled assertion still enabled in `infos`, when there
/// is exactly one: the result paths that have no model to localise with can
/// still name it.
fn sole_enabled_assert_id(infos: &Vec<AssertionInfo>) -> Option<crate::ast::AssertId> {
    let mut enabled = infos.iter().filter(|info| !info.disabled);
    match (enabled.next(), enabled.next()) {
        (Some(info), None) => info.assert_id.clone(),
        _ => None,
    }
}

fn smt_get_model(
    context: &mut Context,
    mut infos: Vec<AssertionInfo>,
    air_model: Model,
) -> ValidityResult {
    let mut discovered_error: Option<AssertionInfo> = None;
    let mut discovered_assert_id: Option<Option<Arc<Vec<u64>>>> = None;
    let mut discovered_additional_info: Vec<ArcDynMessage> = Vec::new();

    context.smt_log.log_word("get-model");

    let smt_data = context.smt_log.take_pipe_data();
    let smt_output = context.get_smt_process().send_commands(smt_data);

    if smt_output.iter().any(|line| line.contains("model is not available")) {
        // when we don't use incremental solving, sometime the model is not available when the z3 result is unknown
        let assert_id = sole_enabled_assert_id(&infos);
        context.state = ContextState::FoundInvalid(infos, None);
        return ValidityResult::Invalid(None, None, assert_id);
    };

    let model =
        crate::parser::Parser::new(context.message_interface.clone()).lines_to_model(&smt_output);
    let mut model_defs: HashMap<Ident, ModelDef> = HashMap::new();
    for def in model.iter() {
        model_defs.insert(def.name.clone(), def.clone());
    }
    for info in infos.iter_mut() {
        if let Some(def) = model_defs.get(&info.label) {
            if *def.body == "true" {
                discovered_error = Some(info.clone());
                discovered_assert_id = Some(info.assert_id.clone());

                // Disable this label in subsequent check-sat calls to get additional errors
                info.disabled = true;
                let disable_label = mk_not(&ident_var(&info.label));
                context.smt_log.log_assert(&None, &None, &disable_label);

                break;
            }
        }
    }
    let discovered_error = discovered_error.expect("discovered_error");
    let mut axiom_infos: Vec<Arc<AxiomInfo>> =
        context.axiom_infos.map().values().cloned().collect();
    axiom_infos.sort_by_key(|info| info.label.clone());
    // stabilize order
    for info in axiom_infos {
        if let Some(def) = model_defs.get(&info.label) {
            if *def.body == "true"
                && (info.filter.is_none() || info.filter == discovered_error.filter)
            {
                discovered_additional_info.append(&mut info.labels.clone());
                break;
            }
        }
    }

    if context.debug {
        println!("Z3 model: {:?}", model);
    }

    // Attach the additional info to the error
    // For example, the error might be something like "precondition not satisfied"
    // (an error which comes from the air assert statement)
    // and the additional info might tell you _which_ precondition failed
    // (a label that comes from one of the axioms associated
    // to the function precondition)

    let error = discovered_error.error;
    let e = context.message_interface.append_labels(&error, &discovered_additional_info);
    context.state = ContextState::FoundInvalid(infos, Some(air_model.clone()));
    ValidityResult::Invalid(Some(air_model), Some(e), discovered_assert_id.unwrap())
}

pub(crate) fn smt_check_query<'ctx>(
    context: &mut Context,
    diagnostics: &impl Diagnostics,
    query: &Query,
    air_model: Model,
    report_long_running: Option<&mut ReportLongRunning>,
) -> ValidityResult {
    if !context.single_check_query {
        context.smt_log.log_push();
        context.push_name_scope();
        if let Some((key, only)) = &context.restore_instantiations {
            context.smt_log.log_restore_instantiations(key, *only);
        }
    }

    let rlimit_count_1 = if matches!(context.solver, SmtSolver::Z3) {
        let rlimit_count = match smt_get_rlimit_count(context) {
            Ok(rlimit_count) => rlimit_count,
            Err(e) => return e,
        };
        Some(rlimit_count)
    } else {
        None
    };

    // add query-local declarations
    for decl in query.local.iter() {
        if let Err(err) = crate::typecheck::add_decl(context, decl, false) {
            // A type error opens no query to finish, so close the scope opened above.
            if !context.single_check_query {
                context.pop_name_scope();
                context.smt_log.log_pop();
            }
            return ValidityResult::TypeError(err);
        }
        smt_add_decl(context, decl);
    }

    // after lowering, there should be just one assertion
    let assertion = match &*query.assertion {
        StmtX::Assert(_, _, _, expr) => expr,
        _ => panic!("internal error: query not lowered"),
    };
    let assertion = elim_zero_args_expr(assertion);

    // An e-graph request is focused on the classes of this query's own terms.
    if context.egraph_request.is_some() {
        let printer = crate::printer::Printer::new(
            context.message_interface.clone(),
            true,
            context.solver.clone(),
        );
        context.egraph_focus = Some(egraph_focus_terms(&assertion, &printer));
    }

    // add labels to assertions for error reporting
    let mut infos: Vec<AssertionInfo> = Vec::new();
    let mut axiom_infos: Vec<AxiomInfo> = Vec::new();
    let labeled_assertion = label_asserts(context, &mut infos, &mut axiom_infos, &assertion);
    for info in &infos {
        context.smt_log.comment(&context.message_interface.get_note(&info.error));
        if let Err(err) = crate::typecheck::add_decl(context, &info.decl, false) {
            return ValidityResult::TypeError(err);
        }
        smt_add_decl(context, &info.decl);
    }

    // check assertion; the negated query is the one assertion every goal lives in
    let not_expr = Arc::new(ExprX::Unary(UnaryOp::Not, labeled_assertion));
    let query_tag =
        if context.emit_assert_ids { Some(crate::def::ProvenanceTag::Query) } else { None };
    context.smt_log.log_assert(&None, &query_tag, &not_expr);

    let rlimit_count_2 = if matches!(context.solver, SmtSolver::Z3) {
        let rlimit_count = match smt_get_rlimit_count(context) {
            Ok(rlimit_count) => rlimit_count,
            Err(e) => return e,
        };
        Some(rlimit_count)
    } else {
        None
    };

    let result =
        smt_check_assertion(context, diagnostics, infos, air_model, false, report_long_running);

    if matches!(context.solver, SmtSolver::Z3) {
        let (ctx_rlimit_init, ctx_rlimit_run) = context.rlimit_count.unwrap();
        let rlimit_count_3 = match smt_get_rlimit_count(context) {
            Ok(rlimit_count) => rlimit_count,
            Err(e) => return e,
        };
        let rlimit_init = rlimit_count_2.unwrap() - rlimit_count_1.unwrap();
        let rlimit_run = rlimit_count_3 - rlimit_count_2.unwrap();
        context.rlimit_count = Some((ctx_rlimit_init + rlimit_init, ctx_rlimit_run + rlimit_run));
    }

    result
}

#[cfg(test)]
mod egraph_tests {
    use super::*;

    fn lines(text: &[&str]) -> Vec<String> {
        text.iter().map(|line| line.to_string()).collect()
    }

    #[test]
    fn egraph_reply_parses_summary_equalities_and_refusals() {
        let reply = parse_egraph_lines(&lines(&[
            "(egraph-equalities",
            "(summary :classes 2 :candidates 3 :focus 4 :focus-found 3 :used-omitted 1 :too-large 5)",
            "(equality (f b) c :level entailed :used false :used-by () :focus 2 :because ((= a b) (= (f a) c)))",
            "(equality d b :level decision :used true :used-by (prelude_box user_f_1) :focus 1 :because () :because-hidden 2)",
            ")",
        ]));
        assert!(reply.error.is_none(), "{:?}", reply.error);
        assert_eq!(
            (reply.classes, reply.candidates, reply.focus, reply.focus_found, reply.used_omitted),
            (2, 3, 4, 3, 1)
        );
        assert_eq!(reply.too_large, 5);
        assert_eq!(
            (reply.equalities[0].because_hidden, reply.equalities[1].because_hidden),
            (0, 2)
        );
        assert_eq!(reply.equalities.len(), 2);
        let first = &reply.equalities[0];
        assert_eq!(
            (first.lhs.as_str(), first.rhs.as_str(), first.level.as_str(), first.used, first.focus),
            ("(f b)", "c", "entailed", false, 2)
        );
        assert_eq!(first.because, vec!["(= a b)", "(= (f a) c)"]);
        assert!(reply.equalities[1].used && reply.equalities[1].because.is_empty());
        assert!(first.used_by.is_empty());
        assert_eq!(reply.equalities[1].used_by, vec!["prelude_box", "user_f_1"]);

        let refused = parse_egraph_lines(&lines(&[
            "(error \"cannot get e-graph equalities unless after a SAT or UNKNOWN response.\")",
        ]));
        assert!(refused.equalities.is_empty());
        assert!(refused.error.unwrap().contains("cannot get e-graph equalities"));
        assert!(parse_egraph_lines(&Vec::new()).error.is_some());
    }

    #[test]
    fn egraph_focus_skips_bound_variables_labels_and_connectives() {
        let var = |x: &str| Arc::new(ExprX::Var(Arc::new(x.to_string())));
        let apply = |f: &str, args: Vec<Expr>| {
            Arc::new(ExprX::Apply(Arc::new(f.to_string()), Arc::new(args)))
        };
        let eq = |a: Expr, b: Expr| Arc::new(ExprX::Binary(BinaryOp::Eq, a, b));
        let one = Arc::new(ExprX::Const(crate::ast::Constant::Nat(Arc::new("1".to_string()))));
        let binder = Arc::new(crate::ast::BinderX {
            name: Arc::new("i".to_string()),
            a: Arc::new(TypX::Int),
        });
        let forall = Arc::new(ExprX::Bind(
            Arc::new(BindX::Quant(Quant::Forall, Arc::new(vec![binder]), Arc::new(vec![]), None)),
            eq(apply("g", vec![var("i")]), var("z")),
        ));
        let label = format!("{}0", PREFIX_LABEL);
        let goal = Arc::new(ExprX::Binary(
            BinaryOp::Implies,
            var(&label),
            Arc::new(ExprX::Binary(
                BinaryOp::Lt,
                Arc::new(ExprX::Multi(MultiOp::Add, Arc::new(vec![var("x"), one]))),
                var("w"),
            )),
        ));
        let query = mk_and(&vec![eq(apply("f", vec![var("x")]), var("y")), forall, goal]);
        let printer = crate::printer::Printer::new(
            Arc::new(crate::messages::AirMessageInterface {}),
            true,
            SmtSolver::Cvc5,
        );
        let focus: Vec<String> = egraph_focus_terms(&query, &printer)
            .iter()
            .map(crate::printer::node_to_string)
            .collect();
        assert_eq!(focus, vec!["w", "x", "y", "z", "(f x)", "(+ x 1)"]);
    }
}
