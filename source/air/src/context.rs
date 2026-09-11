use crate::ast::{
    AssertId, AxiomInfoFilter, Command, CommandX, Decl, Ident, Query, Typ, TypeError, Typs,
};
use crate::closure::ClosureTerm;
use crate::emitter::Emitter;
use crate::messages::{ArcDynMessage, Diagnostics};
use crate::model::Model;
use crate::node;
use crate::printer::{macro_push_node, str_to_node};

use crate::scope_map::ScopeMap;
use crate::smt_process::SmtProcess;
use crate::smt_verify::ReportLongRunning;
use crate::typecheck::Typing;
use sise::TreeNode as Node;
use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::Duration;

#[derive(Clone, Debug)]
pub(crate) struct AssertionInfo {
    pub(crate) assert_id: Option<crate::ast::AssertId>,
    pub(crate) error: ArcDynMessage,
    pub(crate) label: Ident,
    pub(crate) filter: AxiomInfoFilter,
    pub(crate) decl: Decl,
    pub(crate) disabled: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct AxiomInfo {
    pub(crate) labels: Vec<Arc<dyn Any + Send + Sync>>,
    pub(crate) label: Ident,
    pub(crate) filter: AxiomInfoFilter,
    pub(crate) decl: Decl,
}

#[derive(Debug)]
pub enum UsageInfo {
    None,
    UsedAxioms(Vec<Ident>),
}

/// What cvc5 reported about one `check-sat` in provenance mode: the tag
/// lists of `(get-assertion-sources :tags-only)` and the instantiation dump.
/// Tags are the symbols from the wire (`hyp_3`, `ax_...`, `query`, `?`);
/// the join back to source happens in Verus.
#[derive(Debug, Clone, Default)]
pub struct ProvenanceInfo {
    /// SSA symbol -> original AIR variable and assignment version, recorded by lowering.
    pub variable_versions: VariableVersions,
    /// One entry per distinct tag list with at least one real tag.
    pub sources: Vec<Vec<String>>,
    /// Instantiated quantifiers, by `:qid`, with each instantiation vector
    /// printed as one string.
    pub instantiations: Vec<(String, Vec<String>)>,
    /// Reply lines the parser did not recognise, kept rather than failed on.
    pub unparsed: Vec<String>,
}

pub type VariableVersions = HashMap<String, (String, u32)>;

#[derive(Debug)]
pub enum ValidityResult {
    Valid(UsageInfo),
    Invalid(Option<Model>, Option<ArcDynMessage>, Option<AssertId>),
    Canceled,
    TypeError(TypeError),
    UnexpectedOutput(String),
}

#[derive(Clone, Debug)]
pub(crate) enum ContextState {
    NotStarted,
    ReadyForQuery,
    FoundResult,
    FoundInvalid(Vec<AssertionInfo>, Option<Model>),
    Canceled,
    NoMoreQueriesAllowed,
}

pub struct QueryContext<'a, 'b: 'a> {
    pub report_long_running: Option<&'a mut ReportLongRunning<'b>>,
}

impl<'a, 'b: 'a> Default for QueryContext<'a, 'b> {
    fn default() -> Self {
        QueryContext { report_long_running: None }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum SmtSolver {
    Z3,
    Cvc5,
}

impl SmtSolver {
    /// The solver's executable name, as used in messages.
    pub fn name(&self) -> &'static str {
        match self {
            SmtSolver::Z3 => "z3",
            SmtSolver::Cvc5 => "cvc5",
        }
    }
}

impl Default for SmtSolver {
    fn default() -> Self {
        SmtSolver::Z3
    }
}

pub struct Context {
    pub(crate) message_interface: Arc<dyn crate::messages::MessageInterface>,
    smt_process: Option<SmtProcess>,
    pub(crate) axiom_infos: ScopeMap<Ident, Arc<AxiomInfo>>,
    pub(crate) axiom_infos_count: u64,
    pub(crate) array_map: ScopeMap<ClosureTerm, Ident>,
    pub(crate) array_count: u64,
    pub(crate) lambda_map: ScopeMap<ClosureTerm, Ident>,
    pub(crate) lambda_count: u64,
    pub(crate) choose_map: ScopeMap<ClosureTerm, Ident>,
    pub(crate) choose_count: u64,
    pub(crate) apply_map: ScopeMap<(Typs, Typ), Ident>,
    pub(crate) apply_count: u64,
    pub(crate) typing: Typing,
    pub(crate) debug: bool,
    pub(crate) ignore_unexpected_smt: bool,
    pub(crate) rlimit: u32,
    pub(crate) air_initial_log: Emitter,
    pub(crate) air_middle_log: Emitter,
    pub(crate) air_final_log: Emitter,
    pub(crate) smt_log: Emitter,
    pub(crate) smt_transcript_log: Option<Box<dyn std::io::Write + Send>>,
    pub(crate) time_smt_init: Duration,
    pub(crate) time_smt_run: Duration,
    pub(crate) rlimit_count: Option<(u64, u64)>,
    pub(crate) state: ContextState,
    pub(crate) expected_solver_version: Option<String>,
    pub(crate) profile_logfile_name: Option<String>,
    pub(crate) single_check_query: bool,
    pub(crate) usage_info_enabled: bool,
    pub(crate) check_valid_used: bool,
    pub(crate) solver: SmtSolver,
    /// Put provenance ids on the wire: goal labels carry their AssertId.
    /// On by default under cvc5, which reads them back; z3 would only warn.
    pub(crate) emit_assert_ids: bool,
    /// Axioms that arrived without a tag and without a `:qid` to derive one
    /// from are tagged `ax_anon_<n>` with this counter.
    pub(crate) anon_axiom_count: u64,
    /// Provenance mode (`-V provenance`): cvc5 runs with preprocessing
    /// proofs, twice the per-query budget, and is asked for the sources of
    /// each query. Off by default; it perturbs the search, so plain runs stay
    /// the verdict of record.
    pub(crate) provenance: bool,
    /// The provenance of the last `check-sat`, until the caller takes it.
    pub(crate) last_provenance: Option<ProvenanceInfo>,
    /// Whether this solver may save and restore instantiations across
    /// rechecks of a query (cvc5 only, fixed at launch).
    pub(crate) instantiation_replay: bool,
    /// The key under which the next query's scope restores saved
    /// instantiations, and whether they are the only ones allowed (cvc5
    /// only).
    pub(crate) restore_instantiations: Option<(String, bool)>,
    /// The keys this solver has saved instantiations under.
    pub(crate) saved_instantiations: HashSet<String>,
    /// An `import-instantiations` command to send before the next query's
    /// first `check-sat`, once its declarations are in scope (cvc5 only).
    pub(crate) import_instantiations: Option<String>,
    variable_versions: VariableVersions,
}

impl Context {
    pub fn new(
        message_interface: Arc<dyn crate::messages::MessageInterface>,
        solver: SmtSolver,
    ) -> Self {
        let mut context = Context {
            message_interface: message_interface.clone(),
            smt_process: None,
            axiom_infos: ScopeMap::new(),
            axiom_infos_count: 0,
            array_map: ScopeMap::new(),
            array_count: 0,
            lambda_map: ScopeMap::new(),
            lambda_count: 0,
            choose_map: ScopeMap::new(),
            choose_count: 0,
            apply_map: ScopeMap::new(),
            apply_count: 0,
            typing: Typing {
                message_interface: message_interface.clone(),
                decls: crate::scope_map::ScopeMap::new(),
                snapshots: HashSet::new(),
                break_labels_local: HashSet::new(),
                break_labels_in_scope: crate::scope_map::ScopeMap::new(),
                solver: solver.clone(),
            },
            debug: false,
            ignore_unexpected_smt: false,
            rlimit: 0,
            air_initial_log: Emitter::new(
                message_interface.clone(),
                false,
                false,
                None,
                solver.clone(),
            ),
            air_middle_log: Emitter::new(
                message_interface.clone(),
                false,
                false,
                None,
                solver.clone(),
            ),
            air_final_log: Emitter::new(
                message_interface.clone(),
                false,
                false,
                None,
                solver.clone(),
            ),
            smt_log: Emitter::new(message_interface.clone(), true, true, None, solver.clone()),
            smt_transcript_log: None,
            time_smt_init: Duration::new(0, 0),
            time_smt_run: Duration::new(0, 0),
            rlimit_count: match solver {
                SmtSolver::Z3 => Some((0, 0)),
                SmtSolver::Cvc5 => None,
            },
            state: ContextState::NotStarted,
            expected_solver_version: None,
            profile_logfile_name: None,
            single_check_query: false,
            usage_info_enabled: false,
            check_valid_used: false,
            emit_assert_ids: matches!(solver, SmtSolver::Cvc5),
            anon_axiom_count: 0,
            provenance: false,
            last_provenance: None,
            instantiation_replay: false,
            restore_instantiations: None,
            saved_instantiations: HashSet::new(),
            import_instantiations: None,
            variable_versions: HashMap::new(),
            solver,
        };
        context.axiom_infos.push_scope(false);
        context.array_map.push_scope(false);
        context.lambda_map.push_scope(false);
        context.choose_map.push_scope(false);
        context.apply_map.push_scope(false);
        context.typing.decls.push_scope(false);
        context.typing.break_labels_in_scope.push_scope(false);
        context
    }

    pub fn get_smt_process(&mut self) -> &mut SmtProcess {
        // Only start the smt process if there are queries to run
        if self.smt_process.is_none() {
            let transcript_log = self.smt_transcript_log.take();
            self.smt_process =
                Some(SmtProcess::launch(
                    &self.solver,
                    transcript_log,
                    self.provenance,
                    self.instantiation_replay,
                ));
        }
        self.smt_process.as_mut().unwrap()
    }

    /// Send everything buffered since the last solver interaction and wait for
    /// the solver to acknowledge it, returning whatever it printed.
    ///
    /// `push`, `pop` and `global` only append to the pipe buffer; the solver
    /// does not see them until a query flushes it. A caller that needs to
    /// attribute the cost of those commands separately from the query that
    /// follows must flush them itself. Returns nothing before the solver has
    /// started, leaving the buffer intact: an unstarted context has no pending
    /// work worth launching one for.
    pub fn flush_commands(&mut self) -> Vec<String> {
        if self.smt_process.is_none() {
            return Vec::new();
        }
        let smt_data = self.smt_log.take_pipe_data();
        self.get_smt_process().send_commands(smt_data)
    }

    pub fn set_air_initial_log(&mut self, writer: Box<dyn std::io::Write + Send>) {
        self.air_initial_log.set_log(Some(writer));
    }

    pub fn set_air_middle_log(&mut self, writer: Box<dyn std::io::Write + Send>) {
        self.air_middle_log.set_log(Some(writer));
    }

    pub fn set_air_final_log(&mut self, writer: Box<dyn std::io::Write + Send>) {
        self.air_final_log.set_log(Some(writer));
    }

    pub fn set_smt_log(&mut self, writer: Box<dyn std::io::Write + Send>) {
        self.smt_log.set_log(Some(writer));
    }

    pub fn set_smt_transcript_log(&mut self, writer: Box<dyn std::io::Write + Send>) {
        if let Some(smt_process) = &mut self.smt_process {
            smt_process.set_transcript_log(writer);
        } else {
            self.smt_transcript_log = Some(writer);
        }
    }

    pub fn set_debug(&mut self, debug: bool) {
        self.debug = debug;
    }

    pub fn get_debug(&self) -> bool {
        self.debug
    }

    pub fn get_solver(&self) -> &SmtSolver {
        &self.solver
    }

    pub fn set_ignore_unexpected_smt(&mut self, ignore_unexpected_smt: bool) {
        self.ignore_unexpected_smt = ignore_unexpected_smt;
    }

    pub fn get_time(&self) -> (Duration, Duration) {
        (self.time_smt_init, self.time_smt_run)
    }

    pub fn get_rlimit_count(&self) -> Option<(u64, u64)> {
        self.rlimit_count
    }

    pub fn set_expected_solver_version(&mut self, version: String) {
        self.expected_solver_version = Some(version);
    }

    /// Whether goal labels (and, later, other top-level assertions) carry
    /// their provenance ids on the wire. Defaults to the solver being cvc5.
    pub fn set_emit_assert_ids(&mut self, enabled: bool) {
        self.emit_assert_ids = enabled;
    }

    /// The provenance cvc5 reported for the most recent `check-sat`, if any;
    /// each call returns it once.
    pub fn take_provenance(&mut self) -> Option<ProvenanceInfo> {
        self.last_provenance.take().map(|mut info| {
            info.variable_versions = self.variable_versions.clone();
            info
        })
    }

    /// Turn provenance mode on (cvc5 only; must precede the first query).
    /// Under it the solver is launched with `--proof-mode=pp-only`, each
    /// query runs with twice the budget, and the sources are requested.
    pub fn set_provenance(&mut self, enabled: bool) {
        assert!(matches!(self.state, ContextState::NotStarted));
        assert!(!enabled || matches!(self.solver, SmtSolver::Cvc5));
        self.provenance = enabled;
    }

    /// Allow saving and restoring instantiations (cvc5 only; must precede the
    /// first query). The solver is launched with `--no-fresh-declarations`,
    /// so a recheck's re-declared constants are the ones its saved
    /// instantiations mention.
    pub fn set_instantiation_replay(&mut self, enabled: bool) {
        assert!(matches!(self.state, ContextState::NotStarted));
        assert!(!enabled || matches!(self.solver, SmtSolver::Cvc5));
        self.instantiation_replay = enabled;
    }

    pub fn instantiation_replay(&self) -> bool {
        self.instantiation_replay
    }

    /// Restore the instantiations saved under `key` in the next query's scope
    /// (cvc5 only). cvc5 replays each saved term vector through its own
    /// instantiation path, and only for quantifiers that scope asserts, so a
    /// key that saved nothing, or saved for another query, is harmless. With
    /// `only`, no other instantiation happens in that scope, so the solver
    /// answers unsat or unknown from the restored instances alone.
    pub fn set_restore_instantiations(&mut self, key: Option<String>, only: bool) {
        assert!(key.is_none() || matches!(self.solver, SmtSolver::Cvc5));
        self.restore_instantiations = key.map(|key| (key, only));
    }

    /// Whether this solver has saved instantiations under `key`.
    pub fn has_saved_instantiations(&self, key: &str) -> bool {
        self.saved_instantiations.contains(key)
    }

    /// Send `command`, an `import-instantiations` command another solver
    /// exported, in the next query's scope just before its first `check-sat`,
    /// where the query's declarations are in scope (cvc5 only). cvc5 skips an
    /// entry naming a symbol it has not declared.
    pub fn set_import_instantiations(&mut self, command: Option<String>) {
        assert!(command.is_none() || matches!(self.solver, SmtSolver::Cvc5));
        self.import_instantiations = command;
    }

    /// Ask the solver for what `key` saved, as an `import-instantiations`
    /// command, and return its reply lines (cvc5 only). Flushes: call it
    /// after `save_instantiations` and before `finish_query`.
    pub fn export_instantiations(&mut self, key: &str) -> Vec<String> {
        assert!(matches!(self.solver, SmtSolver::Cvc5));
        self.smt_log.log_export_instantiations(key);
        self.flush_commands()
    }

    /// Save the current query's instantiations under `key` before
    /// `finish_query` pops its scope (cvc5 only). Call only after the solver
    /// answered the query: cvc5 rejects a save with no result to save from.
    pub fn save_instantiations(&mut self, key: &str) {
        assert!(matches!(self.solver, SmtSolver::Cvc5));
        self.smt_log.log_save_instantiations(key);
        self.saved_instantiations.insert(key.to_owned());
    }

    pub fn set_profile_with_logfile_name(&mut self, file_name: String) {
        assert!(matches!(self.state, ContextState::NotStarted));
        self.profile_logfile_name = Some(file_name);
    }

    pub fn set_rlimit(&mut self, rlimit: u32) {
        self.rlimit = rlimit;
        // The AIR logs record the budget in solver units whichever solver runs.
        self.air_initial_log.log_set_option("rlimit", &rlimit.to_string());
        self.air_middle_log.log_set_option("rlimit", &rlimit.to_string());
        self.air_final_log.log_set_option("rlimit", &rlimit.to_string());
    }

    pub fn set_single_check_query(&mut self) {
        self.single_check_query = true;
        self.air_initial_log.log_set_option("single_check_query", "true");
        self.air_middle_log.log_set_option("single_check_query", "true");
        self.air_final_log.log_set_option("single_check_query", "true");
    }

    pub fn enable_usage_info(&mut self) {
        assert!(matches!(self.state, ContextState::NotStarted));
        self.usage_info_enabled = true;
        self.set_z3_param_bool("produce-unsat-cores", true, true);
    }

    // emit blank line into log files
    pub fn blank_line(&mut self) {
        self.air_initial_log.blank_line();
        self.air_middle_log.blank_line();
        self.air_final_log.blank_line();
        self.smt_log.blank_line();
    }

    // Single-line comment, emitted with ";;" into log files
    pub fn comment(&mut self, s: &str) {
        self.air_initial_log.comment(s);
        self.air_middle_log.comment(s);
        self.air_final_log.comment(s);
        self.smt_log.comment(s);
    }

    fn log_set_z3_param(&mut self, option: &str, value: &str) {
        self.air_initial_log.log_set_option(option, value);
        self.air_middle_log.log_set_option(option, value);
        self.air_final_log.log_set_option(option, value);
        self.smt_log.log_set_option(option, value);
    }

    pub(crate) fn set_z3_param_bool(&mut self, option: &str, value: bool, write_to_logs: bool) {
        if option == "air_recommended_options" && value {
            match self.solver {
                SmtSolver::Z3 => {
                    self.set_z3_param_bool("auto_config", false, true);
                    self.set_z3_param_bool("smt.mbqi", false, true);
                    self.set_z3_param_u32("smt.case_split", 3, true);
                    self.set_z3_param_f64("smt.qi.eager_threshold", 100.0, true);
                    self.set_z3_param_bool("smt.delay_units", true, true);
                    self.set_z3_param_u32("smt.arith.solver", 2, true);
                    self.set_z3_param_bool("smt.arith.nl", false, true);
                    self.set_z3_param_bool("pi.enabled", false, true);
                    self.set_z3_param_bool("rewriter.sort_disjunctions", false, true);
                }
                SmtSolver::Cvc5 => {
                    self.smt_log.log_node(&node!((set-logic {str_to_node("ALL")})));
                    self.set_z3_param_bool("incremental", true, true);
                }
            }
        } else if option == "single_check_query" && value {
            self.single_check_query = true;
            if write_to_logs {
                self.set_single_check_query();
            }
        } else {
            if write_to_logs {
                self.log_set_z3_param(option, &value.to_string());
            }
        }
    }

    pub(crate) fn set_z3_param_u32(&mut self, option: &str, value: u32, write_to_logs: bool) {
        if option == "rlimit" && write_to_logs && matches!(self.solver, SmtSolver::Z3) {
            self.set_rlimit(value);
        } else {
            if write_to_logs {
                self.log_set_z3_param(option, &value.to_string());
            }
        }
    }

    pub(crate) fn set_z3_param_f64(&mut self, option: &str, value: f64, write_to_logs: bool) {
        if write_to_logs {
            let mut s = value.to_string();
            if !s.contains(".") {
                s += ".0";
            }
            self.log_set_z3_param(option, &s);
        }
    }

    pub(crate) fn set_z3_param_str(&mut self, option: &str, value: &str, write_to_logs: bool) {
        if write_to_logs {
            self.log_set_z3_param(option, value);
        }
    }

    pub fn set_z3_param(&mut self, option: &str, value: &str) {
        if value == "true" {
            self.set_z3_param_bool(option, true, true);
        } else if value == "false" {
            self.set_z3_param_bool(option, false, true);
        } else if let Ok(v) = value.parse::<u32>() {
            self.set_z3_param_u32(option, v, true);
        } else if let Ok(v) = value.parse::<f64>() {
            self.set_z3_param_f64(option, v, true);
        } else if value.is_ascii() {
            self.set_z3_param_str(option, value, true);
        } else {
            panic!("unexpected z3 param {}", value);
        }
    }

    pub(crate) fn push_name_scope(&mut self) {
        self.axiom_infos.push_scope(false);
        self.array_map.push_scope(false);
        self.lambda_map.push_scope(false);
        self.choose_map.push_scope(false);
        self.apply_map.push_scope(false);
        self.typing.decls.push_scope(false);
    }

    pub(crate) fn pop_name_scope(&mut self) {
        self.axiom_infos.pop_scope();
        self.array_map.pop_scope();
        self.lambda_map.pop_scope();
        self.choose_map.pop_scope();
        self.apply_map.pop_scope();
        self.typing.decls.pop_scope();
    }

    fn ensure_started(&mut self) {
        match self.state {
            ContextState::NotStarted => {
                let profile_logfile_name = self.profile_logfile_name.clone();
                if let Some(profile_logfile_name) = profile_logfile_name {
                    self.set_z3_param("trace", "true");
                    // Very expensive.  May be needed to support more detailed log analysis.
                    // self.set_z3_param("proof", "true");

                    // sise does not support backslashes in atoms, which appear in Windows paths
                    let profile_logfile_name = profile_logfile_name.replace("\\", "/");
                    self.log_set_z3_param("trace_file_name", &profile_logfile_name);
                }
                self.blank_line();
                if self.provenance {
                    self.comment(&format!(
                        "provenance mode: cvc5 args {}",
                        crate::smt_process::PROVENANCE_ARGS.join(" ")
                    ));
                }
                self.comment("AIR prelude");
                self.smt_log.log_node(&node!((declare-sort {str_to_node(crate::def::FUNCTION)} 0)));
                self.blank_line();
                self.state = ContextState::ReadyForQuery;
            }
            ContextState::ReadyForQuery => {}
            ContextState::NoMoreQueriesAllowed => {
                panic!("no more queries allowed after disabling incremental solving");
            }
            _ => {
                panic!("expected call to finish_query before next command");
            }
        }
    }

    pub fn push(&mut self) {
        self.ensure_started();
        self.air_initial_log.log_push();
        self.air_middle_log.log_push();
        self.air_final_log.log_push();
        self.smt_log.log_push();
        self.push_name_scope();
    }

    pub fn pop(&mut self) {
        self.air_initial_log.log_pop();
        self.air_middle_log.log_pop();
        self.air_final_log.log_pop();
        self.smt_log.log_pop();
        self.pop_name_scope();
    }

    pub fn global(&mut self, decl: &Decl) -> Result<(), TypeError> {
        self.ensure_started();
        self.air_initial_log.log_decl(decl);
        self.air_middle_log.log_decl(decl);
        self.air_final_log.log_decl(decl);
        let (gen_decls, decl) = crate::typecheck::check_decl(self, decl)?;
        for gen_decl in gen_decls.iter() {
            crate::smt_verify::smt_add_decl(self, gen_decl);
        }
        crate::typecheck::add_decl(self, &decl, true)?;
        crate::smt_verify::smt_add_decl(self, &decl);
        Ok(())
    }

    pub fn check_valid(
        &mut self,
        message_interface: &dyn crate::messages::MessageInterface,
        diagnostics: &impl Diagnostics,
        query: &Query,
        query_context: QueryContext<'_, '_>,
    ) -> ValidityResult {
        self.ensure_started();

        self.air_initial_log.log_query(query);
        let query = match crate::typecheck::check_query(self, query) {
            Ok(query) => query,
            Err(err) => return ValidityResult::TypeError(err),
        };
        let (query, snapshots, local_vars, variable_versions) =
            crate::var_to_const::lower_query(&query, self.provenance);
        self.variable_versions = variable_versions;
        self.air_middle_log.log_query(&query);
        let query = crate::block_to_assert::lower_query(message_interface, &query);
        self.air_final_log.log_query(&query);

        let model = Model::new(snapshots, local_vars);
        let validity = crate::smt_verify::smt_check_query(
            self,
            diagnostics,
            &query,
            model,
            query_context.report_long_running,
        );
        self.check_valid_used = true;

        validity
    }

    pub fn check_valid_used(&self) -> bool {
        self.check_valid_used
    }

    /// After receiving ValidityResult::Invalid, try to find another error.
    /// only_check_earlier == true means to only look for errors preceding all the previous
    /// errors, with the goal of making sure that the earliest error gets reported.
    /// Once only_check_earlier is set, it remains set until finish_query is called.
    pub fn check_valid_again(
        &mut self,
        diagnostics: &impl Diagnostics,
        only_check_earlier: bool,
        query_context: QueryContext<'_, '_>,
    ) -> ValidityResult {
        if let ContextState::FoundInvalid(infos, Some(air_model)) = self.state.clone() {
            let res = crate::smt_verify::smt_check_assertion(
                self,
                diagnostics,
                infos,
                air_model,
                only_check_earlier,
                query_context.report_long_running,
            );
            self.check_valid_used = true;
            res
        } else {
            panic!("check_valid_again expected query to be ValidityResult::Invalid(_, Some(_))");
        }
    }

    pub fn finish_query(&mut self) {
        if self.single_check_query {
            self.state = ContextState::NoMoreQueriesAllowed;
        } else {
            self.pop_name_scope();
            self.smt_log.log_pop();
            self.state = ContextState::ReadyForQuery;
        }
    }

    pub fn eval_expr(&mut self, expr: sise::TreeNode) -> String {
        self.smt_log.log_eval(expr);
        let smt_data = self.smt_log.take_pipe_data();
        let smt_output = self.get_smt_process().send_commands(smt_data);
        if smt_output.len() != 1 {
            panic!("unexpected output from SMT eval {:?}", smt_output);
        }
        smt_output[0].clone()
    }

    pub fn command(
        &mut self,
        message_interface: &dyn crate::messages::MessageInterface,
        diagnostics: &impl Diagnostics,
        command: &Command,
        query_context: QueryContext<'_, '_>,
    ) -> ValidityResult {
        match &**command {
            CommandX::Push => {
                self.push();
                ValidityResult::Valid(UsageInfo::None)
            }
            CommandX::Pop => {
                self.pop();
                ValidityResult::Valid(UsageInfo::None)
            }
            CommandX::SetOption(option, value) => {
                self.set_z3_param(option, value);
                ValidityResult::Valid(UsageInfo::None)
            }
            CommandX::Global(decl) => {
                if let Err(err) = self.global(&decl) {
                    ValidityResult::TypeError(err)
                } else {
                    ValidityResult::Valid(UsageInfo::None)
                }
            }
            CommandX::CheckValid(query) => {
                self.check_valid(message_interface, diagnostics, &query, query_context)
            }
            #[cfg(feature = "singular")]
            CommandX::CheckSingular(_) => {
                panic!("CheckSingular not supported in this context");
            }
        }
    }
}
