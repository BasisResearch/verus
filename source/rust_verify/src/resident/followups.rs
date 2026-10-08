//! What a batch run checks and prints after a body check fails, served by a
//! resident session for the checks it answers itself.
//!
//! After a function's body check fails an assertion, the batch run goes on
//! with that function's follow-ups (`verifier::verify_bucket`): under
//! `--expand-errors`, the expand-errors chain (`ExpandErrorsDriver` and the
//! `Style::Expanded` queries it asks for, each focused on one sub-assertion
//! and checked in the body's solver at the body's prefix) ending in its
//! `diagnostics via expansion` note; then, unless a round ran out of its
//! budget or `--no-auto-recommends-check` is set, the recommends follow-up.
//!
//! A check request with `followups` does the same after a failed body check
//! and answers `printed`: the diagnostics of the check and its follow-ups in
//! the order the batch run prints them. That order is not the order they
//! were found in. The batch run reports a failure that comes with a model
//! when the function's op chain ends (or when a check has run for two
//! seconds, or when the expand-errors chain starts), and everything else as
//! it comes; with more than one thread its main thread sorts each group of
//! deferred diagnostics by their first span (`verifier::QueuedReporter`).
//! `PrintOrder` follows those rules. A session that checks its queries itself
//! records the same list in each failing function's `initial` verdict, read
//! off its own reporter (`verifier::PrintTee`).
//!
//! The expand-errors chain needs the function's SST and a VIR context for its
//! bucket, which a session does not keep: `ExpansionSource` keeps the crate
//! and rebuilds them for the failing function's bucket on demand, as the
//! verifier built them (`verifier::verify_bucket_outer`), and walks the
//! bucket's ops to the function's body op with the verifier's own
//! `OpGenerator`. The rebuilt body query must print as the retained one does
//! (`query_text`), or the expansion is refused rather than answered from a
//! context that differs from the one the query was checked in.

use super::SourceDiagnostic;
use crate::buckets::{Bucket, BucketId};
use crate::commands::{OpGenerator, OpKind, QueryOp, Style};
use crate::expand_errors_driver::ExpandErrorsResult;
use air::ast::{CommandX, Query};
use air::messages::{ArcDynMessage, MessageLevel};
use rustc_session::config::ErrorOutputType;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use vir::ast::{Fun, Krate};
use vir::def::CommandsWithContext;
use vir::messages::{MessageX, VirMessageInterface};

/// How the batch run hands a diagnostic to its reporter
/// (`verifier::check_result_validity`): at once, or kept until the function's
/// op chain flushes what it collected, sorted there by the position of the
/// first span (`SpanData` order: start, then end) when the run has threads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Emit {
    Now,
    Collect(Option<(u32, u32)>),
}

/// One thing a check reported, in the order it happened.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Emitted {
    /// The check's diagnostic of this index, handed over this way.
    Diagnostic(usize, Emit),
    /// The check ran for two seconds: the batch run's long-running hook
    /// flushes what the op chain had collected.
    Flush,
}

/// Where the batch run's main thread sorts a collected diagnostic: by its
/// first span, a raw `SpanData` (`spans::from_raw_span`), none first.
pub(super) fn sort_key(message: &MessageX) -> Option<(u32, u32)> {
    message.spans.first().and_then(raw_span_key)
}

/// A span's place in the source map, as rustc orders spans (`SpanData`:
/// start, then end), read without the session globals a server thread lacks.
pub(super) fn raw_span_key(span: &vir::messages::Span) -> Option<(u32, u32)> {
    let raw = &(*span.raw_span) as &(dyn std::any::Any + Send + Sync);
    raw.downcast_ref::<rustc_span::SpanData>().map(|data| (data.lo.0, data.hi.0))
}

/// The batch run's reporter for one function's op chain, as far as the order
/// of what it prints goes (see the module documentation).
pub(super) struct PrintOrder {
    printed: Vec<SourceDiagnostic>,
    collected: Option<Vec<(Option<(u32, u32)>, SourceDiagnostic)>>,
    sort: bool,
}

impl PrintOrder {
    /// `sort`: whether the run verifies with threads, whose main thread sorts
    /// each flushed group (`--num-threads` other than 1).
    pub(super) fn new(sort: bool) -> Self {
        PrintOrder { printed: Vec::new(), collected: Some(Vec::new()), sort }
    }

    pub(super) fn now(&mut self, diagnostic: SourceDiagnostic) {
        self.printed.push(diagnostic);
    }

    pub(super) fn collect(&mut self, key: Option<(u32, u32)>, diagnostic: SourceDiagnostic) {
        match &mut self.collected {
            Some(collected) => collected.push((key, diagnostic)),
            None => self.printed.push(diagnostic),
        }
    }

    pub(super) fn flush(&mut self) {
        if let Some(mut collected) = self.collected.take() {
            if self.sort {
                // Stable, as the batch run's `sort_by_key` is.
                collected.sort_by_key(|(key, _)| *key);
            }
            self.printed.extend(collected.into_iter().map(|(_, diagnostic)| diagnostic));
        }
    }

    /// Replay what one check reported.
    pub(super) fn replay(&mut self, diagnostics: &[SourceDiagnostic], emitted: &[Emitted]) {
        for emitted in emitted {
            match *emitted {
                Emitted::Diagnostic(i, Emit::Now) => self.now(diagnostics[i].clone()),
                Emitted::Diagnostic(i, Emit::Collect(key)) => {
                    self.collect(key, diagnostics[i].clone())
                }
                Emitted::Flush => self.flush(),
            }
        }
    }

    /// The end of the op chain: everything still collected is printed.
    pub(super) fn finish(mut self) -> Vec<SourceDiagnostic> {
        self.flush();
        self.printed
    }
}

/// A query printed as AIR, its quantifiers' patterns sorted and their bucket
/// counters dropped, as fingerprints read it (`Fnv::node`): what a rebuilt
/// query is compared to the retained one by.
pub(super) fn query_text(query: &Query) -> String {
    let printer = air::printer::Printer::new(
        Arc::new(VirMessageInterface {}),
        false,
        air::context::SmtSolver::Cvc5,
    );
    let mut node = printer.query_to_node(query);
    super::sort_patterns(&mut node);
    super::forget_quantifier_counters(&mut node);
    air::printer::node_to_string(&node)
}

/// What a session keeps to rebuild a bucket's VIR context and SST when one of
/// its checks needs the expand-errors chain: the crate as the verifier
/// verified it (after `ast_simplify`), a crate-wide context to start each
/// bucket's from, and each bucket's functions.
pub(crate) struct ExpansionSource {
    pub(crate) krate: Krate,
    pub(crate) crate_id: vir::ast::CrateId,
    pub(crate) global: Mutex<vir::context::GlobalCtx>,
    pub(crate) buckets: HashMap<BucketId, HashSet<Fun>>,
    pub(crate) error_format: Option<ErrorOutputType>,
}

/// A rebuilt expansion's outcome.
pub(super) struct Expansion {
    /// The `diagnostics via expansion` note the batch run reports at the end
    /// of the chain, if the chain got that far.
    pub(super) note: Option<ArcDynMessage>,
    /// Expanded queries checked.
    pub(super) queries: usize,
}

/// Ignores what rebuilding a bucket reports: the session's own compilation
/// reported it already.
struct Silent;

impl air::messages::Diagnostics for Silent {
    fn report_as(&self, _: &ArcDynMessage, _: MessageLevel) {}
    fn report(&self, _: &ArcDynMessage) {}
    fn report_now(&self, _: &ArcDynMessage) {}
    fn report_as_now(&self, _: &ArcDynMessage, _: MessageLevel) {}
}

impl ExpansionSource {
    /// Rebuild `bucket`'s context and SST as `verify_bucket_outer` builds them.
    fn rebuild(
        &self,
        bucket: &BucketId,
    ) -> Result<(vir::context::Ctx, vir::sst::KrateSst), String> {
        let message = |error: vir::ast::VirErr| error.note.clone();
        let global = self
            .global
            .lock()
            .map_err(|_| "the crate context is poisoned".to_owned())?
            .from_self_with_log(Arc::new(Mutex::new(None)));
        let (pruned_krate, prune_info) = vir::prune::prune_krate_for_module_or_krate(
            &self.krate,
            &self.crate_id,
            None,
            Some(bucket.module().clone()),
            bucket.function(),
            true,
            true,
        );
        let vir::prune::PruneInfo {
            mono_abstract_datatypes,
            spec_fn_types,
            used_builtins,
            fndef_types,
            resolved_typs,
            dyn_traits,
        } = prune_info;
        let module = pruned_krate
            .modules
            .iter()
            .find(|m| &m.x.path == bucket.module())
            .ok_or_else(|| "the bucket's module is not in the crate".to_owned())?
            .clone();
        let mut ctx = vir::context::Ctx::new(
            &pruned_krate,
            global,
            module,
            mono_abstract_datatypes.expect("monotypes collected"),
            spec_fn_types,
            dyn_traits,
            used_builtins,
            fndef_types,
            resolved_typs.expect("resolvable types collected"),
            false,
        )
        .map_err(message)?;
        let funs = self.buckets.get(bucket).ok_or_else(|| "unknown bucket".to_owned())?;
        let krate_sst =
            vir::ast_to_sst_crate::ast_to_sst_krate(&mut ctx, &Silent, funs, &pruned_krate)
                .map_err(message)?;
        let krate_sst = vir::poly::poly_krate_for_module(&mut ctx, &krate_sst);
        Ok((ctx, krate_sst))
    }

    /// Run the expand-errors chain for `fun`'s body query, which failed at
    /// `assert_id`, as the batch run does after that failure
    /// (`start_expand_errors_if_possible`, then `expand_errors_next` until it
    /// returns the note). `check` checks one expanded query's commands and
    /// says whether it failed and whether it ran out of budget.
    pub(super) fn expand(
        &self,
        bucket: &BucketId,
        fun: &Fun,
        body: &str,
        assert_id: air::ast::AssertId,
        mut check: impl FnMut(&CommandsWithContext) -> std::io::Result<(bool, bool)>,
    ) -> Result<Expansion, String> {
        let (mut ctx, krate_sst) = self.rebuild(bucket)?;
        let funs = self.buckets.get(bucket).ok_or_else(|| "unknown bucket".to_owned())?.clone();
        let mut opgen = OpGenerator::new(&mut ctx, &krate_sst, Bucket { funs });
        loop {
            let Some(mut function_opgen) = opgen.next().map_err(|error| error.note.clone())? else {
                return Err("the rebuilt bucket has no body check for the function".to_owned());
            };
            while let Some(op) = function_opgen.next() {
                let OpKind::Query {
                    query_op: QueryOp::Body(Style::Normal),
                    commands_with_context_list,
                    ..
                } = &op.kind
                else {
                    continue;
                };
                if &op.get_function().x.name != fun {
                    continue;
                }
                let same = commands_with_context_list.iter().any(|cmds| {
                    cmds.commands.iter().any(|command| match &**command {
                        CommandX::CheckValid(query) => query_text(query) == body,
                        _ => false,
                    })
                });
                if !same {
                    return Err("the rebuilt body check differs from the one the session retained"
                        .to_owned());
                }
                function_opgen.start_expand_errors_if_possible(&op, assert_id);
                let mut queries = 0;
                loop {
                    match function_opgen.expand_errors_next(self.error_format) {
                        None => return Ok(Expansion { note: None, queries }),
                        Some(Err(note)) => return Ok(Expansion { note: Some(note), queries }),
                        Some(Ok(expanded)) => {
                            let OpKind::Query { commands_with_context_list, .. } = &expanded.kind
                            else {
                                return Err("an expand-errors op that is not a query".to_owned());
                            };
                            let (mut invalid, mut timed_out) = (false, false);
                            for cmds in commands_with_context_list.iter() {
                                let (i, t) = check(cmds).map_err(|error| error.to_string())?;
                                invalid |= i;
                                timed_out |= t;
                            }
                            queries += 1;
                            function_opgen.report_expand_error_result(if timed_out {
                                ExpandErrorsResult::Timeout
                            } else if invalid {
                                ExpandErrorsResult::Fail
                            } else {
                                ExpandErrorsResult::Pass
                            });
                        }
                    }
                }
            }
        }
    }
}
