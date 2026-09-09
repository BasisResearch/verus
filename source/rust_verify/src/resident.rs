//! Recheck retained AIR queries against their original bucket context.
//!
//! This driver serves one immutable compilation over JSON lines. It never reads
//! replacement source or accepts new assertions from its caller.

use crate::commands::{QueryOp, Style};
use air::ast::{CommandX, Commands, Query};
use air::context::{Context, QueryContext, ValidityResult};
use air::messages::{ArcDynMessage, Diagnostics, MessageLevel};
use serde::{Deserialize, Serialize};
use std::cell::RefCell;
use std::io::{self, BufRead, Read, Write};
use std::time::{Instant, SystemTime, UNIX_EPOCH};
use vir::ast_util::fun_as_friendly_rust_name;
use vir::def::{CommandContext, CommandsWithContext};
use vir::messages::{MessageX, VirMessageInterface};

#[derive(Clone, Copy, Deserialize, Serialize)]
#[serde(transparent)]
struct QueryId(usize);

struct RetainedQuery {
    query: Query,
    context: CommandContext,
    prefix: usize,
    rlimit: f32,
    kind: QueryKind,
}

#[derive(Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
enum QueryKind {
    Termination,
    Body,
    RecommendsFollowup,
    Recommends,
    Expanded,
    ApiSafety,
}

impl QueryKind {
    fn from_op(op: &QueryOp) -> Self {
        match op {
            QueryOp::SpecTermination => Self::Termination,
            QueryOp::Body(Style::Normal) => Self::Body,
            QueryOp::Body(Style::RecommendsFollowupFromError) => Self::RecommendsFollowup,
            QueryOp::Body(Style::RecommendsChecked) => Self::Recommends,
            QueryOp::Body(Style::Expanded) => Self::Expanded,
            QueryOp::Body(Style::CheckApiSafety) => Self::ApiSafety,
        }
    }
}

/// A journal of bucket declarations and queries from one compilation.
///
/// Every journal entry has its own AIR/SMT scope. `applied` is the length of
/// the prefix currently asserted. A query can run only at its recorded prefix,
/// so declarations and axioms introduced later cannot affect an earlier query.
pub(crate) struct Session {
    contexts: Vec<Commands>,
    queries: Vec<RetainedQuery>,
    applied: usize,
}

#[derive(Deserialize)]
#[serde(tag = "command", rename_all = "snake_case", deny_unknown_fields)]
enum Request {
    List,
    Check { session: String, query: QueryId },
    Close { session: String },
}

#[derive(Serialize)]
struct QueryDescription {
    id: QueryId,
    function: String,
    description: String,
    kind: QueryKind,
    span: String,
}

#[derive(Serialize)]
#[serde(tag = "event", rename_all = "snake_case")]
enum Response<'a> {
    Ready {
        protocol: u32,
        session: &'a str,
        bucket: &'a str,
        process_id: u32,
        queries: &'a [QueryDescription],
    },
    Queries {
        session: &'a str,
        queries: &'a [QueryDescription],
    },
    Checked {
        session: &'a str,
        query: QueryId,
        result: QueryResult,
        assert_id: Option<Vec<u64>>,
        diagnostics: Vec<SourceDiagnostic>,
        elapsed_ms: u128,
    },
    Error {
        message: &'a str,
    },
    Closed {
        session: &'a str,
    },
}

#[derive(Serialize)]
#[serde(rename_all = "snake_case")]
enum QueryResult {
    Valid,
    Invalid,
    ResourceLimit,
}

#[derive(Serialize)]
struct SourceDiagnostic {
    level: MessageLevel,
    message: String,
    spans: Vec<String>,
    labels: Vec<SourceLabel>,
}

#[derive(Serialize)]
struct SourceLabel {
    message: String,
    span: String,
}

#[derive(Default)]
struct QueryDiagnostics(RefCell<Vec<SourceDiagnostic>>);

impl QueryDiagnostics {
    fn record(&self, message: &ArcDynMessage, level: MessageLevel) {
        let message = message.downcast_ref::<MessageX>().expect("VIR diagnostic message");
        self.0.borrow_mut().push(SourceDiagnostic {
            level,
            message: message.note.clone(),
            spans: message.spans.iter().map(|span| span.as_string.clone()).collect(),
            labels: message
                .labels
                .iter()
                .map(|label| SourceLabel {
                    message: label.note.clone(),
                    span: label.span.as_string.clone(),
                })
                .collect(),
        });
    }
}

impl Diagnostics for QueryDiagnostics {
    fn report(&self, message: &ArcDynMessage) {
        let level = message.downcast_ref::<MessageX>().expect("VIR diagnostic message").level;
        self.record(message, level);
    }

    fn report_now(&self, message: &ArcDynMessage) {
        self.report(message);
    }

    fn report_as(&self, message: &ArcDynMessage, level: MessageLevel) {
        self.record(message, level);
    }

    fn report_as_now(&self, message: &ArcDynMessage, level: MessageLevel) {
        self.record(message, level);
    }
}

fn send(output: &mut impl Write, response: &Response<'_>) -> io::Result<()> {
    serde_json::to_writer(&mut *output, response)?;
    writeln!(output)?;
    output.flush()
}

impl Session {
    pub(crate) fn new() -> Self {
        Self { contexts: Vec::new(), queries: Vec::new(), applied: 0 }
    }

    /// Begin a scope before the verifier emits the next declaration batch.
    pub(crate) fn push_context(
        &mut self,
        air: &mut Context,
        commands: Commands,
    ) -> Result<(), &'static str> {
        if commands.iter().any(|command| !matches!(**command, CommandX::Global(_))) {
            return Err("resident context batches must contain only declarations");
        }
        debug_assert_eq!(self.applied, self.contexts.len());
        air.push();
        self.contexts.push(commands);
        self.applied += 1;
        Ok(())
    }

    /// Retain the lowered query and the declaration prefix that precedes it.
    pub(crate) fn record_query(
        &mut self,
        commands: CommandsWithContext,
        op: &QueryOp,
        rlimit: f32,
    ) -> Result<(), &'static str> {
        if commands.commands.iter().any(|command| !matches!(**command, CommandX::CheckValid(_))) {
            return Err("resident query batches must contain only check-valid commands");
        }
        for command in commands.commands.iter() {
            if let CommandX::CheckValid(query) = &**command {
                self.queries.push(RetainedQuery {
                    query: query.clone(),
                    context: commands.context.clone(),
                    prefix: self.applied,
                    rlimit,
                    kind: QueryKind::from_op(op),
                });
            }
        }
        Ok(())
    }

    fn restore_prefix(&mut self, air: &mut Context, prefix: usize) -> io::Result<()> {
        while self.applied > prefix {
            air.pop();
            self.applied -= 1;
        }
        while self.applied < prefix {
            air.push();
            for command in self.contexts[self.applied].iter() {
                if let CommandX::Global(decl) = &**command {
                    air.global(decl).map_err(|error| io::Error::other(error.to_string()))?;
                }
            }
            self.applied += 1;
        }
        Ok(())
    }

    pub(crate) fn serve(
        mut self,
        air: &mut Context,
        bucket: String,
        set_rlimit: impl Fn(&mut Context, f32),
    ) -> io::Result<()> {
        let stamp = SystemTime::now().duration_since(UNIX_EPOCH).map_err(io::Error::other)?;
        let session = format!("{}-{}", std::process::id(), stamp.as_nanos());
        let input = io::stdin();
        let output = io::stdout();
        self.run(air, &bucket, &session, input.lock(), output.lock(), set_rlimit)
    }

    fn run(
        &mut self,
        air: &mut Context,
        bucket: &str,
        session: &str,
        mut input: impl BufRead,
        mut output: impl Write,
        set_rlimit: impl Fn(&mut Context, f32),
    ) -> io::Result<()> {
        let queries: Vec<_> = self
            .queries
            .iter()
            .enumerate()
            .map(|(id, query)| QueryDescription {
                id: QueryId(id),
                function: fun_as_friendly_rust_name(&query.context.fun),
                description: query.context.desc.clone(),
                kind: query.kind,
                span: query.context.span.as_string.clone(),
            })
            .collect();
        send(
            &mut output,
            &Response::Ready {
                protocol: 1,
                session,
                bucket,
                process_id: std::process::id(),
                queries: &queries,
            },
        )?;
        loop {
            // A framing failure closes the session. Never interpret a suffix of
            // an oversized request as a second request.
            let mut line = String::new();
            if input.by_ref().take(65537).read_line(&mut line)? == 0 {
                self.restore_prefix(air, 0)?;
                return Ok(());
            }
            if line.len() > 65536 {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "resident request exceeds 64 KiB",
                ));
            }
            let request = match serde_json::from_str::<Request>(&line) {
                Ok(request) => request,
                Err(_) => {
                    send(&mut output, &Response::Error { message: "invalid resident request" })?;
                    continue;
                }
            };
            match request {
                Request::List => {
                    send(&mut output, &Response::Queries { session, queries: &queries })?
                }
                Request::Check { session: requested, .. }
                | Request::Close { session: requested }
                    if requested != session =>
                {
                    send(
                        &mut output,
                        &Response::Error { message: "session does not match this compilation" },
                    )?;
                }
                Request::Close { .. } => {
                    self.restore_prefix(air, 0)?;
                    send(&mut output, &Response::Closed { session })?;
                    return Ok(());
                }
                Request::Check { query: id, .. } => {
                    let Some(query) = self.queries.get(id.0) else {
                        send(&mut output, &Response::Error { message: "unknown query" })?;
                        continue;
                    };
                    let prefix = query.prefix;
                    self.restore_prefix(air, prefix)?;
                    let query = &self.queries[id.0];
                    set_rlimit(air, query.rlimit);
                    let diagnostics = QueryDiagnostics::default();
                    let start = Instant::now();
                    let result = air.check_valid(
                        &VirMessageInterface {},
                        &diagnostics,
                        &query.query,
                        QueryContext::default(),
                    );
                    let (result, assert_id) = match result {
                        ValidityResult::Valid(_) => (QueryResult::Valid, None),
                        ValidityResult::Invalid(_, error, id) => {
                            if let Some(error) = error {
                                diagnostics.report(&error);
                            }
                            (QueryResult::Invalid, id.map(|id| (*id).clone()))
                        }
                        ValidityResult::Canceled => (QueryResult::ResourceLimit, None),
                        ValidityResult::TypeError(error) => {
                            return Err(io::Error::other(error.to_string()));
                        }
                        ValidityResult::UnexpectedOutput(error) => {
                            return Err(io::Error::other(error));
                        }
                    };
                    air.finish_query();
                    send(
                        &mut output,
                        &Response::Checked {
                            session,
                            query: id,
                            result,
                            assert_id,
                            diagnostics: diagnostics.0.into_inner(),
                            elapsed_ms: start.elapsed().as_millis(),
                        },
                    )?;
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use air::context::SmtSolver;
    use std::sync::Arc;

    fn commands(text: &str) -> Commands {
        let text = format!("({text})");
        let node = sise::parse_tree(&mut sise::Parser::new(&text)).unwrap();
        let sise::TreeNode::List(nodes) = node else { panic!("expected command list") };
        air::parser::Parser::new(Arc::new(VirMessageInterface {}))
            .nodes_to_commands(&nodes)
            .unwrap()
    }

    #[test]
    fn later_axioms_cannot_prove_an_earlier_query() {
        let mut air = Context::new(Arc::new(VirMessageInterface {}), SmtSolver::Cvc5);
        air.set_z3_param("air_recommended_options", "true");
        let diagnostics = QueryDiagnostics::default();
        let base = commands("(declare-const x Int)");
        let later = commands("(declare-const y Int) (axiom (= x y)) (axiom (= y 0))");
        let query = commands("(check-valid (assert (= x 0)))");
        let mut session = Session::new();
        for command in base.iter() {
            if let CommandX::Global(decl) = &**command {
                air.global(decl).unwrap();
            }
        }
        session.push_context(&mut air, later.clone()).unwrap();
        for command in later.iter() {
            if let CommandX::Global(decl) = &**command {
                air.global(decl).unwrap();
            }
        }
        // Repeated backwards/forwards jumps exercise both removal of axioms
        // and redeclaration of names removed with their scope.
        for (prefix, valid) in [(1, true), (0, false), (1, true), (0, false)] {
            session.restore_prefix(&mut air, prefix).unwrap();
            let result = air.command(
                &VirMessageInterface {},
                &diagnostics,
                &query[0],
                QueryContext::default(),
            );
            if valid {
                assert!(matches!(result, ValidityResult::Valid(_)), "{result:?}");
            } else {
                assert!(matches!(result, ValidityResult::Invalid(..)), "{result:?}");
            }
            air.finish_query();
        }
    }

    #[test]
    fn oversized_request_closes_without_parsing_its_suffix() {
        let mut air = Context::new(Arc::new(VirMessageInterface {}), SmtSolver::Cvc5);
        let mut session = Session::new();
        let input = format!("{}\n{{\"command\":\"list\"}}\n", " ".repeat(65537));
        let mut output = Vec::new();
        let error = session
            .run(&mut air, "test", "test", input.as_bytes(), &mut output, |_, _| {})
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert_eq!(String::from_utf8(output).unwrap().lines().count(), 1);
    }
}
