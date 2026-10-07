use crate::ast::{Decl, Expr, Ident, Query};
use crate::context::SmtSolver;
use crate::instantiations::ImportInstantiations;
use crate::printer::{NodeWriter, Printer, macro_push_node};
use crate::{node, nodes};
use sise::TreeNode as Node;
use std::io::Write;

pub(crate) struct Emitter {
    /// AIR/SMT -> Node printer
    printer: Printer,
    /// Node -> string writer
    node_writer: NodeWriter,
    /// buffer for data to be sent across pipe to Z3 process
    pipe_buffer: Option<Vec<u8>>,
    /// log file
    log: Option<Box<dyn std::io::Write + Send>>,
    /// string of space characters representing current indentation level
    current_indent: String,
    /// What a relaunched solver needs to reach the state this one is in
    /// (`Context::suspend`), when the context keeps it.
    pub(crate) replay: Option<Replay>,
}

/// The commands that built a solver's current state, kept so that the solver
/// can be stopped and a new one brought to the same state: every declaration,
/// definition, assertion and option sent to it, by assertion level. A `pop`
/// drops what its level added, so what is kept is what the solver holds now,
/// not its history. Checks and queries (`check-sat`, `get-*`, `eval`, `echo`
/// and the Basis extensions) change no assertion and are not kept. Options
/// are global rather than scoped, so they stay at the base level whichever
/// level set them.
#[derive(Default)]
pub(crate) struct Replay {
    levels: Vec<Vec<u8>>,
    /// The commands taken from the pipe last, which the solver may not have
    /// been sent yet: a context whose solver is stopped takes its next
    /// commands and only then relaunches, and the relaunched solver must get
    /// the state from before them, then them.
    staged: Vec<u8>,
    /// The levels are deflated: the solver is stopped, and a module of
    /// hundreds of stopped solvers would otherwise hold each one's whole
    /// context as text.
    frozen: bool,
}

impl Replay {
    pub(crate) fn new() -> Self {
        Replay { levels: vec![Vec::new()], staged: Vec::new(), frozen: false }
    }

    /// Deflate the record while its solver is stopped.
    pub(crate) fn freeze(&mut self) {
        if self.frozen {
            return;
        }
        for level in &mut self.levels {
            let mut encoder =
                flate2::write::DeflateEncoder::new(Vec::new(), flate2::Compression::fast());
            encoder.write_all(level).expect("deflating into memory");
            *level = encoder.finish().expect("deflating into memory");
        }
        self.frozen = true;
    }

    /// Inflate a frozen record, to extend it or send it.
    pub(crate) fn thaw(&mut self) {
        if !self.frozen {
            return;
        }
        for level in &mut self.levels {
            let mut text = Vec::new();
            std::io::Read::read_to_end(
                &mut flate2::read::DeflateDecoder::new(&level[..]),
                &mut text,
            )
            .expect("inflating a record this process deflated");
            *level = text;
        }
        self.frozen = false;
    }

    /// Commands taken from the pipe, about to be sent. The ones taken before
    /// them have reached a solver by now.
    pub(crate) fn stage(&mut self, data: &[u8]) {
        self.commit();
        self.staged = data.to_vec();
    }

    /// Fold the staged commands into the record: they reached the solver.
    pub(crate) fn commit(&mut self) {
        let staged = std::mem::take(&mut self.staged);
        self.record(&staged);
    }

    /// Fold commands that were sent to the solver into the record.
    pub(crate) fn record(&mut self, data: &[u8]) {
        if data.is_empty() {
            return;
        }
        self.thaw();
        for form in top_level_forms(data) {
            let head = form_head(form);
            match head {
                "push" | "pop" => {
                    let n = form_count(form);
                    for _ in 0..n {
                        if head == "push" {
                            self.levels.push(b"(push 1)\n".to_vec());
                        } else if self.levels.len() > 1 {
                            self.levels.pop();
                        }
                    }
                }
                "set-option" | "set-logic" | "set-info" => {
                    self.levels[0].extend_from_slice(form);
                    self.levels[0].push(b'\n');
                }
                "declare-fun" | "declare-const" | "declare-sort" | "declare-datatype"
                | "declare-datatypes" | "define-fun" | "define-fun-rec" | "define-funs-rec"
                | "define-sort" | "define-const" | "assert" => {
                    let level = self.levels.last_mut().expect("the base level");
                    level.extend_from_slice(form);
                    level.push(b'\n');
                }
                _ => {}
            }
        }
    }

    /// The commands, in order, that bring a fresh solver to the recorded
    /// state, not counting the staged ones.
    pub(crate) fn commands(&mut self) -> Vec<u8> {
        self.thaw();
        self.levels.concat()
    }

    /// How many assertion levels the recorded state has above the base.
    #[cfg(test)]
    pub(crate) fn depth(&self) -> usize {
        self.levels.len() - 1
    }

    pub(crate) fn bytes(&self) -> usize {
        self.levels.iter().map(Vec::len).sum()
    }
}

/// The top-level s-expressions of SMT-LIB text, skipping comments and
/// whitespace; strings (`"..."`, with `""` inside) and quoted symbols
/// (`|...|`) are read whole.
fn top_level_forms(data: &[u8]) -> Vec<&[u8]> {
    let mut forms = Vec::new();
    let (mut depth, mut start, mut i) = (0usize, 0usize, 0usize);
    while i < data.len() {
        match data[i] {
            b';' => {
                while i < data.len() && data[i] != b'\n' {
                    i += 1;
                }
            }
            b'"' => {
                i += 1;
                while i < data.len() {
                    if data[i] == b'"' {
                        if data.get(i + 1) == Some(&b'"') {
                            i += 1;
                        } else {
                            break;
                        }
                    }
                    i += 1;
                }
            }
            b'|' => {
                i += 1;
                while i < data.len() && data[i] != b'|' {
                    i += 1;
                }
            }
            b'(' => {
                if depth == 0 {
                    start = i;
                }
                depth += 1;
            }
            b')' => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    forms.push(&data[start..=i]);
                }
            }
            _ => {}
        }
        i += 1;
    }
    forms
}

/// The command name of a top-level form: `assert` in `(assert ...)`.
fn form_head(form: &[u8]) -> &str {
    let inner = &form[1..];
    let start = inner.iter().position(|b| !b.is_ascii_whitespace()).unwrap_or(0);
    let end = inner[start..]
        .iter()
        .position(|b| b.is_ascii_whitespace() || *b == b'(' || *b == b')')
        .map_or(inner.len(), |n| start + n);
    std::str::from_utf8(&inner[start..end]).unwrap_or("")
}

/// The level count of `(push n)` / `(pop n)`, 1 when absent.
fn form_count(form: &[u8]) -> usize {
    let text = std::str::from_utf8(form).unwrap_or("");
    text.trim_matches(|c| c == '(' || c == ')')
        .split_whitespace()
        .nth(1)
        .and_then(|n| n.parse().ok())
        .unwrap_or(1)
}

impl Emitter {
    pub fn new(
        message_interface: std::sync::Arc<dyn crate::messages::MessageInterface>,
        use_pipe: bool,
        print_as_smt: bool,
        writer: Option<Box<dyn std::io::Write + Send>>,
        solver: SmtSolver,
    ) -> Self {
        let pipe_buffer = if use_pipe { Some(Vec::new()) } else { None };
        Emitter {
            printer: Printer::new(message_interface, print_as_smt, solver),
            node_writer: NodeWriter::new(),
            pipe_buffer,
            log: writer,
            current_indent: "".to_string(),
            replay: None,
        }
    }

    pub fn set_log(&mut self, writer: Option<Box<dyn std::io::Write + Send>>) {
        self.log = writer;
    }

    fn is_none(&self) -> bool {
        self.pipe_buffer.is_none() && self.log.is_none()
    }

    /// Return all the data in pipe_buffer, and reset pipe_buffer to Some empty vector
    pub fn take_pipe_data(&mut self) -> Vec<u8> {
        let data = self.pipe_buffer.take().expect("use_pipe must be set to true to take pipe");
        self.pipe_buffer = Some(Vec::new());
        // Everything taken is sent to the solver right away.
        if let Some(replay) = &mut self.replay {
            replay.stage(&data);
        }
        data
    }

    pub fn indent(&mut self) {
        if let Some(_) = self.log {
            self.current_indent = self.current_indent.clone() + " ";
        }
    }

    pub fn unindent(&mut self) {
        if let Some(_) = self.log {
            self.current_indent = self.current_indent[1..].to_string();
        }
    }

    pub fn blank_line(&mut self) {
        if let Some(w) = &mut self.log {
            writeln!(w, "").unwrap();
            w.flush().unwrap();
        }
    }

    pub fn comment(&mut self, s: &str) {
        if let Some(w) = &mut self.log {
            writeln!(w, "{};; {}", self.current_indent, s).unwrap();
            w.flush().unwrap();
        }
    }

    pub fn log_node(&mut self, node: &Node) {
        if let Some(w) = &mut self.pipe_buffer {
            writeln!(w, "{}", self.node_writer.node_to_string_indent(&self.current_indent, &node))
                .unwrap();
            w.flush().unwrap();
        }
        if let Some(w) = &mut self.log {
            writeln!(
                w,
                "{}{}",
                self.current_indent,
                self.node_writer.node_to_string_indent(&self.current_indent, &node)
            )
            .unwrap();
            w.flush().unwrap();
        }
    }

    pub fn log_set_option(&mut self, option: &str, value: &str) {
        if !self.is_none() {
            self.log_node(&node!(
                (set-option {Node::Atom(":".to_owned() + option)} {Node::Atom(value.to_string())})
            ));
        }
    }

    /// `(get-assertion-sources :tags-only)`: cvc5 replies with one tag list per
    /// preprocessed assertion (provenance mode only).
    pub fn log_get_assertion_sources(&mut self) {
        if !self.is_none() {
            self.log_node(&node!((get-assertion-sources {Node::Atom(":tags-only".to_string())})));
        }
    }

    /// `(get-egraph-equalities :limit n [:include-used] [:focus (t ...)])`:
    /// cvc5 replies with the equalities its e-graph holds after the last
    /// `check-sat`, in the classes of the focus terms, or of every term when
    /// there are none.
    pub fn log_get_egraph_equalities(&mut self, focus: &[Node], limit: u32, include_used: bool) {
        if !self.is_none() {
            let mut items = vec![
                Node::Atom("get-egraph-equalities".to_string()),
                Node::Atom(":limit".to_string()),
                Node::Atom(limit.to_string()),
            ];
            if include_used {
                items.push(Node::Atom(":include-used".to_string()));
            }
            if !focus.is_empty() {
                items.push(Node::Atom(":focus".to_string()));
                items.push(Node::List(focus.to_vec()));
            }
            self.log_node(&Node::List(items));
        }
    }

    /// `(save-instantiations k)`: cvc5 keeps the instantiations of the current
    /// scope under `k` after it pops.
    pub fn log_save_instantiations(&mut self, key: &str) {
        if !self.is_none() {
            self.log_node(&node!((save-instantiations {Node::Atom(key.to_string())})));
        }
    }

    /// `(restore-instantiations k [:only])`: cvc5 replays what `k` saved into
    /// the current scope, for each quantifier this scope asserts. With
    /// `:only` no other instantiation happens in that scope.
    pub fn log_restore_instantiations(&mut self, key: &str, only: bool) {
        if !self.is_none() {
            let mut items =
                vec![Node::Atom("restore-instantiations".to_string()), Node::Atom(key.to_string())];
            if only {
                items.push(Node::Atom(":only".to_string()));
            }
            self.log_node(&Node::List(items));
        }
    }

    /// `(get-instantiation-graph)`: cvc5 replies with the instantiations of
    /// the last `check-sat` and which earlier ones they matched terms of.
    pub fn log_get_instantiation_graph(&mut self) {
        if !self.is_none() {
            let command = Node::Atom("get-instantiation-graph".to_string());
            self.log_node(&Node::List(vec![command]));
        }
    }

    /// `(export-instantiations k)`: cvc5 replies with an
    /// `import-instantiations` command carrying what `k` saved.
    pub fn log_export_instantiations(&mut self, key: &str) {
        if !self.is_none() {
            self.log_node(&node!((export-instantiations {Node::Atom(key.to_string())})));
        }
    }

    /// `(import-instantiations k ...)`: a certificate another solver exported,
    /// already validated by `ImportInstantiations::parse`.
    pub fn log_import_instantiations(&mut self, certificate: &ImportInstantiations) {
        if !self.is_none() {
            self.log_node(&certificate.to_node());
        }
    }

    pub fn log_get_info(&mut self, param: &str) {
        if !self.is_none() {
            self.log_node(&node!(
                (get-info {Node::Atom(format!(":{}", param))})
            ));
        }
    }

    pub fn log_push(&mut self) {
        if !self.is_none() {
            self.log_node(&nodes!(push));
            self.indent();
        }
    }

    pub fn log_pop(&mut self) {
        if !self.is_none() {
            self.unindent();
            self.log_node(&nodes!(pop));
        }
    }

    /*
    pub fn log_function_decl(&mut self, x: &Ident, typs: &[Typ], typ: &Typ) {
        if let Some(_) = self.log {
            self.log_node(&function_decl_to_node(x, typs, typ));
        }
    }
    */

    pub fn log_decl(&mut self, decl: &Decl) {
        if !self.is_none() {
            self.log_node(&self.printer.decl_to_node(decl));
        }
    }

    /// `(assert e)`, or `(assert (! e :named n))`, `(assert (! e :assert-id t))`,
    /// `(assert (! e :named n :assert-id t))` when a name or a provenance tag
    /// is given.
    pub fn log_assert(
        &mut self,
        named: &Option<Ident>,
        tag: &Option<crate::def::ProvenanceTag>,
        expr: &Expr,
    ) {
        if !self.is_none() {
            if named.is_none() && tag.is_none() {
                self.log_node(&nodes!(assert {self.printer.expr_to_node(expr)}));
                return;
            }
            let mut annotated = vec![Node::Atom("!".to_string()), self.printer.expr_to_node(expr)];
            if let Some(named) = named {
                annotated.push(Node::Atom(":named".to_string()));
                annotated.push(Node::Atom((**named).clone()));
            }
            if let Some(tag) = tag {
                annotated.push(Node::Atom(":assert-id".to_string()));
                annotated.push(Node::Atom(tag.to_symbol()));
            }
            self.log_node(&nodes!(assert {Node::List(annotated)}));
        }
    }

    /// `(check-sat-assuming (l ...))`, each literal a boolean constant or its
    /// negation.
    pub fn log_check_sat_assuming(&mut self, literals: &[Expr]) {
        if !self.is_none() {
            let literals = literals.iter().map(|l| self.printer.expr_to_node(l)).collect();
            self.log_node(&Node::List(vec![
                Node::Atom("check-sat-assuming".to_string()),
                Node::List(literals),
            ]));
        }
    }

    pub fn log_word(&mut self, s: &str) {
        if !self.is_none() {
            self.log_node(&Node::List(vec![Node::Atom(s.to_string())]));
        }
    }

    pub fn log_query(&mut self, query: &Query) {
        if !self.is_none() {
            self.log_node(&self.printer.query_to_node(query));
        }
    }

    pub fn log_eval(&mut self, expr: Node) {
        if !self.is_none() {
            self.log_node(&nodes!(eval { expr }));
        }
    }
}

#[cfg(test)]
mod replay_tests {
    use super::Replay;

    #[test]
    fn a_replay_keeps_what_the_solver_holds_now() {
        let mut replay = Replay::new();
        replay.record(
            b"(set-logic ALL)\n; a comment (with parens\n(declare-fun f (Int) Int)\n(push 1)\n\
              (assert (= (f 0) 1))\n(check-sat)\n(get-info :reason-unknown)\n",
        );
        replay.record(b"(push 2)\n(declare-const |a b)| Int)(assert (> x \"y)\"\"\"))(set-option :rlimit 7)\n");
        assert_eq!(replay.depth(), 3);
        assert_eq!(
            String::from_utf8(replay.commands()).unwrap(),
            "(set-logic ALL)\n(declare-fun f (Int) Int)\n(set-option :rlimit 7)\n(push 1)\n\
             (assert (= (f 0) 1))\n(push 1)\n(push 1)\n(declare-const |a b)| Int)\n\
             (assert (> x \"y)\"\"\"))\n"
        );
        // A pop drops what its level added; options stay, since they are global.
        replay.record(b"(pop 1)(echo \"<<DONE>>\")");
        assert_eq!(replay.depth(), 2);
        assert_eq!(
            String::from_utf8(replay.commands()).unwrap(),
            "(set-logic ALL)\n(declare-fun f (Int) Int)\n(set-option :rlimit 7)\n(push 1)\n\
             (assert (= (f 0) 1))\n(push 1)\n"
        );
        replay.record(b"(pop 2)");
        assert_eq!(replay.depth(), 0);
        assert_eq!(
            String::from_utf8(replay.commands()).unwrap(),
            "(set-logic ALL)\n(declare-fun f (Int) Int)\n(set-option :rlimit 7)\n"
        );
    }

    /// What was taken from the pipe last may not have reached a solver yet:
    /// it is left out of the replay until the next take or a stop commits it.
    #[test]
    fn staged_commands_are_left_out_until_committed() {
        let mut replay = Replay::new();
        replay.stage(b"(declare-fun f () Int)(push)");
        replay.stage(b"(assert (= f 1))(pop)");
        assert_eq!(
            String::from_utf8(replay.commands()).unwrap(),
            "(declare-fun f () Int)\n(push 1)\n"
        );
        replay.commit();
        assert_eq!(String::from_utf8(replay.commands()).unwrap(), "(declare-fun f () Int)\n");
    }

    /// A stopped solver's record is kept deflated and reads back the same.
    #[test]
    fn a_frozen_replay_reads_back_the_same() {
        let mut replay = Replay::new();
        replay.record(b"(declare-fun f () Int)(push 1)(assert (= f 1))");
        let before = replay.commands();
        let size = replay.bytes();
        replay.freeze();
        assert!(replay.bytes() > 0);
        assert_eq!(replay.commands(), before);
        replay.freeze();
        replay.record(b"(pop 1)");
        assert_eq!(String::from_utf8(replay.commands()).unwrap(), "(declare-fun f () Int)\n");
        assert!(replay.bytes() < size);
    }
}
