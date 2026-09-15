//! Speculative probes (cvc5 only): a hypothesis about quantifier
//! instantiation, held in one query's scope, and what cvc5 reported it did.
//!
//! A probe is an ordinary check of a query with one `(speculate ...)` command
//! sent in the query's own scope, just before its first `check-sat`, and
//! `(get-info :speculation)` read right after it. `finish_query` pops the
//! scope, and cvc5 keeps every hypothesis and everything it installed in
//! that scope's user context, so nothing of the probe outlives the check.
//!
//! The terms of a hypothesis are sent as strings, which cvc5 parses one at a
//! time: a term that names a symbol the scope does not declare fails the
//! command with an error, before any `check-sat`, instead of ending the
//! solver as a bad term elsewhere in the stream would.

use crate::ast::{BindX, Decl, DeclX, Expr, ExprX, Quant, Query};
use crate::context::VariableVersions;
use crate::printer::Printer;
use sise::TreeNode as Node;
use std::collections::HashMap;

/// What a probe adds to its query's scope.
#[derive(Clone, Debug)]
pub enum Hypothesis {
    /// Nothing: the check is observed for matching loops.
    Observe,
    /// Instantiate the quantifiers named `qid` once, with a term, in the
    /// solver's spelling, for each variable, by its name on the wire.
    Instantiate { qid: String, subst: Vec<(String, String)> },
    /// Match the quantifiers named `qid` with one more trigger, whose terms
    /// are over the variables `vars` (name and sort, as on the wire).
    Trigger { qid: String, vars: Vec<(String, Node)>, pattern: Vec<String> },
    /// Refuse the instantiations of the quantifiers named `qid` whose terms,
    /// or trigger instance, match `fingerprint` (holes `_`, `_<n>`, `#<n>`).
    Block { qid: String, fingerprint: String },
}

#[derive(Clone, Debug)]
pub struct SpeculationRequest {
    pub hypothesis: Hypothesis,
    /// The depth rises that make a matching loop; cvc5's default when `None`.
    pub loop_threshold: Option<u32>,
}

/// A string literal cvc5 reads back as `text`: quoted, `"` doubled. Line
/// breaks become spaces, so the command stays on one line.
fn string_atom(text: &str) -> Node {
    let flat: String = text.chars().map(|c| if c.is_whitespace() { ' ' } else { c }).collect();
    Node::Atom(format!("\"{}\"", flat.replace('"', "\"\"")))
}

fn atom(text: &str) -> Node {
    Node::Atom(text.to_string())
}

impl SpeculationRequest {
    /// The `(speculate ...)` command for this request.
    pub(crate) fn to_node(&self) -> Node {
        let mut items = vec![atom("speculate")];
        match &self.hypothesis {
            Hypothesis::Observe => items.push(atom(":observe")),
            Hypothesis::Instantiate { qid, subst } => {
                items.extend([atom(":instantiate"), atom(qid)]);
                items.push(Node::List(
                    subst
                        .iter()
                        .map(|(name, term)| Node::List(vec![atom(name), string_atom(term)]))
                        .collect(),
                ));
            }
            Hypothesis::Trigger { qid, vars, pattern } => {
                items.extend([atom(":trigger"), atom(qid)]);
                items.push(Node::List(
                    vars.iter()
                        .map(|(name, sort)| Node::List(vec![atom(name), sort.clone()]))
                        .collect(),
                ));
                items.push(Node::List(pattern.iter().map(|p| string_atom(p)).collect()));
            }
            Hypothesis::Block { qid, fingerprint } => {
                items.extend([atom(":block"), atom(qid), string_atom(fingerprint)]);
            }
        }
        if let Some(threshold) = self.loop_threshold {
            items.extend([atom(":loop-threshold"), atom(&threshold.to_string())]);
        }
        Node::List(items)
    }
}

/// What cvc5 reported a hypothesis did, from `(get-info :speculation)`.
#[derive(Clone, Debug, Default)]
pub struct HypothesisReport {
    /// `observe`, `instantiate`, `trigger` or `block`
    pub kind: String,
    pub qid: String,
    /// `applied`, `rejected` (the instantiation funnel refused the directed
    /// instance: it was made already, it is a lemma already sent, it
    /// simplifies to true, or the instantiation level limit refused a term),
    /// `mismatch` (the variables do not fit), `unusable` (the pattern cannot
    /// be a trigger), `no-quantifier` (applied, but no asserted formula has
    /// the qid) or `pending` (no instantiation round reached e-matching, for
    /// instance because conflict-based instantiation closed every check
    /// first)
    pub status: String,
    pub reason: Option<String>,
    /// how many asserted quantifiers have the qid
    pub quantifiers: u64,
    /// instantiations it made, and directed ones the funnel refused
    pub added: u64,
    pub rejected: u64,
    /// instantiations a block refused
    pub blocked: u64,
    /// term vectors it made, or refused for a block, the first few
    pub instances: Vec<Vec<String>>,
    /// the instances' bodies (instantiate)
    pub bodies: Vec<String>,
    /// the pattern over the quantifier's variables (trigger)
    pub pattern: Vec<String>,
    /// the quantifier with the pattern as its only one (trigger)
    pub materialized: Vec<String>,
    pub fingerprint: Option<String>,
}

/// A quantifier whose instantiating terms kept getting deeper, round after
/// round, in the probed check.
#[derive(Clone, Debug, Default)]
pub struct LoopReport {
    pub qid: String,
    pub instantiations: u64,
    /// of them directed by the hypothesis
    pub directed: u64,
    pub rounds: u64,
    /// rounds in which its deepest instantiating term got deeper than before
    pub rises: u64,
    pub first_depth: u64,
    pub max_depth: u64,
    pub first_round: u64,
    pub last_round: u64,
}

/// cvc5's reply to `(get-info :speculation)` after a probe's `check-sat`, or
/// its refusal of the `(speculate ...)` command.
#[derive(Clone, Debug, Default)]
pub struct SpeculationReply {
    pub active: bool,
    /// instantiation rounds the check ran
    pub rounds: u64,
    pub loop_threshold: u64,
    pub hypotheses: Vec<HypothesisReport>,
    pub loops: Vec<LoopReport>,
    /// The solver's refusal of the command, `(error "...")`, when it could
    /// not read a term or the fingerprint. The query was not checked.
    pub error: Option<String>,
    /// The reply, when it did not parse.
    pub unparsed: Option<String>,
    /// SSA symbol -> original AIR variable and assignment version, recorded by lowering.
    pub variable_versions: VariableVersions,
}

/// The contents of a string literal cvc5 printed: unquoted, `""` read as `"`.
fn unquote(text: &str) -> String {
    match text.strip_prefix('"').and_then(|t| t.strip_suffix('"')) {
        Some(inner) => inner.replace("\"\"", "\""),
        None => text.to_string(),
    }
}

/// A string or symbol value of a reply, as its text: `sexp_text` would put
/// one holding a space back between bars.
fn text(node: &Node) -> String {
    match node {
        Node::Atom(atom) => unquote(atom),
        Node::List(_) => crate::smt_verify::sexp_text(node),
    }
}

fn terms(node: &Node) -> Option<Vec<String>> {
    match node {
        Node::List(items) => Some(items.iter().map(crate::smt_verify::sexp_text).collect()),
        Node::Atom(_) => None,
    }
}

fn vectors(node: &Node) -> Option<Vec<Vec<String>>> {
    match node {
        Node::List(items) => items.iter().map(terms).collect(),
        Node::Atom(_) => None,
    }
}

fn count(node: &Node) -> Option<u64> {
    match node {
        Node::Atom(a) => crate::smt_verify::difficulty_count(a),
        Node::List(_) => None,
    }
}

fn parse_hypothesis(node: &Node) -> Option<HypothesisReport> {
    let Node::List(items) = node else { return None };
    let (Node::Atom(kind), fields) = items.split_first()? else { return None };
    let mut h = HypothesisReport { kind: kind.clone(), ..Default::default() };
    for pair in fields.chunks(2) {
        let [Node::Atom(key), value] = pair else { return None };
        match key.as_str() {
            ":qid" => h.qid = text(value),
            ":status" => h.status = text(value),
            ":reason" => h.reason = Some(text(value)),
            ":fingerprint" => h.fingerprint = Some(text(value)),
            ":quantifiers" => h.quantifiers = count(value)?,
            ":added" => h.added = count(value)?,
            ":rejected" => h.rejected = count(value)?,
            ":blocked" => h.blocked = count(value)?,
            ":instances" | ":examples" => h.instances = vectors(value)?,
            ":bodies" => h.bodies = terms(value)?,
            ":pattern" => h.pattern = terms(value)?,
            ":materialized" => h.materialized = terms(value)?,
            _ => {}
        }
    }
    Some(h)
}

fn parse_loop(node: &Node) -> Option<LoopReport> {
    let Node::List(items) = node else { return None };
    let (Node::Atom(head), fields) = items.split_first()? else { return None };
    if head != "loop" {
        return None;
    }
    let mut l = LoopReport::default();
    for pair in fields.chunks(2) {
        let [Node::Atom(key), value] = pair else { return None };
        match key.as_str() {
            ":qid" => l.qid = text(value),
            ":instantiations" => l.instantiations = count(value)?,
            ":directed" => l.directed = count(value)?,
            ":rounds" => l.rounds = count(value)?,
            ":rises" => l.rises = count(value)?,
            ":first-depth" => l.first_depth = count(value)?,
            ":max-depth" => l.max_depth = count(value)?,
            ":first-round" => l.first_round = count(value)?,
            ":last-round" => l.last_round = count(value)?,
            _ => {}
        }
    }
    Some(l)
}

/// Parse `(:speculation (:active B :rounds N :loop-threshold N :hypotheses
/// (H ...) :loops (L ...)))`. A reply that does not parse is kept whole in
/// `unparsed`.
pub(crate) fn parse_speculation(line: &str) -> SpeculationReply {
    let mut out = SpeculationReply::default();
    let text = crate::smt_verify::bar_symbols_as_strings(line);
    let mut parser = sise::Parser::new(&text);
    let parsed = (|| {
        let Ok(Node::List(items)) = sise::parse_tree(&mut parser) else { return None };
        let [Node::Atom(head), Node::List(fields)] = &items[..] else { return None };
        if head != ":speculation" {
            return None;
        }
        for pair in fields.chunks(2) {
            let [Node::Atom(key), value] = pair else { return None };
            match (key.as_str(), value) {
                (":active", Node::Atom(v)) => out.active = v == "true",
                (":rounds", v) => out.rounds = count(v)?,
                (":loop-threshold", v) => out.loop_threshold = count(v)?,
                (":hypotheses", Node::List(hs)) => {
                    out.hypotheses = hs.iter().map(parse_hypothesis).collect::<Option<_>>()?
                }
                (":loops", Node::List(ls)) => {
                    out.loops = ls.iter().map(parse_loop).collect::<Option<_>>()?
                }
                _ => {}
            }
        }
        Some(())
    })();
    if parsed.is_none() {
        out = SpeculationReply { unparsed: Some(line.to_string()), ..Default::default() };
    }
    out
}

/// A quantifier a query's scope asserts, as the solver is sent it.
#[derive(Clone, Debug)]
pub struct QuantifierSmt {
    pub qid: String,
    /// Each variable's name and sort.
    pub binders: Vec<(String, Node)>,
    /// Each trigger, as its terms.
    pub triggers: Vec<Vec<Node>>,
    /// The body, without the trigger and qid attributes.
    pub body: Node,
    /// Whether the query itself, rather than a declaration before it,
    /// asserts it.
    pub in_query: bool,
}

impl QuantifierSmt {
    /// The body with each variable in `subst` replaced by its term.
    pub fn instance(&self, subst: &HashMap<String, Node>) -> Node {
        substitute(&self.body, subst)
    }

    /// Each trigger with each variable in `subst` replaced by its term.
    pub fn trigger_instances(&self, subst: &HashMap<String, Node>) -> Vec<Vec<Node>> {
        self.triggers
            .iter()
            .map(|trigger| trigger.iter().map(|term| substitute(term, subst)).collect())
            .collect()
    }
}

/// The names a binder list `((x T) ...)` binds.
fn bound_names(binders: &Node) -> Vec<String> {
    match binders {
        Node::List(items) => items
            .iter()
            .filter_map(|b| match b {
                Node::List(pair) => match pair.first() {
                    Some(Node::Atom(name)) => Some(name.clone()),
                    _ => None,
                },
                _ => None,
            })
            .collect(),
        Node::Atom(_) => Vec::new(),
    }
}

/// `node` with each free occurrence of a name in `subst` replaced by its
/// term. A binder (`forall`, `exists`, `lambda`, `choose`, `let`) shadows the
/// names it binds within its scope.
pub fn substitute(node: &Node, subst: &HashMap<String, Node>) -> Node {
    match node {
        Node::Atom(a) => subst.get(a).cloned().unwrap_or_else(|| node.clone()),
        Node::List(items) => {
            if let [Node::Atom(head), binders, rest @ ..] = &items[..] {
                let quantifier = matches!(head.as_str(), "forall" | "exists" | "lambda" | "choose");
                if quantifier || head == "let" {
                    let shadowed = bound_names(binders);
                    let inner: HashMap<String, Node> = subst
                        .iter()
                        .filter(|(name, _)| !shadowed.contains(name))
                        .map(|(name, term)| (name.clone(), term.clone()))
                        .collect();
                    // a let's bound terms see the outer names
                    let binders = match (head.as_str(), binders) {
                        ("let", Node::List(pairs)) => Node::List(
                            pairs
                                .iter()
                                .map(|pair| match pair {
                                    Node::List(p) if p.len() == 2 => {
                                        Node::List(vec![p[0].clone(), substitute(&p[1], subst)])
                                    }
                                    other => other.clone(),
                                })
                                .collect(),
                        ),
                        _ => binders.clone(),
                    };
                    let mut out = vec![items[0].clone(), binders];
                    out.extend(rest.iter().map(|n| substitute(n, &inner)));
                    return Node::List(out);
                }
            }
            Node::List(items.iter().map(|n| substitute(n, subst)).collect())
        }
    }
}

/// Every universal quantifier under `expr` with a qid, in the order met.
fn quantifiers_in(expr: &Expr, found: &mut Vec<Expr>) {
    let expr = crate::smt_verify::elim_zero_args_expr(expr);
    crate::visitor::map_expr_visitor(&expr, &mut |e| {
        if let ExprX::Bind(bind, _) = &**e {
            if let BindX::Quant(Quant::Forall, _, _, Some(_)) = &**bind {
                found.push(e.clone());
            }
        }
        e.clone()
    });
}

/// The universal quantifiers with a qid that `decls` and `query` assert,
/// the query's own first, then the declarations' from the last: each with
/// whether the query asserts it.
fn all_quantifiers<'a>(decls: impl Iterator<Item = &'a Decl>, query: &Query) -> Vec<(Expr, bool)> {
    let mut declared = Vec::new();
    for decl in decls {
        if let DeclX::Axiom(axiom) = &**decl {
            quantifiers_in(&axiom.expr, &mut declared);
        }
    }
    let mut own = Vec::new();
    for decl in query.local.iter() {
        if let DeclX::Axiom(axiom) = &**decl {
            quantifiers_in(&axiom.expr, &mut own);
        }
    }
    crate::visitor::map_stmt_expr_visitor(&query.assertion, &mut |e| {
        quantifiers_in(e, &mut own);
        e.clone()
    });
    let own = own.into_iter().rev().map(|e| (e, true));
    own.chain(declared.into_iter().rev().map(|e| (e, false))).collect()
}

fn qid_of(expr: &Expr) -> Option<&str> {
    match &**expr {
        ExprX::Bind(bind, _) => match &**bind {
            BindX::Quant(_, _, _, Some(qid)) => Some(qid.as_str()),
            _ => None,
        },
        _ => None,
    }
}

fn describe(expr: &Expr, in_query: bool, printer: &Printer) -> Option<QuantifierSmt> {
    let ExprX::Bind(bind, body) = &**expr else { return None };
    let BindX::Quant(Quant::Forall, binders, triggers, Some(qid)) = &**bind else { return None };
    Some(QuantifierSmt {
        qid: qid.to_string(),
        binders: binders.iter().map(|b| (b.name.to_string(), printer.typ_to_node(&b.a))).collect(),
        triggers: triggers
            .iter()
            .map(|t| t.iter().map(|term| printer.expr_to_node(term)).collect())
            .collect(),
        body: printer.expr_to_node(body),
        in_query,
    })
}

/// The quantifier named `qid` that `decls` or `query` asserts, preferring
/// the query's own. `None` if neither does.
pub(crate) fn find_quantifier<'a>(
    decls: impl Iterator<Item = &'a Decl>,
    query: &Query,
    qid: &str,
    printer: &Printer,
) -> Option<QuantifierSmt> {
    all_quantifiers(decls, query)
        .iter()
        .find(|(e, _)| qid_of(e) == Some(qid))
        .and_then(|(e, in_query)| describe(e, *in_query, printer))
}

/// The universal quantifiers `decls` and `query` assert that `keep` accepts
/// by qid and whether the query asserts them: the query's own first, each
/// qid once.
pub(crate) fn quantifiers<'a>(
    decls: impl Iterator<Item = &'a Decl>,
    query: &Query,
    printer: &Printer,
    keep: impl Fn(&str, bool) -> bool,
) -> Vec<QuantifierSmt> {
    let mut seen = std::collections::HashSet::new();
    all_quantifiers(decls, query)
        .iter()
        .filter(|(e, in_query)| {
            qid_of(e).is_some_and(|qid| keep(qid, *in_query) && seen.insert(qid.to_string()))
        })
        .filter_map(|(e, in_query)| describe(e, *in_query, printer))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tree(text: &str) -> Node {
        sise::parse_tree(&mut sise::Parser::new(text)).unwrap()
    }

    #[test]
    fn requests_send_terms_as_strings() {
        let request = SpeculationRequest {
            hypothesis: Hypothesis::Instantiate {
                qid: "user_f_1".into(),
                subst: vec![("x$".into(), "(f \"a\"\nb)".into())],
            },
            loop_threshold: Some(3),
        };
        let printer = crate::printer::node_to_string;
        assert_eq!(
            printer(&request.to_node()),
            r#"(speculate :instantiate user_f_1 ((x$ "(f ""a"" b)")) :loop-threshold 3)"#
        );
        let trigger = SpeculationRequest {
            hypothesis: Hypothesis::Trigger {
                qid: "q".into(),
                vars: vec![("i".into(), tree("Int"))],
                pattern: vec!["(f i)".into()],
            },
            loop_threshold: None,
        };
        assert_eq!(printer(&trigger.to_node()), r#"(speculate :trigger q ((i Int)) ("(f i)"))"#);
    }

    #[test]
    fn replies_parse_hypotheses_and_loops() {
        let reply = parse_speculation(
            r#"(:speculation (:active true :rounds 4 :loop-threshold 5 :hypotheses ((observe) (instantiate :qid ax_f :status mismatch :reason "no term for ""i""" :quantifiers 1 :added 0 :rejected 0 :instances ((a (g b))) :bodies ((not (<= (f a) 0))))) :loops ((loop :qid |a b| :instantiations 9 :directed 1 :rounds 6 :rises 5 :first-depth 1 :max-depth 6 :first-round 1 :last-round 6))))"#,
        );
        assert!(reply.unparsed.is_none(), "{:?}", reply);
        assert!(reply.active);
        assert_eq!((reply.rounds, reply.loop_threshold), (4, 5));
        assert_eq!(reply.hypotheses.len(), 2);
        assert_eq!(reply.hypotheses[0].kind, "observe");
        let h = &reply.hypotheses[1];
        assert_eq!(
            (h.kind.as_str(), h.qid.as_str(), h.status.as_str()),
            ("instantiate", "ax_f", "mismatch")
        );
        assert_eq!(h.reason.as_deref(), Some("no term for \"i\""));
        assert_eq!(h.instances, vec![vec!["a".to_string(), "(g b)".to_string()]]);
        assert_eq!(h.bodies, vec!["(not (<= (f a) 0))".to_string()]);
        assert_eq!(reply.loops.len(), 1);
        assert_eq!((reply.loops[0].qid.as_str(), reply.loops[0].rises), ("a b", 5));
        let bad = parse_speculation("(:speculation (:rounds x))");
        assert!(bad.unparsed.is_some());
    }

    #[test]
    fn substitution_respects_binders() {
        let subst = HashMap::from([("x".to_string(), tree("(g a)"))]);
        let substituted = substitute(
            &tree("(and (f x) (forall ((x Int)) (f x)) (let ((y x) (x 1)) (h x y)))"),
            &subst,
        );
        assert_eq!(
            substituted,
            tree("(and (f (g a)) (forall ((x Int)) (f x)) (let ((y (g a)) (x 1)) (h x y)))")
        );
    }
}
