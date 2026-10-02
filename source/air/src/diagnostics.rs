//! What cvc5 can say about a check that did not prove its query, read right
//! after the check and before anything else reaches the solver.
//!
//! Every reading here leaves the search alone: the `get-info` keys only read
//! counters and records the check already kept, and the e-graph is read
//! after the check. They are asked only when a check fails (`sat` or
//! `unknown`), so a proof that goes through pays nothing for them. Terms
//! and `:qid`s are the solver's spelling; Verus joins them back to source.
//!
//! The keys are answered by the Basis cvc5 fork that Verus verifies with
//! (see `source/tools/get-cvc5.sh`). A cvc5 without a key answers
//! `unsupported`, which is kept rather than failed on.

use crate::ast::{BinaryOp, BindX, Expr, ExprX, Ident, MultiOp, UnaryOp};
use crate::def::{GLOBAL_PREFIX_LABEL, PREFIX_LABEL};
use std::collections::HashMap;

/// Everything read about one failed check. Each part is `None` when it was
/// not asked for, which depends on how the check failed.
#[derive(Debug, Clone, Default)]
pub struct FailureDiagnostics {
    /// `sat` or `unknown`, as the check answered.
    pub result: String,
    /// SSA symbol -> original AIR variable and assignment version, recorded
    /// when the query was lowered, so solver terms read as source variables.
    pub variable_versions: VariableVersions,
    /// Why an `unknown` answer was given (`unknown` only).
    pub unknown_reason: Option<UnknownReason>,
    /// What the check spent.
    pub check_effort: Option<CheckEffort>,
    /// How often each quantifier was instantiated.
    pub inst_pressure: Option<InstPressure>,
    /// The nonlinear terms the solver could not reconcile with their
    /// arguments.
    pub nl_frontier: Option<NlFrontier>,
    /// The quantifiers whose instantiations fed themselves (`unknown` only).
    pub matching_loops: Option<MatchingLoopsInfo>,
    /// The equalities the solver held between the query's own terms.
    pub egraph: Option<EgraphReply>,
    /// Quantifiers whose instances made each other's triggers, from the
    /// instantiation graph (`unknown` only).
    pub inst_cycles: Option<InstCycles>,
}

/// The cycles among quantifiers in cvc5's `(get-instantiation-graph)`: an
/// edge runs from a quantifier to another when an instance of the first
/// introduced a term an instance of the second matched. Folded to
/// quantifiers as it is read, so the per-instance graph is never kept.
#[derive(Debug, Clone, Default)]
pub struct InstCycles {
    /// Most repetitions first.
    pub cycles: Vec<InstCycle>,
    /// Instantiations in the graph, and those cvc5 did not record.
    pub instantiations: u64,
    pub dropped: u64,
    /// The reply, when it did not parse.
    pub unparsed: Option<String>,
}

/// One strongly connected set of quantifiers.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct InstCycle {
    /// The quantifiers' `:qid`s, sorted.
    pub qids: Vec<String>,
    /// Instance-to-instance edges among them.
    pub repetitions: u64,
    /// Their instantiations.
    pub instantiations: u64,
}

pub type VariableVersions = HashMap<String, (String, u32)>;

/// Why a `check-sat` answered `unknown`, as the solver reported it. The join
/// of the culprit `:qid`s back to source happens in Verus.
#[derive(Debug, Clone, Default)]
pub struct UnknownReason {
    /// The `(get-info :reason-unknown)` answer, unquoted: `incomplete`,
    /// `resourceout`, `timeout`, ...
    pub reason: String,
    /// cvc5's own classification of an incomplete answer, the `IncompleteId`
    /// behind `(get-info :incomplete-id)`: `QUANTIFIERS`, `ARITH_NL`,
    /// `QUANTIFIERS_MAX_INST_ROUNDS`, ... `None` when the answer was not
    /// incomplete or the solver cannot say.
    pub incomplete_id: Option<String>,
    /// The `:qid`s of `(get-info :incomplete-culprits)`: the asserted
    /// quantifiers no strategy claimed to have fully processed. Candidates,
    /// not a verdict: when the solver gave up for a global reason (the
    /// instantiation round limit, a module's own check) there are none.
    pub culprit_qids: Vec<String>,
}

/// What cvc5's `(get-info :nl-frontier)` reported for one `check-sat`: the nonlinear terms whose value in the linear model
/// the nonlinear extension could not reconcile with their arguments' values,
/// and where each entered the problem. Terms and tags are the solver's
/// spelling; the join back to source happens in Verus.
#[derive(Debug, Clone, Default)]
pub struct NlFrontier {
    /// `unsat`, `sat` or `unknown` as cvc5 answered; `none` before a check.
    pub result: String,
    /// The unknown explanation in lower case (`incomplete`, `resourceout`,
    /// ...), `none` unless `unknown`.
    pub reason: String,
    /// Whether cvc5's nonlinear extension was on.
    pub enabled: bool,
    /// Model-based refinement runs, runs with an assertion false in the
    /// candidate model, and runs that gave up (no lemma, model unverified).
    pub checks: u64,
    pub rounds: u64,
    pub punts: u64,
    /// How the most recent run ended: `none`, `sat`, `lemma` or `punt`.
    pub last: String,
    /// Most recent round's atoms first, then by rounds wrong.
    pub atoms: Vec<NlAtom>,
    /// Atoms left out of `atoms`.
    pub omitted: u64,
    /// Whether the search for hosts in instantiations stopped early.
    pub truncated: bool,
    /// The reply, when it did not parse.
    pub unparsed: Option<String>,
}

/// What cvc5 reported for `(get-info :matching-loops)` after a `check-sat`
/// answered unknown: the quantifiers whose
/// instantiations fed themselves, symbols and SMT terms not yet joined to
/// source. The fields mirror the reply (see cvc5's
/// `theory/quantifiers/matching_loops.h`).
#[derive(Debug, Clone, Default)]
pub struct MatchingLoopsInfo {
    /// The last instantiation round of the check
    pub rounds: u64,
    /// Instantiations recorded, and those past cvc5's recording cap
    pub instantiations: u64,
    pub dropped: u64,
    /// Whether the instantiation round limit stopped the check
    pub max_inst_rounds: bool,
    pub loops: Vec<MatchingLoop>,
    /// Reply parts the parser did not recognise, kept rather than failed on.
    pub unparsed: Vec<String>,
}

/// One self-feeding quantifier, as cvc5 reported it. Terms are SMT text.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct MatchingLoop {
    pub qid: String,
    /// high (the round limit cut the loop off while it climbed), medium, low
    pub confidence: String,
    /// linear-depth, exponential-fanout, or bounded
    pub growth: String,
    /// whether the chain follows instantiations that matched a term the
    /// previous rung introduced, rather than the deepest one of each round
    pub edges_confirmed: bool,
    /// whether consecutive rungs generalise to one shape
    pub stable: bool,
    pub instantiations: u64,
    pub rounds: u64,
    pub first_round: u64,
    pub last_round: u64,
    pub chain: u64,
    pub self_fed: u64,
    pub depth_per_rung: f64,
    pub depth_per_round: f64,
    pub fanout_per_round: f64,
    /// growth per step of the quantifier's own rounds: a loop that fires
    /// every other round doubles per step while `fanout_per_round` reads 1.41
    pub fanout_per_step: f64,
    /// qids of the other quantifiers a step passed through
    pub via: Vec<String>,
    /// the trigger whose matches formed the rungs, one term per trigger term
    pub trigger: Vec<String>,
    /// what each rung wraps around the previous one's growing subterm,
    /// generalised over the chain, `_0` marking that subterm; one per class
    /// when the loop climbs several subterms (`(r _0)`, `(l _0)`), and empty
    /// when the rungs do not grow into each other
    pub context: Vec<String>,
    /// the generalisation of every rung, and of every rung after the first
    pub shape: Vec<String>,
    pub step: Vec<String>,
    /// the first rungs and the last, each the trigger instantiated
    pub ladder: Vec<Vec<String>>,
    pub ladder_length: u64,
    /// instantiations of the quantifier per round, the last rounds
    pub per_round: Vec<u64>,
}

/// One equality from `(get-egraph-equalities)`, its terms as cvc5 printed
/// them. The same solver can parse them back in the same query's scope.
#[derive(Debug, Clone)]
pub struct EgraphEquality {
    pub lhs: String,
    pub rhs: String,
    /// `entailed` (every literal of the explanation holds at decision level 0
    /// in the query's scope), `decision`, or `unknown`
    pub level: String,
    /// whether some quantifier was instantiated with either side
    pub used: bool,
    /// the `:qid`s of those quantifiers
    pub used_by: Vec<String>,
    /// how many of the two sides are subterms of the query, 0 to 2
    pub focus: u32,
    /// the literals the equality follows from, except those cvc5 left out
    pub because: Vec<String>,
    /// how many literals of the explanation cvc5 left out, as naming a
    /// skolem or printing larger than its size limit; when not 0, `because`
    /// alone does not imply the equality
    pub because_hidden: u64,
}

/// cvc5's reply to `(get-egraph-equalities)` after a failed `check-sat`,
/// with what it counted.
#[derive(Debug, Clone, Default)]
pub struct EgraphReply {
    pub equalities: Vec<EgraphEquality>,
    /// classes listed
    pub classes: u64,
    /// equalities before the limit
    pub candidates: u64,
    /// focus terms sent, and how many of them the e-graph holds
    pub focus: u64,
    pub focus_found: u64,
    /// equalities left out because a quantifier was instantiated with a side
    pub used_omitted: u64,
    /// terms left out because they print larger than cvc5's size limit
    pub too_large: u64,
    /// The solver's refusal, as after `unsat`, where there is no e-graph to
    /// read, or a reply this parser did not recognise.
    pub error: Option<String>,
}

/// What cvc5's `(get-info :inst-pressure)` reported for one `check-sat`: per quantifier, by `:qid`, how often it was
/// instantiated and how often an attempt was rejected as a duplicate. The
/// join back to source happens in Verus.
#[derive(Debug, Clone, Default)]
pub struct InstPressure {
    /// Instantiation rounds that sent lemmas.
    pub rounds: u64,
    /// Whether each row says how many of its instances the refutation used.
    /// Only after `unsat` with proofs on, so not in an ordinary run.
    pub refutation: bool,
    /// Most instantiated first.
    pub quantifiers: Vec<QuantPressure>,
    /// The reply, when it did not parse.
    pub unparsed: Option<String>,
}

/// What cvc5's `(get-info :check-effort)` reported for one `check-sat`: the
/// resource units it spent, in the units of `rlimit-per` and so of a
/// query's rlimit budget, the instantiations it added and the
/// instantiation rounds that sent lemmas.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CheckEffort {
    pub resource_units: u64,
    pub instantiations: u64,
    pub inst_rounds: u64,
    /// The reply, when it did not parse, such as `unsupported` from a cvc5
    /// without the key.
    pub unparsed: Option<String>,
}

/// One nonlinear term of `(get-info :nl-frontier)`.
#[derive(Debug, Clone, Default)]
pub struct NlAtom {
    /// The term as the input spelled it, e.g. `(* x y)`.
    pub atom: String,
    /// product, power, division, iand, pow2 or transcendental
    pub kind: String,
    /// Whether it was wrong in the most recent refinement round.
    pub current: bool,
    /// In how many rounds it was wrong.
    pub rounds: u64,
    /// Its value in the linear model, and the value its arguments give it
    /// (they differ: that is why it is on the frontier). Each is a rational
    /// as cvc5 prints it (`-5`, `1/2`), or `none`.
    pub value: String,
    pub from_args: String,
    /// The bounds asserted on the atom itself.
    pub lower: Option<NlBound>,
    pub upper: Option<NlBound>,
    /// Its distinct arguments with their values and asserted bounds.
    pub args: Vec<NlTerm>,
    /// Where it entered the problem.
    pub hosts: Vec<NlHost>,
}

/// A term with its model value and asserted bounds.
#[derive(Debug, Clone, Default)]
pub struct NlTerm {
    pub term: String,
    pub value: String,
    pub lower: Option<NlBound>,
    pub upper: Option<NlBound>,
}

/// A constant bound read off an asserted literal.
#[derive(Debug, Clone, Default)]
pub struct NlBound {
    /// A rational as cvc5 prints it, e.g. `5`, `-5` or `1/2`.
    pub value: String,
    pub strict: bool,
    /// Whether the literal is implied by the assertions (fixed at SAT level
    /// 0), rather than holding only in the branch the solver explored.
    pub fixed: bool,
}

/// A term that applies one function to exactly an atom's factors: in a
/// tagged input assertion, or in the instantiations of one quantifier.
#[derive(Debug, Clone, Default)]
pub struct NlHost {
    /// `true` for an input assertion, `false` for an instantiation.
    pub input: bool,
    pub term: String,
    /// Input hosts: the tags of the assertions holding the term.
    pub tags: Vec<String>,
    /// Instantiation hosts: the quantifier's `:qid`, and how many vectors.
    pub qid: Option<String>,
    pub count: u64,
}

/// One quantifier's row of `(get-info :inst-pressure)`. Counts are the
/// solver's own, disaggregated: every attempt that reached the duplicate
/// checks is counted once, as added or as one kind of duplicate.
#[derive(Debug, Clone, Default)]
pub struct QuantPressure {
    /// The `:qid`, or a synthetic `quant_<n>` when `named` is false.
    pub qid: String,
    pub named: bool,
    pub instantiations: u64,
    /// Rejected: the same term vector was used before.
    pub duplicate_eq: u64,
    /// Rejected: the instance was already entailed.
    pub duplicate_ent: u64,
    /// Rejected: the same lemma was already sent.
    pub duplicate_lemma: u64,
    /// Instances made because they conflicted with, or propagated in, the
    /// current assignment (conflict-based instantiation).
    pub conflict: u64,
    pub propagate: u64,
    /// The rounds of the first and last instantiation; none without one.
    pub first_round: Option<u64>,
    pub last_round: Option<u64>,
    /// Instances the refutation used, when `InstPressure::refutation`.
    pub refutation: Option<u64>,
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
pub(crate) fn parse_nl_frontier(line: &str) -> NlFrontier {
    use sise::TreeNode;
    let mut out = NlFrontier::default();
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
pub(crate) fn sexp_text(node: &sise::TreeNode) -> String {
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
fn parse_nl_bound(node: &sise::TreeNode) -> Option<NlBound> {
    let sise::TreeNode::List(items) = node else { return None };
    let mut b = NlBound::default();
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
fn parse_nl_term(node: &sise::TreeNode) -> Option<NlTerm> {
    let sise::TreeNode::List(items) = node else { return None };
    let mut t = NlTerm::default();
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
fn parse_nl_atom(node: &sise::TreeNode) -> Option<NlAtom> {
    use sise::TreeNode;
    let TreeNode::List(items) = node else { return None };
    let mut a = NlAtom::default();
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
                    let mut h = NlHost::default();
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
pub(crate) fn difficulty_count(v: &str) -> Option<u64> {
    (!v.is_empty() && v.bytes().all(|b| b.is_ascii_digit()))
        .then(|| v.parse::<u64>().unwrap_or(u64::MAX))
}

/// cvc5 quotes a symbol that needs it as `|...|`, which sise cannot read, so
/// spell each one as a sise string. A symbol that cannot be a sise string
/// (it holds `"` or `\`) is left alone, and the reply stays unparsed.
pub(crate) fn bar_symbols_as_strings(line: &str) -> String {
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

/// Parse cvc5's `(:inst-pressure (:rounds R :refutation B :quantifiers (ROW
/// ...)))`, where each ROW is `(qid :key value ...)`. Unknown keys are
/// skipped; a reply that does not parse is kept whole in `unparsed`.
pub(crate) fn parse_inst_pressure(line: &str) -> InstPressure {
    use sise::TreeNode;
    let mut out = InstPressure::default();
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

/// Parse cvc5's `(:check-effort (:resource-units N :instantiations M
/// :inst-rounds R))`. Unknown keys are skipped; a reply without the three
/// counts is kept whole in `unparsed`.
pub(crate) fn parse_check_effort(line: &str) -> CheckEffort {
    use sise::TreeNode;
    let mut out = CheckEffort::default();
    let fields = match read_smt_sexp(line) {
        Some(TreeNode::List(items)) => match &items[..] {
            [TreeNode::Atom(key), TreeNode::List(fields)] if key == ":check-effort" => {
                fields.clone()
            }
            _ => Vec::new(),
        },
        _ => Vec::new(),
    };
    let mut seen = 0;
    for pair in fields.chunks(2) {
        if let [TreeNode::Atom(k), TreeNode::Atom(v)] = pair {
            let slot = match k.as_str() {
                ":resource-units" => &mut out.resource_units,
                ":instantiations" => &mut out.instantiations,
                ":inst-rounds" => &mut out.inst_rounds,
                _ => continue,
            };
            if let Ok(n) = v.parse() {
                *slot = n;
                seen += 1;
            }
        }
    }
    if seen != 3 {
        out = CheckEffort { unparsed: Some(line.to_owned()), ..Default::default() };
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
fn parse_quant_pressure(row: &sise::TreeNode) -> Option<QuantPressure> {
    use sise::TreeNode;
    let TreeNode::List(items) = row else { return None };
    let (TreeNode::Atom(qid), rest) = items.split_first()? else { return None };
    let mut q = QuantPressure { qid: qid.to_owned(), named: true, ..Default::default() };
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
pub(crate) fn parse_matching_loops_lines(lines: &Vec<String>) -> MatchingLoopsInfo {
    use sise::TreeNode as Node;
    use {MatchingLoop, MatchingLoopsInfo};
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
pub(crate) fn parse_egraph_lines(lines: &[String]) -> EgraphReply {
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
    let mut reply = EgraphReply::default();
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
                            let mut equality = EgraphEquality {
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

/// At most this many e-graph equalities are asked for after a failed check.
const EGRAPH_LIMIT: u32 = 20;

/// Send one batch of commands and return the solver's reply lines.
fn ask(context: &mut crate::context::Context) -> Vec<String> {
    let smt_data = context.smt_log.take_pipe_data();
    context.get_smt_process().send_commands(smt_data)
}

/// One `(get-info :key)` whose reply is a single `(:key ...)` line, or
/// `None` when the solver has no such key (`unsupported`) or says something
/// else.
fn get_info_line(context: &mut crate::context::Context, key: &str) -> Option<String> {
    context.smt_log.log_get_info(key);
    let prefix = format!("(:{key} ");
    ask(context).into_iter().find(|line| line.starts_with(&prefix))
}

/// Read what the solver can say about the check that just failed, before
/// anything but other `get-info`s reaches it: the e-graph and the counters
/// describe this check until the next `check-sat` or `get-model`. `unknown`
/// is whether the check answered `unknown` rather than `sat`. Only reads:
/// nothing here is asserted, and the solver's budget is not involved.
pub(crate) fn read_after_failed_check(
    context: &mut crate::context::Context,
    unknown: bool,
) -> FailureDiagnostics {
    let mut diagnostics = FailureDiagnostics {
        result: if unknown { "unknown" } else { "sat" }.to_string(),
        variable_versions: context.variable_versions.clone(),
        ..Default::default()
    };
    diagnostics.check_effort =
        get_info_line(context, "check-effort").map(|line| parse_check_effort(&line));
    diagnostics.inst_pressure =
        get_info_line(context, "inst-pressure").map(|line| parse_inst_pressure(&line));
    diagnostics.nl_frontier =
        get_info_line(context, "nl-frontier").map(|line| parse_nl_frontier(&line));
    // The e-graph is focused on the classes of the query's own terms, and
    // read before `get-model` can disturb it.
    if let Some(assertion) = context.failure_query.clone() {
        let printer = crate::printer::Printer::new(
            context.message_interface.clone(),
            true,
            context.solver.clone(),
        );
        let focus = egraph_focus_terms(&assertion, &printer);
        context.smt_log.log_get_egraph_equalities(&focus, EGRAPH_LIMIT, false);
        diagnostics.egraph = Some(parse_egraph_lines(&ask(context)));
    }
    diagnostics
}

/// Parse cvc5's reply to `(get-instantiation-graph)`: `(instantiation-graph`,
/// then one `(quantifier <i> <qid>)` per quantifier, one `(node <i> <q>
/// <strategy> <round> <depth> <term-depth> (<parent> ...) [(eq ...)])` per
/// instantiation, `(dropped <n>)`, and `)`. The attributed `(eq ...)`
/// parents are left out: they are cvc5's inference, not an observed match.
pub(crate) fn parse_inst_cycles(lines: &[String]) -> InstCycles {
    fn parse(lines: &[String]) -> Option<InstCycles> {
        let mut out = InstCycles::default();
        let mut qids: Vec<String> = Vec::new();
        let mut node_q: Vec<usize> = Vec::new();
        let mut weights: HashMap<(usize, usize), u64> = HashMap::new();
        let mut lines = lines.iter().map(|l| l.trim()).filter(|l| !l.is_empty());
        if lines.next()? != "(instantiation-graph" {
            return None;
        }
        for line in lines {
            if line == ")" {
                break;
            }
            let body = line.strip_prefix('(')?.strip_suffix(')')?;
            let (head, rest) = body.split_once(' ')?;
            match head {
                "quantifier" => {
                    let (index, name) = rest.split_once(' ')?;
                    if index.parse::<usize>().ok()? != qids.len() {
                        return None;
                    }
                    let name =
                        name.strip_prefix('|').and_then(|n| n.strip_suffix('|')).unwrap_or(name);
                    qids.push(name.to_string());
                }
                "node" => {
                    let (fields, parents) = rest.split_once(" (")?;
                    let parents = parents.split(')').next()?;
                    let mut fields = fields.split(' ');
                    let index: usize = fields.next()?.parse().ok()?;
                    let q: usize = fields.next()?.parse().ok()?;
                    if index != node_q.len() || q >= qids.len() {
                        return None;
                    }
                    node_q.push(q);
                    for parent in parents.split(' ').filter(|p| !p.is_empty()) {
                        let parent: usize = parent.parse().ok()?;
                        let from = *node_q.get(parent)?;
                        *weights.entry((from, q)).or_default() += 1;
                    }
                }
                "dropped" => out.dropped = rest.parse().ok()?,
                _ => return None,
            }
        }
        out.instantiations = node_q.len() as u64;
        let mut counts = vec![0u64; qids.len()];
        for q in &node_q {
            counts[*q] += 1;
        }
        let mut adjacent = vec![Vec::new(); qids.len()];
        for &(from, to) in weights.keys() {
            adjacent[from].push(to);
        }
        for component in strongly_connected(&adjacent) {
            let self_loop = weights.contains_key(&(component[0], component[0]));
            if component.len() == 1 && !self_loop {
                continue;
            }
            let repetitions = weights
                .iter()
                .filter(|((f, t), _)| component.contains(f) && component.contains(t))
                .map(|(_, n)| n)
                .sum();
            let mut members: Vec<String> = component.iter().map(|q| qids[*q].clone()).collect();
            members.sort();
            let instantiations = component.iter().map(|q| counts[*q]).sum();
            out.cycles.push(InstCycle { qids: members, repetitions, instantiations });
        }
        out.cycles.sort_by(|a, b| b.repetitions.cmp(&a.repetitions).then(a.qids.cmp(&b.qids)));
        Some(out)
    }
    parse(lines).unwrap_or_else(|| InstCycles {
        unparsed: Some(lines.join(" ").chars().take(200).collect()),
        ..Default::default()
    })
}

/// The strongly connected components of a graph over `0..adjacent.len()`
/// (Tarjan's algorithm, iterative so a long chain cannot overflow the stack).
fn strongly_connected(adjacent: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = adjacent.len();
    let (mut index, mut low) = (vec![usize::MAX; n], vec![0; n]);
    let mut on_stack = vec![false; n];
    let (mut stack, mut components, mut next) = (Vec::new(), Vec::new(), 0);
    for root in 0..n {
        if index[root] != usize::MAX {
            continue;
        }
        let mut work = vec![(root, 0usize)];
        while let Some(&mut (v, ref mut child)) = work.last_mut() {
            if *child == 0 {
                index[v] = next;
                low[v] = next;
                next += 1;
                stack.push(v);
                on_stack[v] = true;
            }
            if let Some(&w) = adjacent[v].get(*child) {
                *child += 1;
                if index[w] == usize::MAX {
                    work.push((w, 0));
                } else if on_stack[w] {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            work.pop();
            if let Some(&(parent, _)) = work.last() {
                low[parent] = low[parent].min(low[v]);
            }
            if low[v] == index[v] {
                let mut component = Vec::new();
                loop {
                    let w = stack.pop().expect("tarjan stack");
                    on_stack[w] = false;
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                components.push(component);
            }
        }
    }
    components
}

/// After an `unknown`: the cycles among the quantifiers that instantiated
/// each other. Read before the next `check-sat`, which starts a new graph.
pub(crate) fn read_inst_cycles(context: &mut crate::context::Context) -> InstCycles {
    context.smt_log.log_node(&sise::TreeNode::List(vec![sise::TreeNode::Atom(
        "get-instantiation-graph".to_string(),
    )]));
    parse_inst_cycles(&ask(context))
}

/// After an `unknown`, once its reason has been read: the quantifiers that
/// fed themselves. Read before the next `check-sat`, whose presolve clears
/// the record.
pub(crate) fn read_matching_loops(context: &mut crate::context::Context) -> MatchingLoopsInfo {
    context.smt_log.log_get_info("matching-loops");
    parse_matching_loops_lines(&ask(context))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Quant, TypX};
    use crate::ast_util::mk_and;
    use crate::context::SmtSolver;
    use std::sync::Arc;

    /// cvc5's `(get-info :matching-loops)` reply, as it prints it: one loop per
    /// line after the header.
    #[test]
    fn matching_loops_reply_parses() {
        let lines: Vec<String> = [
            "(:matching-loops (:rounds 10 :instantiations 12 :dropped 0 :max-inst-rounds true :loops (",
            "(loop :qid |user_f_grows_3| :confidence high :growth linear-depth :edges confirmed \
             :stable true :instantiations 10 :rounds 10 :first-round 1 :last-round 10 :chain 10 \
             :self-fed 9 :depth-per-rung 1.00 :depth-per-round 1.00 :fanout-per-round 1.00 \
             :via () :trigger ((f x)) :context ((g _0)) :shape ((f _0)) :step ((f (g _0))) \
             :ladder (((f a)) ((f (g a))) ((f (g (g a)))) ((f (g (g (g a)))))) :ladder-length 10 \
             :per-round (1 1 1 1 1 1 1 1 1 1)))))",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        let info = super::parse_matching_loops_lines(&lines);
        assert!(info.unparsed.is_empty(), "{:?}", info.unparsed);
        assert_eq!((info.rounds, info.instantiations, info.max_inst_rounds), (10, 12, true));
        assert_eq!(info.loops.len(), 1);
        let l = &info.loops[0];
        assert_eq!(l.qid, "user_f_grows_3");
        assert_eq!((l.confidence.as_str(), l.growth.as_str()), ("high", "linear-depth"));
        assert!(l.edges_confirmed && l.stable);
        assert_eq!((l.chain, l.self_fed, l.ladder_length), (10, 9, 10));
        assert_eq!(l.depth_per_round, 1.0);
        assert_eq!(l.trigger, vec!["(f x)"]);
        assert_eq!(l.context, vec!["(g _0)"]);
        assert_eq!(l.shape, vec!["(f _0)"]);
        assert_eq!(l.step, vec!["(f (g _0))"]);
        assert_eq!(l.ladder.len(), 4);
        assert_eq!(l.ladder[1], vec!["(f (g a))"]);
        assert_eq!(l.per_round.len(), 10);
        // no loops; and a reply of another shape is kept, not failed on
        let info = super::parse_matching_loops_lines(&vec![
            "(:matching-loops (:rounds 2 :instantiations 3 :dropped 0 :max-inst-rounds false :loops ()))"
                .to_string(),
        ]);
        assert!(info.loops.is_empty() && info.unparsed.is_empty());
        let info = super::parse_matching_loops_lines(&vec!["(error \"no\")".to_string()]);
        assert_eq!(info.unparsed, vec!["(error \"no\")".to_string()]);
        // a quoted symbol sise cannot read bare, a bar inside a string literal,
        // and a term broken across lines: the reply still parses, terms one line
        let info = super::parse_matching_loops_lines(&vec![
            "(:matching-loops (:rounds 3 :instantiations 3 :dropped 0 :max-inst-rounds false :loops ("
                .to_string(),
            "(loop :qid |odd name| :confidence low :growth bounded :edges unconfirmed :stable false \
             :via (|odd name|) :trigger ((str.++ s \"a|b\")) :shape ((f\n   (g _0))) :ladder-length 0))))"
                .to_string(),
        ]);
        assert!(info.unparsed.is_empty(), "{:?}", info.unparsed);
        let l = &info.loops[0];
        assert_eq!((l.qid.as_str(), l.via.clone()), ("|odd name|", vec!["|odd name|".to_string()]));
        assert_eq!(l.trigger, vec!["(str.++ s \"a|b\")"]);
        assert_eq!(l.shape, vec!["(f (g _0))"]);
        // `:fanout-per-step` beside `:fanout-per-round`, and one context per
        // class of growing subterm (BasisResearch/cvc5#3 since ea27199)
        let info = super::parse_matching_loops_lines(&vec![
            "(:matching-loops (:rounds 10 :instantiations 31 :dropped 0 :max-inst-rounds true :loops ("
                .to_string(),
            "(loop :qid |user_f_branches_1| :confidence high :growth exponential-fanout \
             :edges confirmed :stable true :fanout-per-round 1.41 :fanout-per-step 2.00 \
             :context ((r _0) (l _0)) :ladder-length 5))))"
                .to_string(),
        ]);
        assert!(info.unparsed.is_empty(), "{:?}", info.unparsed);
        let l = &info.loops[0];
        assert_eq!((l.fanout_per_round, l.fanout_per_step), (1.41, 2.0));
        assert_eq!(l.context, vec!["(r _0)", "(l _0)"]);
    }

    /// cvc5's `(get-info :incomplete-culprits)` reply: plain symbols, and symbols
    /// it had to quote.
    #[test]
    fn incomplete_culprits_reply_parses() {
        let parse = super::parse_incomplete_culprits;
        assert_eq!(
            parse("(:incomplete-culprits (user_lib__f_4 |also never matched| prelude_box_unbox))"),
            vec!["user_lib__f_4", "also never matched", "prelude_box_unbox"]
        );
        assert!(parse("(:incomplete-culprits ())").is_empty());
        // an unterminated quote ends the list rather than inventing a name
        assert_eq!(parse("(:incomplete-culprits (a |b))"), vec!["a"]);
        assert!(parse("unsupported").is_empty());
    }

    #[test]
    fn parse_nl_frontier_reply() {
        // the shape cvc5's (get-info :nl-frontier) prints after a budget runs out
        let f = super::parse_nl_frontier(
            "(:nl-frontier (:result unknown :reason resourceout :enabled true :checks 40 \
             :rounds 38 :punts 0 :last lemma :atoms (\
             (:atom (* x y) :kind product :current true :rounds 12 :value 5 :from-args -6 \
             :lower (:value 0 :strict false :fixed true) \
             :args ((:term x :value 2 :lower (:value 0 :strict false :fixed true)) \
             (:term |y%1| :value -1/3 :upper (:value 10 :strict true :fixed false))) \
             :hosts ((:in input :term (Mul x |y%1|) :tags (query hyp_2)) \
             (:in instance :term (Mul x |y%1|) :qid prelude_mul :count 3)))) \
             :omitted 0 :truncated false))",
        );
        assert!(f.unparsed.is_none(), "{:?}", f.unparsed);
        assert_eq!(
            (f.result.as_str(), f.reason.as_str(), f.last.as_str()),
            ("unknown", "resourceout", "lemma")
        );
        assert_eq!((f.enabled, f.checks, f.rounds, f.punts, f.omitted), (true, 40, 38, 0, 0));
        let a = &f.atoms[0];
        assert_eq!(
            (a.atom.as_str(), a.kind.as_str(), a.current, a.rounds),
            ("(* x y)", "product", true, 12)
        );
        assert_eq!((a.value.as_str(), a.from_args.as_str()), ("5", "-6"));
        assert_eq!(a.args[1].value, "-1/3");
        assert!(a.lower.as_ref().is_some_and(|b| b.value == "0" && !b.strict && b.fixed));
        assert!(a.upper.is_none());
        // quoted symbols lose their bars
        assert_eq!(a.args[1].term, "y%1");
        assert!(a.args[1].upper.as_ref().is_some_and(|b| b.value == "10" && b.strict && !b.fixed));
        assert_eq!(a.hosts.len(), 2);
        assert!(a.hosts[0].input && a.hosts[0].tags == vec!["query", "hyp_2"]);
        assert_eq!(a.hosts[0].term, "(Mul x y%1)");
        assert!(!a.hosts[1].input && a.hosts[1].qid.as_deref() == Some("prelude_mul"));
        assert_eq!(a.hosts[1].count, 3);

        // nothing recorded; a solver without the key or anything unforeseen is kept whole
        let f = super::parse_nl_frontier(
            "(:nl-frontier (:result unsat :reason none :enabled true :checks 0 :rounds 0 \
             :punts 0 :last none :atoms () :omitted 0 :truncated false))",
        );
        assert!(f.unparsed.is_none() && f.atoms.is_empty() && f.result == "unsat");
        let bad = "(:nl-frontier (:result sat :atoms ((:atom (* x y) :rounds many))))";
        assert_eq!(super::parse_nl_frontier(bad).unparsed.as_deref(), Some(bad));
        let bad = "(:nl-frontier unsupported)";
        assert_eq!(super::parse_nl_frontier(bad).unparsed.as_deref(), Some(bad));
        // a key without a value is malformed, at any depth
        let bad = "(:nl-frontier (:result sat :checks))";
        assert_eq!(super::parse_nl_frontier(bad).unparsed.as_deref(), Some(bad));
        let bad = "(:nl-frontier (:result sat :atoms ((:atom (* x y) :kind))))";
        assert_eq!(super::parse_nl_frontier(bad).unparsed.as_deref(), Some(bad));
        // a quoted symbol that is not one word keeps its bars
        let f = super::parse_nl_frontier(
            "(:nl-frontier (:result sat :atoms ((:atom (* x |a b|) :args ((:term |a b| :value 3)) \
             :hosts ((:in input :term (Mul x |a b|) :tags (query)))))))",
        );
        assert!(f.unparsed.is_none(), "{:?}", f.unparsed);
        assert_eq!(f.atoms[0].atom, "(* x |a b|)");
        assert_eq!(f.atoms[0].args[0].term, "|a b|");
        assert_eq!(f.atoms[0].hosts[0].term, "(Mul x |a b|)");
    }

    #[test]
    fn parse_inst_pressure_reply() {
        let info = super::parse_inst_pressure(
            "(:inst-pressure (:rounds 3 :refutation true :quantifiers (\
             (user_f_1 :instantiations 5 :duplicate-eq 2 :duplicate-ent 1 :duplicate-lemma 0 \
             :conflict 1 :propagate 0 :first-round 0 :last-round 2 :refutation 1) \
             (|user%g| :instantiations 0 :duplicate-eq 4 :duplicate-ent 0 :duplicate-lemma 0 \
             :conflict 0 :propagate 0 :refutation 0) \
             (quant_0 :named false :instantiations 1 :duplicate-eq 0 :duplicate-ent 0 \
             :duplicate-lemma 0 :conflict 0 :propagate 1 :first-round 1 :last-round 1 \
             :refutation 0))))",
        );
        assert!(info.unparsed.is_none(), "{:?}", info.unparsed);
        assert_eq!((info.rounds, info.refutation, info.quantifiers.len()), (3, true, 3));
        let f = &info.quantifiers[0];
        assert_eq!(f.qid, "user_f_1");
        assert!(f.named);
        assert_eq!(
            (f.instantiations, f.duplicate_eq, f.duplicate_ent, f.duplicate_lemma),
            (5, 2, 1, 0)
        );
        assert_eq!(
            (f.conflict, f.first_round, f.last_round, f.refutation),
            (1, Some(0), Some(2), Some(1))
        );
        // only duplicates: no rounds; quoted symbols lose their bars
        let q = &info.quantifiers[1];
        assert_eq!((q.qid.as_str(), q.first_round, q.duplicate_eq), ("user%g", None, 4));
        let u = &info.quantifiers[2];
        assert_eq!((u.qid.as_str(), u.named, u.propagate), ("quant_0", false, 1));

        // no quantifier instantiated; no refutation counts outside proof mode
        let info = super::parse_inst_pressure(
            "(:inst-pressure (:rounds 0 :refutation false :quantifiers ()))",
        );
        assert!(info.unparsed.is_none() && info.quantifiers.is_empty() && !info.refutation);
        // a solver without the key, or anything unforeseen, is kept whole
        let info = super::parse_inst_pressure("(:inst-pressure unsupported)");
        assert_eq!(info.unparsed.as_deref(), Some("(:inst-pressure unsupported)"));
    }

    #[test]
    fn parse_inst_pressure_symbols() {
        let row = |qid: &str| {
            format!(
                "(:inst-pressure (:rounds 1 :refutation false :quantifiers (({} :instantiations 1 \
                 :duplicate-eq 0 :duplicate-ent 0 :duplicate-lemma 0 :conflict 0 :propagate 0 \
                 :first-round 0 :last-round 0))))",
                qid
            )
        };
        let qids = |line: &str| {
            let info = super::parse_inst_pressure(line);
            assert!(info.unparsed.is_none(), "{:?}", info.unparsed);
            info.quantifiers.into_iter().map(|q| q.qid).collect::<Vec<_>>()
        };
        // a simple symbol may hold characters sise's atoms lack
        assert_eq!(qids(&row("a^b")), vec!["a^b"]);
        // a quoted one may hold anything but a bar, spaces and quotes included
        assert_eq!(qids(&row("|a b|")), vec!["a b"]);
        assert_eq!(qids(&row("|say \"hi\"|")), vec!["say \"hi\""]);
        assert_eq!(qids(&row("||")), vec![""]);

        // unbalanced, trailing, or cut short: kept whole
        for line in [
            "(:inst-pressure (:rounds 1 :refutation false :quantifiers ((a :instantiations 1)))",
            "(:inst-pressure (:rounds 1)) x",
            "(:inst-pressure (:rounds 1 :refutation false :quantifiers ((|a :instantiations 1))))",
        ] {
            let info = super::parse_inst_pressure(line);
            assert_eq!(info.unparsed.as_deref(), Some(line));
        }
        // a malformed row is reported, the others kept
        let info = super::parse_inst_pressure(
            "(:inst-pressure (:rounds 2 :refutation false :quantifiers ((ok :instantiations 1) \
             (bad :instantiations x))))",
        );
        assert!(info.unparsed.is_some());
        assert_eq!(info.quantifiers.len(), 1);
    }

    #[test]
    fn parse_check_effort_reply() {
        let effort = super::parse_check_effort(
            "(:check-effort (:resource-units 1234 :instantiations 7 :inst-rounds 2))",
        );
        assert_eq!(effort.resource_units, 1234);
        assert_eq!(effort.instantiations, 7);
        assert_eq!(effort.inst_rounds, 2);
        assert!(effort.unparsed.is_none());
        // a missing count, or a reply that is not one, is kept whole
        for line in ["(:check-effort (:resource-units 1 :instantiations 2))", "(:check-effort ())"]
        {
            let effort = super::parse_check_effort(line);
            assert_eq!(effort.unparsed.as_deref(), Some(line));
            assert_eq!(effort.resource_units, 0);
        }
    }

    #[test]
    fn instantiation_graph_folds_to_quantifier_cycles() {
        let lines: Vec<String> = [
            "(instantiation-graph",
            "(quantifier 0 user_f_1)",
            "(quantifier 1 user_g_2)",
            "(quantifier 2 |prelude_box|)",
            "(node 0 0 QUANTIFIERS_INST_E_MATCHING 1 0 1 ())",
            "(node 1 1 QUANTIFIERS_INST_E_MATCHING 2 1 2 (0))",
            "(node 2 0 QUANTIFIERS_INST_E_MATCHING 3 2 3 (1) (eq 0))",
            "(node 3 2 QUANTIFIERS_INST_E_MATCHING 3 3 3 (2))",
            "(node 4 2 QUANTIFIERS_INST_E_MATCHING 4 4 3 (3))",
            "(dropped 7)",
            ")",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        let graph = parse_inst_cycles(&lines);
        assert!(graph.unparsed.is_none(), "{:?}", graph.unparsed);
        assert_eq!((graph.instantiations, graph.dropped), (5, 7));
        // f and g feed each other; the box axiom feeds only itself
        assert_eq!(
            graph.cycles,
            vec![
                InstCycle {
                    qids: vec!["user_f_1".into(), "user_g_2".into()],
                    repetitions: 2,
                    instantiations: 3,
                },
                InstCycle { qids: vec!["prelude_box".into()], repetitions: 1, instantiations: 2 },
            ]
        );
        // a refusal, or a parent that is not an earlier instance, is kept
        let refused = parse_inst_cycles(&lines_of(&["(error \"no graph\")"]));
        assert!(refused.unparsed.is_some() && refused.cycles.is_empty());
        let bad = parse_inst_cycles(&lines_of(&[
            "(instantiation-graph",
            "(quantifier 0 q)",
            "(node 0 0 S 1 0 1 (3))",
            ")",
        ]));
        assert!(bad.unparsed.is_some());
    }

    fn lines_of(text: &[&str]) -> Vec<String> {
        text.iter().map(|line| line.to_string()).collect()
    }

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
