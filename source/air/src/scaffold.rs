//! Rewrites of one query that ask about a proposed intermediate assertion
//! (`proof_scaffold_step`).
//!
//! Given a query, the `AssertId` of one of its goals (the target) and a
//! boolean expression `P` over the query's own names, two rewrites ask two
//! questions about `P` at the target's program point:
//!
//! - `Arm::Provable`: is `P` provable there? The target is replaced by an
//!   assertion of `P`.
//! - `Arm::GoalGiven`: does the target hold once `P` is assumed there? An
//!   assumption of `P` is placed right before the target.
//!
//! In both, every other goal of the query becomes an assumption of what it
//! asserts. The answer is then about `P` or the target alone: no other goal
//! can fail the check, and a goal before the target on its path is a
//! hypothesis of the check. Verus itself assumes a source `assert` after
//! checking it, but not a call's precondition, a loop invariant or a
//! postcondition; here those are hypotheses too. When they hold, they follow
//! from the context and change nothing but what the solver has at hand. A
//! goal that fails, before a target the caller named, is assumed all the
//! same, and a false one makes the answer vacuous: the query's own check
//! says which goals fail. The real verifier still checks every one of them.
//!
//! `P` is placed among the query's statements rather than asserted beside
//! the query, so its variables mean what they mean at the target: a variable
//! assigned earlier is read at the version the target reads.
//!
//! A goal is addressed by its `AssertId`, or, for the asserts Verus emits
//! without one (loop invariants at a loop's end, `decreases`), by its index
//! among the query's `Assert` statements.
//!
//! The rewritten query is an ordinary query. Checked in the original query's
//! scope, nothing it asserts outlives the check.

use crate::ast::{AssertId, BindX, DeclX, Expr, ExprX, Ident, Query, QueryX, Stmt, StmtX};
use crate::messages::ArcDynMessage;
use std::collections::HashSet;
use std::sync::Arc;

/// Which question a rewrite asks about `P`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Arm {
    /// Is `P` provable at the target?
    Provable,
    /// Does the target hold once `P` is assumed there?
    GoalGiven,
}

/// A query rewritten for one arm.
pub struct Scaffold {
    pub query: Query,
    /// How often the target occurs: a goal on several branches occurs once
    /// per branch, and `P` is placed before each.
    pub occurrences: usize,
    /// The target's error message, from its first occurrence. Its spans say
    /// where the target is.
    pub error: ArcDynMessage,
    /// Whether the target's first occurrence is the last assert of the dead
    /// end it sits in, as the claim of `assert ... by` is: `P` is then checked
    /// after that block's steps. A goal among the steps is not. The last
    /// assert of a closure body ends its dead end too; the source tells the
    /// two apart.
    pub ends_dead_end: bool,
}

/// Which goal of a query to rewrite around.
#[derive(Clone, Copy, Debug)]
pub enum Target<'a> {
    /// Every `Assert` with this id.
    Id(&'a [u64]),
    /// The `Assert` at this index among the query's `Assert` statements, in
    /// the order the statements reach them (`Goal::index`), for a goal
    /// without an id.
    Index(usize),
}

struct Found {
    occurrences: usize,
    error: Option<ArcDynMessage>,
    /// `Assert` statements passed so far, the index of the next one.
    next_index: usize,
    /// The dead ends now open, innermost last, by the order they opened in.
    open_dead_ends: Vec<usize>,
    dead_ends_opened: usize,
    /// The innermost dead end around the target's first occurrence, while it
    /// is open and no other assert inside it has followed the target.
    trailing_in: Option<usize>,
    ends_dead_end: bool,
}

/// Rewrite `query` for `arm` around `target`. Fails when no goal matches.
pub fn scaffold_query(
    query: &Query,
    target: Target<'_>,
    p: &Expr,
    arm: Arm,
) -> Result<Scaffold, String> {
    let mut found = Found {
        occurrences: 0,
        error: None,
        next_index: 0,
        open_dead_ends: Vec::new(),
        dead_ends_opened: 0,
        trailing_in: None,
        ends_dead_end: false,
    };
    let assertion = rewrite(&query.assertion, target, p, arm, &mut found);
    match found.error {
        Some(error) => Ok(Scaffold {
            query: Arc::new(QueryX { local: query.local.clone(), assertion }),
            occurrences: found.occurrences,
            error,
            ends_dead_end: found.ends_dead_end,
        }),
        None => Err(match target {
            Target::Id(id) => format!("the query has no goal with assert id {:?}", id),
            Target::Index(i) => format!("the query has no goal at index {i}"),
        }),
    }
}

fn rewrite(stmt: &Stmt, target: Target<'_>, p: &Expr, arm: Arm, found: &mut Found) -> Stmt {
    let stmts = |stmts: &[Stmt], found: &mut Found| -> Arc<Vec<Stmt>> {
        Arc::new(stmts.iter().map(|s| rewrite(s, target, p, arm, found)).collect())
    };
    match &**stmt {
        StmtX::Assert(id, error, filter, expr) => {
            let index = found.next_index;
            found.next_index += 1;
            if found.trailing_in.take().is_some() {
                // another assert inside the target's dead end, after it
                found.ends_dead_end = false;
            }
            let matches = match target {
                Target::Id(target) => id.as_ref().is_some_and(|id| **id == target),
                Target::Index(target) => index == target,
            };
            if !matches {
                return Arc::new(StmtX::Assume(expr.clone()));
            }
            found.occurrences += 1;
            if found.error.is_none() {
                found.error = Some(error.clone());
                found.trailing_in = found.open_dead_ends.last().copied();
                found.ends_dead_end = found.trailing_in.is_some();
            }
            match arm {
                Arm::Provable => {
                    Arc::new(StmtX::Assert(id.clone(), error.clone(), filter.clone(), p.clone()))
                }
                Arm::GoalGiven => Arc::new(StmtX::Block(Arc::new(vec![
                    Arc::new(StmtX::Assume(p.clone())),
                    stmt.clone(),
                ]))),
            }
        }
        StmtX::Block(inner) => Arc::new(StmtX::Block(stmts(inner, found))),
        StmtX::Switch(inner) => Arc::new(StmtX::Switch(stmts(inner, found))),
        StmtX::DeadEnd(inner) => {
            let serial = found.dead_ends_opened;
            found.dead_ends_opened += 1;
            found.open_dead_ends.push(serial);
            let inner = rewrite(inner, target, p, arm, found);
            found.open_dead_ends.pop();
            if found.trailing_in == Some(serial) {
                // the target's dead end closed with no assert after it
                found.trailing_in = None;
            }
            Arc::new(StmtX::DeadEnd(inner))
        }
        StmtX::Breakable(label, inner) => {
            Arc::new(StmtX::Breakable(label.clone(), rewrite(inner, target, p, arm, found)))
        }
        StmtX::Assume(_)
        | StmtX::Havoc(_)
        | StmtX::Assign(..)
        | StmtX::Snapshot(_)
        | StmtX::Break(_) => stmt.clone(),
    }
}

/// One goal of a query, as `goals` lists them.
#[derive(Clone, Debug)]
pub struct Goal {
    /// Its index among the query's `Assert` statements, in the order the
    /// statements reach them; of a goal with several occurrences, the first.
    pub index: usize,
    /// `None` for the asserts Verus emits without an id.
    pub id: Option<AssertId>,
    /// The error message of its first occurrence.
    pub error: ArcDynMessage,
}

impl Goal {
    /// How to address this goal: by id when it has one, so that every
    /// occurrence is rewritten, else by index.
    pub fn target(&self) -> Target<'_> {
        match &self.id {
            Some(id) => Target::Id(id),
            None => Target::Index(self.index),
        }
    }
}

/// The query's goals in the order the statements reach them: each id once,
/// and each assert without an id.
pub fn goals(query: &Query) -> Vec<Goal> {
    fn walk(stmt: &Stmt, next_index: &mut usize, out: &mut Vec<Goal>) {
        match &**stmt {
            StmtX::Assert(id, error, _, _) => {
                let index = *next_index;
                *next_index += 1;
                let seen = id.is_some() && out.iter().any(|goal| goal.id == *id);
                if !seen {
                    out.push(Goal { index, id: id.clone(), error: error.clone() });
                }
            }
            StmtX::Block(stmts) | StmtX::Switch(stmts) => {
                stmts.iter().for_each(|s| walk(s, next_index, out))
            }
            StmtX::DeadEnd(s) | StmtX::Breakable(_, s) => walk(s, next_index, out),
            _ => {}
        }
    }
    let mut out = Vec::new();
    walk(&query.assertion, &mut 0, &mut out);
    out
}

/// What a query's own text uses: every application with its arguments, and
/// every variable its statements read or write. A name resolver prefers what
/// the query already uses, and takes a generic function's type arguments from
/// the applications.
#[derive(Default)]
pub struct Occurrences {
    /// Each application in the query's axioms and statements, outermost first.
    pub applications: Vec<(Ident, crate::ast::Exprs)>,
    /// Variables the statements mention, `old` reads included.
    pub statement_variables: HashSet<Ident>,
}

pub fn occurrences(query: &Query) -> Occurrences {
    let mut out = Occurrences::default();
    for decl in query.local.iter() {
        if let DeclX::Axiom(axiom) = &**decl {
            expr_occurrences(&axiom.expr, &mut out.applications, &mut HashSet::new());
        }
    }
    stmt_occurrences(&query.assertion, &mut out);
    out
}

fn stmt_occurrences(stmt: &Stmt, out: &mut Occurrences) {
    match &**stmt {
        StmtX::Assume(e) | StmtX::Assert(_, _, _, e) => {
            expr_occurrences(e, &mut out.applications, &mut out.statement_variables)
        }
        StmtX::Assign(x, e) => {
            out.statement_variables.insert(x.clone());
            expr_occurrences(e, &mut out.applications, &mut out.statement_variables);
        }
        StmtX::Havoc(x) => {
            out.statement_variables.insert(x.clone());
        }
        StmtX::Block(stmts) | StmtX::Switch(stmts) => {
            stmts.iter().for_each(|s| stmt_occurrences(s, out))
        }
        StmtX::DeadEnd(s) | StmtX::Breakable(_, s) => stmt_occurrences(s, out),
        StmtX::Snapshot(_) | StmtX::Break(_) => {}
    }
}

fn expr_occurrences(
    expr: &Expr,
    applications: &mut Vec<(Ident, crate::ast::Exprs)>,
    variables: &mut HashSet<Ident>,
) {
    let mut go = |e: &Expr| expr_occurrences(e, applications, variables);
    match &**expr {
        ExprX::Const(_) => {}
        ExprX::Var(x) | ExprX::Old(_, x) => {
            variables.insert(x.clone());
        }
        ExprX::Apply(head, args) => {
            applications.push((head.clone(), args.clone()));
            for arg in args.iter() {
                expr_occurrences(arg, applications, variables);
            }
        }
        ExprX::ApplyFun(_, f, args) => {
            go(f);
            for arg in args.iter() {
                expr_occurrences(arg, applications, variables);
            }
        }
        ExprX::Unary(_, e) | ExprX::LabeledAxiom(_, _, e) | ExprX::LabeledAssertion(_, _, _, e) => {
            go(e)
        }
        ExprX::Binary(_, a, b) => {
            expr_occurrences(a, applications, variables);
            expr_occurrences(b, applications, variables);
        }
        ExprX::Multi(_, es) | ExprX::Array(es) => {
            for e in es.iter() {
                expr_occurrences(e, applications, variables);
            }
        }
        ExprX::IfElse(a, b, c) => {
            for e in [a, b, c] {
                expr_occurrences(e, applications, variables);
            }
        }
        ExprX::Bind(bind, body) => {
            match &**bind {
                BindX::Let(binders) => {
                    for binder in binders.iter() {
                        expr_occurrences(&binder.a, applications, variables);
                    }
                }
                BindX::Quant(_, _, triggers, _) | BindX::Lambda(_, triggers, _) => {
                    for trigger in triggers.iter() {
                        for e in trigger.iter() {
                            expr_occurrences(e, applications, variables);
                        }
                    }
                }
                BindX::Choose(_, triggers, _, cond) => {
                    for trigger in triggers.iter() {
                        for e in trigger.iter() {
                            expr_occurrences(e, applications, variables);
                        }
                    }
                    expr_occurrences(cond, applications, variables);
                }
            }
            expr_occurrences(body, applications, variables);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::CommandX;
    use crate::context::{Context, SmtSolver, ValidityResult};
    use crate::messages::{AirMessageInterface, Reporter};
    use crate::parser::Parser;
    use sise::TreeNode as Node;

    /// Declare everything before the query, then answer `arm` of the query
    /// for `target` and `p`, and the query itself, with z3.
    fn answers(nodes: &[Node], target: Target<'_>, p: Node, arm: Arm) -> (bool, bool, usize) {
        let mi = Arc::new(AirMessageInterface {});
        let parser = Parser::new(mi.clone());
        let commands = parser.nodes_to_commands(nodes).expect("parses");
        let p = parser.node_to_expr(&p).expect("P parses");
        let mut context = Context::new(mi.clone(), SmtSolver::Z3);
        context.set_z3_param("air_recommended_options", "true");
        let mut result = None;
        for command in commands.iter() {
            match &**command {
                CommandX::CheckValid(query) => {
                    let valid = |context: &mut Context, query: &Query| {
                        let r = context.check_valid(&*mi, &Reporter {}, query, Default::default());
                        assert!(!matches!(r, ValidityResult::TypeError(_)), "{:?}", r);
                        context.finish_query();
                        matches!(r, ValidityResult::Valid(_))
                    };
                    let scaffold = scaffold_query(query, target, &p, arm).expect("target found");
                    let rewritten = valid(&mut context, &scaffold.query);
                    let original = valid(&mut context, query);
                    result = Some((rewritten, original, scaffold.occurrences));
                }
                _ => {
                    let r = context.command(&*mi, &Reporter {}, command, Default::default());
                    assert!(matches!(r, ValidityResult::Valid(_)), "{:?}", r);
                }
            }
        }
        result.expect("a check-valid")
    }

    /// The top-level forms of `text`. Parsed as text, not built with `node!`,
    /// so an assertion's labels stay the quoted strings the parser expects.
    fn nodes(text: &str) -> Vec<Node> {
        let text = format!("({text})");
        let mut parser = sise::Parser::new(&text);
        match sise::parse_tree(&mut parser).expect("well formed") {
            Node::List(items) => items,
            Node::Atom(_) => unreachable!(),
        }
    }

    fn one(text: &str) -> Node {
        nodes(text).remove(0)
    }

    fn query() -> Vec<Node> {
        nodes(
            r#"(declare-fun g (Int) Int)
            (check-valid
                (declare-var y Int)
                (declare-const a Int)
                (axiom (> a 0))
                (block
                    (assign y a)
                    (assert aid_0 ("first") () (> y 5))
                    (assign y (+ y 1))
                    (assert aid_1 ("second") () (> (g y) 0))))"#,
        )
    }

    /// `P` reads a variable at the version the target reads, not at the
    /// query's start: `y` was assigned twice before `aid_1`.
    #[test]
    fn p_is_placed_at_the_target() {
        let (provable, original, occurrences) =
            answers(&query(), Target::Id(&[1]), one("(= y (+ a 1))"), Arm::Provable);
        assert!(provable);
        assert!(!original);
        assert_eq!(occurrences, 1);
        let (provable, _, _) = answers(&query(), Target::Id(&[1]), one("(= y a)"), Arm::Provable);
        assert!(!provable);
    }

    /// The goal closes once `P` is assumed, though `P` is no fact.
    #[test]
    fn a_helpful_p_need_not_be_provable() {
        let helpful = one("(> (g y) 0)");
        assert!(answers(&query(), Target::Id(&[1]), helpful.clone(), Arm::GoalGiven).0);
        assert!(!answers(&query(), Target::Id(&[1]), helpful, Arm::Provable).0);
        // true but no help
        assert!(answers(&query(), Target::Id(&[1]), one("(> y 1)"), Arm::Provable).0);
        assert!(!answers(&query(), Target::Id(&[1]), one("(> y 1)"), Arm::GoalGiven).0);
    }

    /// Other goals are assumed, not proved: `aid_0` (`y > 5`) is no fact,
    /// yet it holds for `aid_1`'s arm, and the answer is about `aid_1`.
    #[test]
    fn other_goals_are_assumed() {
        let (given, _, _) = answers(&query(), Target::Id(&[1]), one("(> y 6)"), Arm::Provable);
        assert!(given);
    }

    /// A goal without an id, as Verus emits a loop invariant at the loop's
    /// end, is addressed by its index among the asserts, and one ending a
    /// dead end says so.
    #[test]
    fn a_goal_without_an_id_is_addressed_by_index() {
        let nodes = nodes(
            r#"(check-valid
                (declare-var y Int)
                (declare-const a Int)
                (axiom (> a 5))
                (block
                    (assign y a)
                    (assert aid_0 ("first") () (> y 5))
                    (deadend (block (assume (> y 6)) (assert ("second") () (> y 6))))
                    (assert ("third") () (> y 2))))"#,
        );
        let mi = Arc::new(AirMessageInterface {});
        let parser = Parser::new(mi);
        let commands = parser.nodes_to_commands(&nodes).unwrap();
        let CommandX::CheckValid(query) = &*commands[0] else { panic!() };
        let listed = goals(query);
        let ids: Vec<Option<Vec<u64>>> =
            listed.iter().map(|g| g.id.as_ref().map(|id| (**id).clone())).collect();
        assert_eq!(ids, vec![Some(vec![0]), None, None]);
        assert_eq!(listed.iter().map(|g| g.index).collect::<Vec<_>>(), vec![0, 1, 2]);
        assert!(matches!(listed[0].target(), Target::Id(&[0])));
        assert!(matches!(listed[2].target(), Target::Index(2)));
        // P at the third assert, addressed by index
        let (provable, original, _) =
            answers(&nodes, Target::Index(2), one("(= y a)"), Arm::Provable);
        assert!(provable);
        assert!(original);
        let p = parser.node_to_expr(&one("true")).unwrap();
        assert!(scaffold_query(query, Target::Index(1), &p, Arm::Provable).unwrap().ends_dead_end);
        assert!(!scaffold_query(query, Target::Index(2), &p, Arm::Provable).unwrap().ends_dead_end);
        assert!(scaffold_query(query, Target::Index(3), &p, Arm::Provable).is_err());
    }

    /// Only the last assert of a dead end ends it, as the claim of `assert
    /// ... by` does after the block's steps: a goal among the steps is
    /// followed by another assert, here one inside a nested dead end.
    #[test]
    fn only_a_dead_ends_last_goal_ends_it() {
        let nodes = nodes(
            r#"(check-valid
                (declare-const a Int)
                (block
                    (deadend (block
                        (assert ("step") () (> a 0))
                        (deadend (block (assert ("inner") () (> a 1))))
                        (assert ("claim") () (> a 2))))
                    (assert ("after") () (> a 3))))"#,
        );
        let mi = Arc::new(AirMessageInterface {});
        let parser = Parser::new(mi);
        let commands = parser.nodes_to_commands(&nodes).unwrap();
        let CommandX::CheckValid(query) = &*commands[0] else { panic!() };
        let p = parser.node_to_expr(&one("true")).unwrap();
        let ends: Vec<bool> = (0..4)
            .map(|i| {
                scaffold_query(query, Target::Index(i), &p, Arm::Provable).unwrap().ends_dead_end
            })
            .collect();
        assert_eq!(ends, vec![false, true, true, false]);
    }

    /// A goal on both branches of a switch occurs twice, and `P` has to hold
    /// before each.
    #[test]
    fn every_occurrence_gets_p() {
        let nodes = nodes(
            r#"(check-valid
                (declare-const a Int)
                (declare-const c Bool)
                (block
                    (switch
                        (block (assume c) (assume (= a 1)) (assert aid_2 ("goal") () (> a 0)))
                        (block (assume (not c)) (assume (= a 2))
                            (assert aid_2 ("goal") () (> a 0))))))"#,
        );
        let (provable, original, occurrences) =
            answers(&nodes, Target::Id(&[2]), one("(= a 1)"), Arm::Provable);
        assert_eq!(occurrences, 2);
        assert!(original);
        assert!(!provable);
        assert!(answers(&nodes, Target::Id(&[2]), one("(>= a 1)"), Arm::Provable).0);
    }

    #[test]
    fn a_missing_target_is_refused() {
        let mi = Arc::new(AirMessageInterface {});
        let parser = Parser::new(mi);
        let commands = parser.nodes_to_commands(&query()).unwrap();
        let CommandX::CheckValid(query) = &*commands[1] else { panic!() };
        let p = parser.node_to_expr(&one("true")).unwrap();
        assert!(scaffold_query(query, Target::Id(&[7]), &p, Arm::Provable).is_err());
        let ids: Vec<Vec<u64>> =
            goals(query).into_iter().map(|goal| (*goal.id.unwrap()).clone()).collect();
        assert_eq!(ids, vec![vec![0], vec![1]]);
        let seen = occurrences(query);
        assert!(seen.applications.iter().any(|(head, args)| &**head == "g" && args.len() == 1));
        assert!(seen.statement_variables.iter().any(|x| &**x == "y"));
    }
}
