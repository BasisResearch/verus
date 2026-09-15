//! Reading a proposed assertion, written as Verus source, as AIR over one
//! retained query's own names (`proof_scaffold_step`).
//!
//! Verus lowers `assert(P)` through rustc's type checker, VIR and SST. A
//! resident worker keeps none of that after compilation, only each query's
//! AIR and the source names the encoders recorded while encoding
//! (`vir::air_names`). So this module reads a spec-expression subset of
//! Verus and resolves every name against the query itself:
//!
//! - a variable is a local of the query whose recorded source name is the
//!   one written. Where shadowing left several (`x`, `x (binding 2)`), the
//!   one the query's statements use is taken, else the latest binding, and
//!   the choice is reported;
//! - a call, method call, field or index is a function, constructor or field
//!   accessor whose recorded source path ends with the path written, declared
//!   in the query's scope, with the right number of value arguments. Several
//!   candidates are narrowed to the receiver's type where the query names it
//!   (a `has_type` fact, or a monomorphic sort), then to those the query
//!   applies, then to those whose argument sorts fit. A generic function's
//!   type arguments come from the receiver's stated type, else from the
//!   query's own applications of it, so a function the query never applies
//!   cannot be called generically;
//! - values are boxed and unboxed (`I`, `%I`, `Poly%D`, ...) where sorts
//!   differ, as the encoders do, and integer arithmetic uses the prelude's
//!   `Add`, `Sub`, `Mul`, `EucDiv`, `EucMod`, so the solver's triggers see
//!   the terms Verus writes.
//!
//! Accepted: literals, `true`/`false`, paths, calls, method calls, `x.f`,
//! `x.0`, `s[i]`, `x@`, `old(x)`, `!`, unary `-`, `+ - * / %`, comparisons,
//! `==`/`!=`/`===`, `&&`, `||`, `==>`, `<==`, `<==>`, `if c { a } else { b }`,
//! and `as` to `int`, `nat` and the integer types. Anything else (closures,
//! quantifiers, `let`, `match`, turbofish, struct literals) is refused with
//! the reason. AIR type-checks the result before a solver sees it, so a
//! lowering this module gets wrong fails loudly rather than asking the
//! solver about a different claim.

use air::ast::{BinaryOp, Constant, Expr, ExprX, Ident, MultiOp, Typ, TypX, UnaryOp};
use air::context::Declared;
use air::scaffold::Occurrences;
use std::sync::Arc;
use vir::air_names::{SourceName, SourceNames, source_symbol};

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Ident(String),
    Int(String),
    Punct(&'static str),
}

/// Longest first, so `==>` is not read as `==` then `>`.
const PUNCTS: &[&str] = &[
    "<==>", "===", "==>", "<==", "=~=", "==", "!=", "<=", ">=", "&&", "||", "::", ":", "(", ")",
    "[", "]", "{", "}", ",", ".", "<", ">", "+", "-", "*", "/", "%", "!", "@", "|", "=", ";",
];

const INT_SUFFIXES: &[&str] = &[
    "int", "nat", "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128",
    "isize",
];

fn tokenize(text: &str) -> Result<Vec<Tok>, String> {
    let mut toks = Vec::new();
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
        } else if c.is_ascii_alphabetic() || c == '_' {
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            toks.push(Tok::Ident(chars[start..i].iter().collect()));
        } else if c.is_ascii_digit() {
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            let word: String = chars[start..i].iter().filter(|c| **c != '_').collect();
            let digits: String = word.chars().take_while(|c| c.is_ascii_digit()).collect();
            let suffix = &word[digits.len()..];
            if !suffix.is_empty() && !INT_SUFFIXES.contains(&suffix) {
                return Err(format!("`{word}` is not an integer literal"));
            }
            toks.push(Tok::Int(digits));
        } else {
            let rest: String = chars[i..chars.len().min(i + 4)].iter().collect();
            match PUNCTS.iter().find(|p| rest.starts_with(**p)) {
                Some(p) => {
                    toks.push(Tok::Punct(p));
                    i += p.chars().count();
                }
                None => return Err(format!("unexpected character `{c}`")),
            }
        }
    }
    Ok(toks)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    Iff,
    Implies,
    Explies,
    Or,
    And,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

#[derive(Clone, Debug, PartialEq)]
enum Ast {
    Int(String),
    Bool(bool),
    Path(Vec<String>),
    Call(Vec<String>, Vec<Ast>),
    Method(Box<Ast>, String, Vec<Ast>),
    Field(Box<Ast>, String),
    Index(Box<Ast>, Box<Ast>),
    View(Box<Ast>),
    Not(Box<Ast>),
    Neg(Box<Ast>),
    Bin(Op, Box<Ast>, Box<Ast>),
    If(Box<Ast>, Box<Ast>, Box<Ast>),
    Old(Box<Ast>),
    Cast(Box<Ast>, String),
}

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
    /// In an `if` condition, where `{` after a path opens the branch, as in
    /// Rust, not a struct literal.
    no_struct: bool,
}

impl Parser {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }

    fn is(&self, p: &str) -> bool {
        matches!(self.peek(), Some(Tok::Punct(q)) if *q == p)
    }

    fn eat(&mut self, p: &str) -> bool {
        let found = self.is(p);
        if found {
            self.pos += 1;
        }
        found
    }

    fn expect(&mut self, p: &str) -> Result<(), String> {
        if self.eat(p) { Ok(()) } else { Err(format!("expected `{p}` {}", self.here())) }
    }

    fn keyword(&self, word: &str) -> bool {
        matches!(self.peek(), Some(Tok::Ident(w)) if w == word)
    }

    fn here(&self) -> String {
        match self.peek() {
            None => "at the end".to_owned(),
            Some(Tok::Ident(w)) | Some(Tok::Int(w)) => format!("before `{w}`"),
            Some(Tok::Punct(p)) => format!("before `{p}`"),
        }
    }

    fn ident(&mut self) -> Result<String, String> {
        match self.peek().cloned() {
            Some(Tok::Ident(w)) => {
                self.pos += 1;
                Ok(w)
            }
            _ => Err(format!("expected a name {}", self.here())),
        }
    }

    fn expr(&mut self) -> Result<Ast, String> {
        let lhs = self.implies()?;
        if self.eat("<==>") {
            let rhs = self.implies()?;
            return Ok(Ast::Bin(Op::Iff, Box::new(lhs), Box::new(rhs)));
        }
        Ok(lhs)
    }

    /// `==>` groups to the right and `<==` to the left, as in Verus.
    fn implies(&mut self) -> Result<Ast, String> {
        let lhs = self.or()?;
        if self.eat("==>") {
            let rhs = self.implies()?;
            return Ok(Ast::Bin(Op::Implies, Box::new(lhs), Box::new(rhs)));
        }
        let mut lhs = lhs;
        while self.eat("<==") {
            let rhs = self.or()?;
            lhs = Ast::Bin(Op::Explies, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn or(&mut self) -> Result<Ast, String> {
        let mut lhs = self.and()?;
        while self.eat("||") {
            lhs = Ast::Bin(Op::Or, Box::new(lhs), Box::new(self.and()?));
        }
        Ok(lhs)
    }

    fn and(&mut self) -> Result<Ast, String> {
        let mut lhs = self.cmp()?;
        while self.eat("&&") {
            lhs = Ast::Bin(Op::And, Box::new(lhs), Box::new(self.cmp()?));
        }
        Ok(lhs)
    }

    fn cmp(&mut self) -> Result<Ast, String> {
        let lhs = self.add()?;
        let op = [
            ("===", Op::Eq),
            ("==", Op::Eq),
            ("!=", Op::Ne),
            ("<=", Op::Le),
            (">=", Op::Ge),
            ("<", Op::Lt),
            (">", Op::Gt),
        ]
        .into_iter()
        .find(|(p, _)| self.is(p));
        if self.is("=~=") {
            return Err("`=~=` needs its extensional-equality trait; state the equality with `==` or through the contents".to_owned());
        }
        let Some((p, op)) = op else { return Ok(lhs) };
        self.expect(p)?;
        let rhs = self.add()?;
        if ["==", "!=", "<", ">", "<=", ">="].iter().any(|p| self.is(p)) {
            return Err("comparisons do not chain; add parentheses or `&&`".to_owned());
        }
        Ok(Ast::Bin(op, Box::new(lhs), Box::new(rhs)))
    }

    fn add(&mut self) -> Result<Ast, String> {
        let mut lhs = self.mul()?;
        loop {
            let op = if self.eat("+") {
                Op::Add
            } else if self.eat("-") {
                Op::Sub
            } else {
                return Ok(lhs);
            };
            lhs = Ast::Bin(op, Box::new(lhs), Box::new(self.mul()?));
        }
    }

    fn mul(&mut self) -> Result<Ast, String> {
        let mut lhs = self.cast()?;
        loop {
            let op = if self.eat("*") {
                Op::Mul
            } else if self.eat("/") {
                Op::Div
            } else if self.eat("%") {
                Op::Mod
            } else {
                return Ok(lhs);
            };
            lhs = Ast::Bin(op, Box::new(lhs), Box::new(self.cast()?));
        }
    }

    fn cast(&mut self) -> Result<Ast, String> {
        let mut e = self.unary()?;
        while self.keyword("as") {
            self.pos += 1;
            e = Ast::Cast(Box::new(e), self.ident()?);
        }
        Ok(e)
    }

    fn unary(&mut self) -> Result<Ast, String> {
        if self.eat("!") {
            return Ok(Ast::Not(Box::new(self.unary()?)));
        }
        if self.eat("-") {
            return Ok(Ast::Neg(Box::new(self.unary()?)));
        }
        self.postfix()
    }

    /// Parse with `no_struct` set as given, restoring it after.
    fn with_no_struct<T>(
        &mut self,
        no_struct: bool,
        parse: impl FnOnce(&mut Self) -> Result<T, String>,
    ) -> Result<T, String> {
        let saved = std::mem::replace(&mut self.no_struct, no_struct);
        let result = parse(self);
        self.no_struct = saved;
        result
    }

    fn args(&mut self) -> Result<Vec<Ast>, String> {
        self.expect("(")?;
        self.with_no_struct(false, |p| {
            let mut args = Vec::new();
            if p.eat(")") {
                return Ok(args);
            }
            loop {
                args.push(p.expr()?);
                if p.eat(")") {
                    return Ok(args);
                }
                p.expect(",")?;
            }
        })
    }

    fn postfix(&mut self) -> Result<Ast, String> {
        let mut e = self.primary()?;
        loop {
            if self.eat(".") {
                match self.peek().cloned() {
                    Some(Tok::Int(n)) => {
                        self.pos += 1;
                        e = Ast::Field(Box::new(e), n);
                    }
                    _ => {
                        let name = self.ident()?;
                        if self.is("::") {
                            return Err("turbofish type arguments are not read; drop them".into());
                        }
                        e = if self.is("(") {
                            Ast::Method(Box::new(e), name, self.args()?)
                        } else {
                            Ast::Field(Box::new(e), name)
                        };
                    }
                }
            } else if self.eat("[") {
                let index = self.expr()?;
                self.expect("]")?;
                e = Ast::Index(Box::new(e), Box::new(index));
            } else if self.eat("@") {
                e = Ast::View(Box::new(e));
            } else if self.is("(") {
                return Err("only a named function can be called".to_owned());
            } else {
                return Ok(e);
            }
        }
    }

    fn primary(&mut self) -> Result<Ast, String> {
        match self.peek().cloned() {
            Some(Tok::Int(n)) => {
                self.pos += 1;
                Ok(Ast::Int(n))
            }
            Some(Tok::Punct("(")) => {
                self.pos += 1;
                let e = self.with_no_struct(false, Self::expr)?;
                if self.is(",") {
                    return Err("tuples are not read; name a field instead".to_owned());
                }
                self.expect(")")?;
                Ok(e)
            }
            Some(Tok::Punct("|")) => Err("closures are not read".to_owned()),
            Some(Tok::Ident(w)) => match w.as_str() {
                "true" | "false" => {
                    self.pos += 1;
                    Ok(Ast::Bool(w == "true"))
                }
                "old" => {
                    self.pos += 1;
                    let mut args = self.args()?;
                    if args.len() != 1 {
                        return Err("old takes one variable".to_owned());
                    }
                    Ok(Ast::Old(Box::new(args.remove(0))))
                }
                "if" => {
                    self.pos += 1;
                    let cond = self.with_no_struct(true, Self::expr)?;
                    self.expect("{")?;
                    let then = self.expr()?;
                    self.expect("}")?;
                    if !self.keyword("else") {
                        return Err("`if` needs an `else` in a spec expression".to_owned());
                    }
                    self.pos += 1;
                    let otherwise = if self.keyword("if") {
                        self.primary()?
                    } else {
                        self.expect("{")?;
                        let e = self.expr()?;
                        self.expect("}")?;
                        e
                    };
                    Ok(Ast::If(Box::new(cond), Box::new(then), Box::new(otherwise)))
                }
                "forall" | "exists" | "choose" | "let" | "match" => {
                    Err(format!("`{w}` is not read; propose a quantifier-free assertion"))
                }
                _ => {
                    let mut path = vec![self.ident()?];
                    while self.eat("::") {
                        if self.is("<") {
                            return Err("turbofish type arguments are not read; drop them".into());
                        }
                        path.push(self.ident()?);
                    }
                    if self.is("{") && path.len() > 1 && !self.no_struct {
                        return Err("struct literals are not read".to_owned());
                    }
                    if self.is("(") {
                        Ok(Ast::Call(path, self.args()?))
                    } else {
                        Ok(Ast::Path(path))
                    }
                }
            },
            _ => Err(format!("expected an expression {}", self.here())),
        }
    }
}

fn parse(text: &str) -> Result<Ast, String> {
    let mut parser = Parser { toks: tokenize(text)?, pos: 0, no_struct: false };
    // `assert(P)` and `assert(P);` as well as `P`
    if parser.keyword("assert") && matches!(parser.toks.get(1), Some(Tok::Punct("("))) {
        parser.pos += 1;
        let mut args = parser.args()?;
        parser.eat(";");
        if args.len() != 1 || parser.pos != parser.toks.len() {
            return Err("expected `assert(P)` with one expression".to_owned());
        }
        return Ok(args.remove(0));
    }
    let e = parser.expr()?;
    parser.eat(";");
    if parser.pos != parser.toks.len() {
        return Err(format!("unexpected text {}", parser.here()));
    }
    Ok(e)
}

/// What a query offers a proposed assertion to name.
pub(crate) struct Env<'a> {
    /// Source names the encoders recorded, AIR symbol -> source.
    pub names: &'a SourceNames,
    /// The crate's own name, which a `crate::` path stands for.
    pub crate_name: &'a str,
    /// The query's local constants and variables, with their sorts.
    pub locals: Vec<(Ident, Typ)>,
    /// Variables bound around the text (a quantifier's), with their sorts,
    /// which shadow the locals of the same source name.
    pub bound: Vec<(Ident, Typ)>,
    /// What the solver context has declared a global name as.
    pub declared: &'a dyn Fn(&str) -> Option<Declared>,
    /// What the query's own text uses.
    pub occurrences: &'a Occurrences,
}

/// A lowered assertion, and how its names were resolved where more than one
/// reading was possible.
pub(crate) struct Lowered {
    pub expr: Expr,
    pub choices: Vec<String>,
}

pub(crate) fn lower(text: &str, env: &Env) -> Result<Lowered, String> {
    let ast = parse(text)?;
    let mut lowerer = Lowerer { env, choices: Vec::new() };
    let (expr, typ) = lowerer.lower(&ast)?;
    let expr = lowerer
        .coerce(expr, &typ, &Arc::new(TypX::Bool))
        .map_err(|_| format!("the assertion is a {}, not a bool", sort_name(&typ)))?;
    // one note per reading, in the order they were made
    let mut seen = std::collections::HashSet::new();
    let choices = lowerer.choices.into_iter().filter(|c| seen.insert(c.clone())).collect();
    Ok(Lowered { expr, choices })
}

/// A term written as Verus source, read as `lower` reads an assertion, and
/// boxed or unboxed to `want` when that is given.
pub(crate) fn lower_term(text: &str, env: &Env, want: Option<&Typ>) -> Result<Lowered, String> {
    let ast = parse(text)?;
    let mut lowerer = Lowerer { env, choices: Vec::new() };
    let (expr, typ) = lowerer.lower(&ast)?;
    let expr = match want {
        Some(want) => lowerer.coerce(expr, &typ, want).map_err(|_| {
            format!("the term is a {}, where a {} is wanted", sort_name(&typ), sort_name(want))
        })?,
        None => expr,
    };
    let mut seen = std::collections::HashSet::new();
    let choices = lowerer.choices.into_iter().filter(|c| seen.insert(c.clone())).collect();
    Ok(Lowered { expr, choices })
}

fn sort_name(typ: &Typ) -> String {
    match &**typ {
        TypX::Bool => "bool".to_owned(),
        TypX::Int => "integer".to_owned(),
        TypX::Real => "real".to_owned(),
        TypX::Named(name) if **name == vir::def::POLY => "boxed value".to_owned(),
        TypX::Named(name) => format!("value of sort {name}"),
        TypX::Fun => "function value".to_owned(),
        TypX::BitVec(n) => format!("{n}-bit vector"),
        TypX::Float { .. } => "float".to_owned(),
    }
}

fn is_poly(typ: &Typ) -> bool {
    matches!(&**typ, TypX::Named(name) if **name == vir::def::POLY)
}

/// A stated type as the query writes it, for a message.
fn render_type(typ: &Expr) -> String {
    let printer = air::printer::Printer::new(
        Arc::new(vir::messages::VirMessageInterface {}),
        true,
        air::context::SmtSolver::Cvc5,
    );
    air::printer::node_to_string(&printer.expr_to_node(typ))
}

/// Whether a value of the stated type `typ` (`INT`, `BOOL`, `(UINT 8)`,
/// `(TYPE%vstd!seq.Seq. $ (UINT 8))`) unboxes to sort `to`; `None` when the
/// type does not say, as a type parameter does not.
fn type_fits(typ: &Expr, to: &Typ) -> Option<bool> {
    let head = match &**typ {
        ExprX::Var(name) | ExprX::Apply(name, _) => name.as_str(),
        _ => return None,
    };
    use vir::def::*;
    let integer = matches!(
        head,
        TYPE_ID_INT
            | TYPE_ID_NAT
            | TYPE_ID_USIZE
            | TYPE_ID_ISIZE
            | TYPE_ID_CHAR
            | TYPE_ID_UINT
            | TYPE_ID_SINT
            | TYPE_ID_CONST_INT
    );
    let path = head.strip_prefix(PREFIX_TYPE_ID);
    if !integer && head != TYPE_ID_BOOL && path.is_none() {
        return None;
    }
    Some(match &**to {
        TypX::Int => integer,
        TypX::Bool => head == TYPE_ID_BOOL,
        TypX::Named(sort) => path.is_some_and(|path| path == sort_base(sort)),
        _ => return None,
    })
}

/// A sort's type path: a monomorphic sort (`vstd!seq.Seq<u8.>.`) carries
/// the type arguments in angle brackets, which the path drops.
fn sort_base(sort: &str) -> String {
    let mut depth = 0usize;
    sort.chars()
        .filter(|c| {
            match c {
                '<' => depth += 1,
                '>' => depth = depth.saturating_sub(1),
                _ => return depth == 0,
            }
            false
        })
        .collect()
}

/// A source path's segments, with generic arguments dropped: `a::S<int>::f`
/// is `a`, `S`, `f`.
fn segments(path: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut current = String::new();
    let mut depth = 0usize;
    let mut chars = path.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '<' => depth += 1,
            '>' => depth = depth.saturating_sub(1),
            ':' if depth == 0 && chars.peek() == Some(&':') => {
                chars.next();
                out.push(std::mem::take(&mut current));
            }
            _ if depth == 0 => current.push(c),
            _ => {}
        }
    }
    out.push(current);
    out.into_iter().map(|s| s.trim().to_owned()).filter(|s| !s.is_empty()).collect()
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Function,
    Constructor,
    Field,
}

#[derive(Clone, Debug)]
struct Candidate {
    head: Ident,
    source: String,
    /// Leading arguments the source does not write: a decoration and a type
    /// id per type parameter (functions), or everything before the receiver
    /// (field accessors).
    type_args: usize,
    params: Vec<Typ>,
    ret: Typ,
}

struct Lowerer<'e, 'a> {
    env: &'e Env<'a>,
    choices: Vec<String>,
}

impl<'e, 'a> Lowerer<'e, 'a> {
    fn declared_fun(&self, head: &str) -> bool {
        matches!((self.env.declared)(head), Some(Declared::Fun(..)))
    }

    /// Box or unbox `expr` from one sort to another. A boxed local is not
    /// unboxed to a sort the `has_type` facts say it isn't: `%I` of a
    /// sequence would type-check and ask the solver about a different claim
    /// than the one written.
    fn coerce(&self, expr: Expr, from: &Typ, to: &Typ) -> Result<Expr, String> {
        if from == to {
            return Ok(expr);
        }
        let apply = |head: String| -> Result<Expr, String> {
            if self.declared_fun(&head) {
                Ok(Arc::new(ExprX::Apply(Arc::new(head), Arc::new(vec![expr.clone()]))))
            } else {
                Err(format!("cannot convert a {} to a {}", sort_name(from), sort_name(to)))
            }
        };
        match (&**from, &**to) {
            (_, _) if is_poly(to) => match &**from {
                TypX::Int => apply(vir::def::BOX_INT.to_owned()),
                TypX::Bool => apply(vir::def::BOX_BOOL.to_owned()),
                TypX::Real => apply(vir::def::BOX_REAL.to_owned()),
                TypX::Named(sort) => apply(format!("{}{}", vir::def::PREFIX_BOX, sort)),
                _ => Err(format!("cannot box a {}", sort_name(from))),
            },
            (_, _) if is_poly(from) => {
                if let ExprX::Var(x) = &*expr {
                    if let Some(typ) =
                        self.stated_type(x).filter(|typ| type_fits(typ, to) == Some(false))
                    {
                        let name =
                            source_symbol(self.env.names, x).unwrap_or_else(|| x.to_string());
                        return Err(format!(
                            "`{name}` is no {} (its type is {})",
                            sort_name(to),
                            render_type(typ)
                        ));
                    }
                }
                match &**to {
                    TypX::Int => apply(vir::def::UNBOX_INT.to_owned()),
                    TypX::Bool => apply(vir::def::UNBOX_BOOL.to_owned()),
                    TypX::Real => apply(vir::def::UNBOX_REAL.to_owned()),
                    TypX::Named(sort) => apply(format!("{}{}", vir::def::PREFIX_UNBOX, sort)),
                    _ => Err(format!("cannot unbox to a {}", sort_name(to))),
                }
            }
            _ => Err(format!("expected a {}, found a {}", sort_name(to), sort_name(from))),
        }
    }

    fn fits(&self, from: &Typ, to: &Typ) -> bool {
        from == to || is_poly(from) || is_poly(to)
    }

    /// Two sides made one sort: the same already, or the boxed side unboxed
    /// to the other's sort.
    fn unify(&self, a: (Expr, Typ), b: (Expr, Typ)) -> Result<(Expr, Expr, Typ), String> {
        let ((ea, ta), (eb, tb)) = (a, b);
        if ta == tb {
            return Ok((ea, eb, ta));
        }
        if is_poly(&ta) {
            return Ok((self.coerce(ea, &ta, &tb)?, eb, tb));
        }
        if is_poly(&tb) {
            return Ok((ea, self.coerce(eb, &tb, &ta)?, ta));
        }
        Err(format!("cannot compare a {} with a {}", sort_name(&ta), sort_name(&tb)))
    }

    /// A boxed local's Verus type, from the `has_type` facts the query
    /// states about it, when one is stated.
    fn stated_type(&self, x: &Ident) -> Option<&Expr> {
        self.env.occurrences.applications.iter().find_map(|(head, args)| match &args[..] {
            [value, typ] if **head == vir::def::HAS_TYPE => match &**value {
                ExprX::Var(y) if y == x => Some(typ),
                _ => None,
            },
            _ => None,
        })
    }

    /// The stated type of a boxed local, as the mangled path of its type
    /// (`vstd!seq.Seq.` from `TYPE%vstd!seq.Seq.`) and the type arguments
    /// the fact applies it to. A method of that type takes those.
    fn receiver_type(&self, receiver: &Expr) -> Option<(String, Vec<Expr>)> {
        let ExprX::Var(x) = &**receiver else { return None };
        let (head, args) = match &**self.stated_type(x)? {
            ExprX::Apply(head, args) => (head, args.to_vec()),
            ExprX::Var(head) => (head, Vec::new()),
            _ => return None,
        };
        Some((head.strip_prefix(vir::def::PREFIX_TYPE_ID)?.to_owned(), args))
    }

    /// Whether a candidate is a method of a receiver's type, when the query
    /// says that type: a boxed local's stated type or a monomorphic sort
    /// (`vstd!seq.Seq<u8.>.`) names the type, whose methods' heads start
    /// with it; a receiver that is itself a method's result (`s.subrange(i,
    /// j)`) is of that method's impl, as `s.subrange(i, j).len()` is.
    fn of_receivers_type(
        &self,
        receiver: &(Expr, Typ),
    ) -> Option<Box<dyn Fn(&Candidate) -> bool + '_>> {
        let (expr, typ) = receiver;
        if is_poly(typ) {
            if let Some((path, _)) = self.receiver_type(expr) {
                return Some(Box::new(move |c| c.head.starts_with(&path)));
            }
            let ExprX::Apply(head, _) = &**expr else { return None };
            let SourceName::Function { name, .. } = self.env.names.get(&**head)? else {
                return None;
            };
            let mut parent = segments(name);
            parent.pop()?;
            Some(Box::new(move |c| {
                let mut theirs = segments(&c.source);
                theirs.pop();
                theirs == parent
            }))
        } else if let TypX::Named(sort) = &**typ {
            let path = sort_base(sort);
            Some(Box::new(move |c| c.head.starts_with(&path)))
        } else {
            None
        }
    }

    /// An integer operand: a boxed value is unboxed, unless the query says
    /// it is no integer.
    fn int(&self, e: (Expr, Typ)) -> Result<Expr, String> {
        self.coerce(e.0, &e.1, &Arc::new(TypX::Int)).map_err(|error| {
            if error.contains("is no integer") {
                format!(
                    "{error}; arithmetic and ordering read integers only: write `a.add(b)` to \
                     concatenate, `s.len()` for a length"
                )
            } else {
                error
            }
        })
    }

    fn bool(&self, e: (Expr, Typ)) -> Result<Expr, String> {
        self.coerce(e.0, &e.1, &Arc::new(TypX::Bool))
    }

    /// Integer arithmetic through the prelude's functions, as Verus writes it.
    fn arith(&self, op: Op, a: Expr, b: Expr) -> Expr {
        let (prelude, builtin) = match op {
            Op::Add => (vir::def::ADD, Some(MultiOp::Add)),
            Op::Sub => (vir::def::SUB, Some(MultiOp::Sub)),
            Op::Mul => (vir::def::MUL, Some(MultiOp::Mul)),
            Op::Div => (vir::def::EUC_DIV, None),
            _ => (vir::def::EUC_MOD, None),
        };
        if self.declared_fun(prelude) {
            return Arc::new(ExprX::Apply(Arc::new(prelude.to_owned()), Arc::new(vec![a, b])));
        }
        match builtin {
            Some(multi) => Arc::new(ExprX::Multi(multi, Arc::new(vec![a, b]))),
            None if op == Op::Div => Arc::new(ExprX::Binary(BinaryOp::EuclideanDiv, a, b)),
            None => Arc::new(ExprX::Binary(BinaryOp::EuclideanMod, a, b)),
        }
    }

    /// The local `name` names: its recorded source name is `name`, or `name`
    /// with a binding number when shadowing renumbered it.
    fn local(&mut self, name: &str) -> Option<(Ident, Typ)> {
        for (x, typ) in &self.env.bound {
            let recorded = self
                .env
                .names
                .get(&**x)
                .map(|n| n.name().to_owned())
                .or_else(|| source_symbol(self.env.names, x));
            if **x == name || recorded.as_deref() == Some(name) {
                return Some((x.clone(), typ.clone()));
            }
        }
        let binding = format!("{name} (binding ");
        let mut found: Vec<(u64, bool, &(Ident, Typ))> = Vec::new();
        for local in &self.env.locals {
            let recorded = self
                .env
                .names
                .get(&**local.0)
                .map(|n| n.name().to_owned())
                .or_else(|| source_symbol(self.env.names, &local.0));
            let Some(recorded) = recorded else { continue };
            let number = if recorded == name {
                0
            } else if let Some(rest) = recorded.strip_prefix(&binding) {
                rest.trim_end_matches(')').parse().unwrap_or(0)
            } else {
                continue;
            };
            let used = self.env.occurrences.statement_variables.contains(&local.0);
            found.push((number, used, local));
        }
        // used by the statements first, then the latest binding
        found.sort_by_key(|f| std::cmp::Reverse((f.1, f.0)));
        let (_, _, chosen) = found.first()?;
        if found.len() > 1 {
            self.choices.push(format!(
                "`{name}` read as {} (of {} bindings: the one the query uses, else the latest)",
                chosen.0,
                found.len()
            ));
        }
        Some((chosen.0.clone(), chosen.1.clone()))
    }

    fn written_path(&self, path: &[String]) -> Vec<String> {
        match path.first().map(String::as_str) {
            Some("crate") => {
                let mut out = segments(self.env.crate_name);
                out.extend(path[1..].iter().cloned());
                out
            }
            _ => path.to_vec(),
        }
    }

    /// Every declared function, constructor or accessor whose recorded name
    /// ends with `path`, sorted by head for a stable order.
    fn candidates(&self, path: &[String], kinds: &[Kind]) -> Vec<Candidate> {
        let mut out = Vec::new();
        for (head, name) in self.env.names.iter() {
            let (kind, source, type_args) = match name {
                SourceName::Function { name, type_args } => (Kind::Function, name, *type_args),
                SourceName::Constructor { name, .. } => (Kind::Constructor, name, 0),
                SourceName::Field(field) => (Kind::Field, field, 0),
                _ => continue,
            };
            if !kinds.contains(&kind) {
                continue;
            }
            let segs = segments(source);
            if segs.len() < path.len() || segs[segs.len() - path.len()..] != *path {
                continue;
            }
            let Some(Declared::Fun(params, ret)) = (self.env.declared)(head) else { continue };
            let params: Vec<Typ> = params.iter().cloned().collect();
            let type_args = match kind {
                Kind::Field if params.is_empty() => continue,
                Kind::Field => params.len() - 1,
                _ => type_args,
            };
            if params.len() < type_args {
                continue;
            }
            out.push(Candidate {
                head: Arc::new(head.clone()),
                source: source.clone(),
                type_args,
                params,
                ret,
            });
        }
        out.sort_by(|a, b| a.head.cmp(&b.head));
        out
    }

    fn applied(&self, head: &Ident) -> impl Iterator<Item = &air::ast::Exprs> {
        self.env.occurrences.applications.iter().filter(move |(h, _)| h == head).map(|(_, a)| a)
    }

    /// Apply the one candidate for `written` that takes `args`, taking type
    /// arguments from the query's own applications of it.
    fn apply(
        &mut self,
        written: &str,
        mut candidates: Vec<Candidate>,
        args: Vec<(Expr, Typ)>,
    ) -> Result<(Expr, Typ), String> {
        if candidates.is_empty() {
            return Err(format!(
                "no function, constructor or field `{written}` is declared where this query is checked"
            ));
        }
        let arity: Vec<Candidate> = candidates
            .iter()
            .filter(|c| c.params.len() - c.type_args == args.len())
            .cloned()
            .collect();
        if arity.is_empty() {
            let takes: Vec<String> = candidates
                .iter()
                .map(|c| format!("{} takes {}", c.source, c.params.len() - c.type_args))
                .collect();
            return Err(format!(
                "`{written}` is given {} argument(s): {}",
                args.len(),
                takes.join("; ")
            ));
        }
        candidates = arity;
        if candidates.len() > 1 {
            // A receiver whose type the query names takes that type's
            // methods: `s.len()` is `Seq::len`, not `Set::len`.
            if let Some(of_type) = args.first().and_then(|r| self.of_receivers_type(r)) {
                let of_type: Vec<Candidate> =
                    candidates.iter().filter(|c| of_type(c)).cloned().collect();
                if !of_type.is_empty() {
                    candidates = of_type;
                }
            }
        }
        // What the query applies, or which sorts fit, is a guess at the
        // reading, and the note says it was one. Spellings of one operation of
        // one type (`spec_index` and `index`) are no choice between readings.
        let mut guessed: Option<(&'static str, usize)> = None;
        let one_type = |candidates: &[Candidate]| {
            let parent = |c: &Candidate| {
                let mut segs = segments(&c.source);
                segs.pop();
                segs
            };
            candidates.iter().all(|c| parent(c) == parent(&candidates[0]))
        };
        if candidates.len() > 1 {
            let used: Vec<Candidate> = candidates
                .iter()
                .filter(|c| self.applied(&c.head).next().is_some())
                .cloned()
                .collect();
            if !used.is_empty() {
                if used.len() < candidates.len() && !one_type(&candidates) {
                    guessed = Some(("the one this query applies", candidates.len()));
                }
                candidates = used;
            }
        }
        if candidates.len() > 1 {
            let fitting: Vec<Candidate> = candidates
                .iter()
                .filter(|c| {
                    args.iter().zip(&c.params[c.type_args..]).all(|((_, t), p)| self.fits(t, p))
                })
                .cloned()
                .collect();
            if !fitting.is_empty() {
                if fitting.len() < candidates.len() && !one_type(&candidates) {
                    guessed.get_or_insert(("the one whose parameter sorts fit", candidates.len()));
                }
                candidates = fitting;
            }
        }
        if candidates.len() > 1 {
            // A field has a plain accessor and an internal `/?` twin; source
            // field access is encoded with the plain one.
            let plain: Vec<Candidate> =
                candidates.iter().filter(|c| !c.head.contains("/?")).cloned().collect();
            if !plain.is_empty() {
                candidates = plain;
            }
        }
        if candidates.len() > 1 {
            // Fields and tuple positions share their source names across
            // datatypes; the solver's symbol tells them apart.
            let names: Vec<String> = candidates
                .iter()
                .map(|c| {
                    let shared = candidates.iter().filter(|d| d.source == c.source).count() > 1;
                    if shared { format!("{} ({})", c.source, c.head) } else { c.source.clone() }
                })
                .collect();
            return Err(format!(
                "`{written}` could be any of {}; write more of the path",
                names.join(", ")
            ));
        }
        let c = candidates.remove(0);
        if let Some((how, of)) = guessed {
            self.choices.push(format!(
                "`{written}` read as {}, of {of} candidates {how}; check lowered_as if the \
                 arguments have another type",
                c.source
            ));
        } else if c.source != written
            && written != format!(".{}", c.source)
            && !c.source.ends_with(&format!("::{written}"))
        {
            self.choices.push(format!("`{written}` read as {}", c.source));
        }
        let mut values = Vec::new();
        for ((expr, typ), param) in args.into_iter().zip(&c.params[c.type_args..]) {
            values.push(
                self.coerce(expr, &typ, param)
                    .map_err(|e| format!("an argument of {}: {e}", c.source))?,
            );
        }
        let mut full: Vec<Expr> = Vec::new();
        if c.type_args > 0 {
            full.extend(self.type_args(&c, &values)?);
        }
        full.extend(values);
        Ok((Arc::new(ExprX::Apply(c.head.clone(), Arc::new(full))), c.ret.clone()))
    }

    /// A generic candidate's type arguments, from the query's applications of
    /// it. Only applications whose arguments are boxed as these are, where
    /// these are boxed, can lend them: a box names the value's sort, so
    /// `(Poly%Seq<u8.>. s)` takes the type arguments of `(Poly%Seq<u8.>. v)`,
    /// and an integer boxed with `I` those of no sequence. Among those, the
    /// only type arguments they use, or those of an application to the same
    /// values, or failing that to the same first value.
    fn type_args(&mut self, c: &Candidate, values: &[Expr]) -> Result<Vec<Expr>, String> {
        // A boxed receiver whose type the query states, `(has_type s (TYPE%T
        // args))`, gives a method of `T` the type's own arguments.
        if let Some((typ, args)) = values.first().and_then(|v| self.receiver_type(v)) {
            if c.head.starts_with(&typ) && args.len() == c.type_args {
                return Ok(args);
            }
        }
        // A receiver that is itself an application of a method of the same
        // impl, such as `s.subrange(i, j)` under `.len()`, carries the
        // impl's type arguments.
        if let Some(ExprX::Apply(head, args)) = values.first().map(|v| &**v) {
            if let Some(SourceName::Function { name, type_args }) = self.env.names.get(&**head) {
                let (theirs, mine) = (segments(name), segments(&c.source));
                if *type_args == c.type_args
                    && args.len() >= c.type_args
                    && theirs.len() == mine.len()
                    && theirs[..theirs.len() - 1] == mine[..mine.len() - 1]
                {
                    return Ok(args[..c.type_args].to_vec());
                }
            }
        }
        let key = |es: &[Expr]| format!("{:?}", es);
        let box_of = |e: &Expr| match &**e {
            ExprX::Apply(head, args)
                if args.len() == 1
                    && ([vir::def::BOX_INT, vir::def::BOX_BOOL, vir::def::BOX_REAL]
                        .contains(&head.as_str())
                        || head.starts_with(vir::def::PREFIX_BOX)) =>
            {
                Some(head.clone())
            }
            _ => None,
        };
        let ours: Vec<Option<Ident>> = values.iter().map(box_of).collect();
        let mut seen: Vec<(String, Vec<Expr>, Vec<Expr>)> = Vec::new();
        let mut applied_at_all = false;
        for args in self.applied(&c.head) {
            if args.len() != c.type_args + values.len() {
                continue;
            }
            applied_at_all = true;
            let prefix = args[..c.type_args].to_vec();
            let rest = args[c.type_args..].to_vec();
            let alike = ours.iter().zip(&rest).all(|(o, r)| o.is_none() || *o == box_of(r));
            if alike {
                seen.push((key(&prefix), prefix, rest));
            }
        }
        let mut distinct: Vec<&(String, Vec<Expr>, Vec<Expr>)> = Vec::new();
        for s in &seen {
            if !distinct.iter().any(|d| d.0 == s.0) {
                distinct.push(s);
            }
        }
        if distinct.is_empty() {
            if let Some(borrowed) = self.sibling_type_args(c, &ours) {
                return Ok(borrowed);
            }
        }
        match distinct.len() {
            0 if !applied_at_all => Err(format!(
                "{} is generic, and this query never applies it, so its type arguments are unknown",
                c.source
            )),
            0 => Err(format!(
                "{} is generic, and this query applies it only to values of other types, so its \
                 type arguments for these are unknown",
                c.source
            )),
            1 => {
                if !seen.iter().any(|s| key(&s.2) == key(values)) {
                    self.choices.push(format!(
                        "{} took the type arguments this query applies it with to other values; \
                         check lowered_as if these have another type",
                        c.source
                    ));
                }
                Ok(distinct[0].1.clone())
            }
            n => {
                let same = seen.iter().find(|s| key(&s.2) == key(values));
                let first = seen.iter().find(|s| {
                    !s.2.is_empty() && !values.is_empty() && key(&s.2[..1]) == key(&values[..1])
                });
                match same.or(first) {
                    Some(s) => {
                        self.choices.push(format!(
                            "{} is applied at {n} types in this query; took those of an application to the same {}",
                            c.source,
                            if same.is_some() { "arguments" } else { "receiver" }
                        ));
                        Ok(s.1.clone())
                    }
                    None => Err(format!(
                        "{} is applied at {n} types in this query and none to these arguments; its type arguments are ambiguous",
                        c.source
                    )),
                }
            }
        }
    }

    /// Type arguments for a generic method the query never applies to a
    /// value boxed like this receiver, from a sibling it does: a function
    /// of the same impl or type (the same path but for the last segment)
    /// taking as many type arguments, applied to a receiver boxed the same
    /// way. Methods of one generic impl take the impl's type arguments, so
    /// `s.len()` borrows those of `s[0]` (`Seq::index`). Only the receiver's
    /// box is compared, and the borrowing is reported in `choices`.
    fn sibling_type_args(&mut self, c: &Candidate, ours: &[Option<Ident>]) -> Option<Vec<Expr>> {
        let receiver = ours.first()?.as_ref()?;
        let segs = segments(&c.source);
        let parent = &segs[..segs.len().checked_sub(1)?];
        let mut found: Option<(String, Vec<Expr>)> = None;
        for (head, args) in &self.env.occurrences.applications {
            let Some(SourceName::Function { name, type_args }) = self.env.names.get(&**head) else {
                continue;
            };
            let sibling = segments(name);
            if *type_args != c.type_args
                || sibling.len() != segs.len()
                || sibling[..sibling.len() - 1] != *parent
                || args.len() <= c.type_args
            {
                continue;
            }
            let boxed_alike = matches!(&*args[c.type_args],
                ExprX::Apply(h, a) if a.len() == 1 && h == receiver);
            if boxed_alike {
                let prefix = args[..c.type_args].to_vec();
                match &found {
                    None => found = Some((name.clone(), prefix)),
                    // siblings at two different types: no single answer
                    Some((_, seen)) if format!("{seen:?}") != format!("{prefix:?}") => return None,
                    Some(_) => {}
                }
            }
        }
        let (sibling, prefix) = found?;
        self.choices.push(format!(
            "{} is not applied to this receiver's type in this query; took the type arguments \
             {sibling} is applied with",
            c.source
        ));
        Some(prefix)
    }

    fn lower(&mut self, ast: &Ast) -> Result<(Expr, Typ), String> {
        let int = || Arc::new(TypX::Int);
        let boolean = || Arc::new(TypX::Bool);
        match ast {
            Ast::Int(n) => Ok((Arc::new(ExprX::Const(Constant::Nat(Arc::new(n.clone())))), int())),
            Ast::Bool(b) => Ok((Arc::new(ExprX::Const(Constant::Bool(*b))), boolean())),
            Ast::Path(path) => {
                if let [name] = &path[..] {
                    if let Some((x, typ)) = self.local(name) {
                        return Ok((Arc::new(ExprX::Var(x)), typ));
                    }
                }
                let written = path.join("::");
                let path = self.written_path(path);
                let candidates = self.candidates(&path, &[Kind::Function, Kind::Constructor]);
                if candidates.is_empty() && path.len() == 1 {
                    return Err(format!(
                        "no variable or constant `{written}` is in scope of this query"
                    ));
                }
                self.apply(&written, candidates, Vec::new())
            }
            Ast::Call(path, args) => {
                let args = args.iter().map(|a| self.lower(a)).collect::<Result<Vec<_>, _>>()?;
                let written = path.join("::");
                let path = self.written_path(path);
                let candidates = self.candidates(&path, &[Kind::Function, Kind::Constructor]);
                self.apply(&written, candidates, args)
            }
            Ast::Method(receiver, name, args) => {
                let mut all = vec![self.lower(receiver)?];
                for a in args {
                    all.push(self.lower(a)?);
                }
                let candidates = self.candidates(std::slice::from_ref(name), &[Kind::Function]);
                self.apply(name, candidates, all)
            }
            Ast::View(receiver) => {
                let receiver = self.lower(receiver)?;
                let candidates = self.candidates(&["view".to_owned()], &[Kind::Function]);
                self.apply("view (@)", candidates, vec![receiver])
            }
            Ast::Index(receiver, index) => {
                let receiver = self.lower(receiver)?;
                let index = self.lower(index)?;
                // `s[i]` is `spec_index`, which Verus usually inlines to
                // `index`: both are candidates, and the query's own
                // applications tell which one it uses.
                let mut candidates = self.candidates(&["spec_index".to_owned()], &[Kind::Function]);
                candidates.extend(self.candidates(&["index".to_owned()], &[Kind::Function]));
                self.apply("index ([])", candidates, vec![receiver, index])
            }
            Ast::Field(receiver, field) => {
                let receiver = self.lower(receiver)?;
                let candidates = self.candidates(std::slice::from_ref(field), &[Kind::Field]);
                self.apply(&format!(".{field}"), candidates, vec![receiver])
            }
            Ast::Not(e) => {
                let e = self.lower(e)?;
                Ok((Arc::new(ExprX::Unary(UnaryOp::Not, self.bool(e)?)), boolean()))
            }
            Ast::Neg(e) => {
                let e = self.lower(e)?;
                let zero = Arc::new(ExprX::Const(Constant::Nat(Arc::new("0".to_owned()))));
                Ok((self.arith(Op::Sub, zero, self.int(e)?), int()))
            }
            Ast::Old(e) => match &**e {
                Ast::Path(path) if path.len() == 1 => match self.local(&path[0]) {
                    Some((x, typ)) => Ok((
                        Arc::new(ExprX::Old(vir::def::snapshot_ident(vir::def::SNAPSHOT_PRE), x)),
                        typ,
                    )),
                    None => Err(format!("`{}` is no variable of this query", path[0])),
                },
                _ => Err("old takes a variable".to_owned()),
            },
            Ast::If(c, t, e) => {
                let c = self.lower(c)?;
                let c = self.bool(c)?;
                let t = self.lower(t)?;
                let e = self.lower(e)?;
                let (t, e, typ) = self.unify(t, e)?;
                Ok((Arc::new(ExprX::IfElse(c, t, e)), typ))
            }
            Ast::Cast(e, target) => {
                let e = self.lower(e)?;
                let e =
                    self.int(e).map_err(|_| format!("only integers are cast, to `{target}`"))?;
                let clip = |head: &str, mut args: Vec<Expr>| -> Result<(Expr, Typ), String> {
                    if !self.declared_fun(head) {
                        return Err(format!(
                            "`as {target}` needs {head}, which is not declared here"
                        ));
                    }
                    args.push(e.clone());
                    Ok((Arc::new(ExprX::Apply(Arc::new(head.to_owned()), Arc::new(args))), int()))
                };
                let width = |bits: &str| -> Expr {
                    if bits == "size" {
                        Arc::new(ExprX::Var(Arc::new(vir::def::ARCH_SIZE.to_owned())))
                    } else {
                        Arc::new(ExprX::Const(Constant::Nat(Arc::new(bits.to_owned()))))
                    }
                };
                match target.as_str() {
                    "int" => Ok((e.clone(), int())),
                    "nat" => clip(vir::def::NAT_CLIP, vec![]),
                    t if t.starts_with('u') && INT_SUFFIXES.contains(&t) => {
                        clip(vir::def::U_CLIP, vec![width(&t[1..])])
                    }
                    t if t.starts_with('i') && INT_SUFFIXES.contains(&t) => {
                        clip(vir::def::I_CLIP, vec![width(&t[1..])])
                    }
                    _ => Err(format!(
                        "`as {target}` is not read; cast to int, nat or an integer type"
                    )),
                }
            }
            Ast::Bin(op, a, b) => {
                let a = self.lower(a)?;
                let b = self.lower(b)?;
                match op {
                    Op::And | Op::Or => {
                        let multi = if *op == Op::And { MultiOp::And } else { MultiOp::Or };
                        let (a, b) = (self.bool(a)?, self.bool(b)?);
                        Ok((Arc::new(ExprX::Multi(multi, Arc::new(vec![a, b]))), boolean()))
                    }
                    Op::Implies | Op::Explies => {
                        let (a, b) = (self.bool(a)?, self.bool(b)?);
                        let (lhs, rhs) = if *op == Op::Implies { (a, b) } else { (b, a) };
                        Ok((Arc::new(ExprX::Binary(BinaryOp::Implies, lhs, rhs)), boolean()))
                    }
                    Op::Iff => {
                        let (a, b) = (self.bool(a)?, self.bool(b)?);
                        Ok((Arc::new(ExprX::Binary(BinaryOp::Eq, a, b)), boolean()))
                    }
                    Op::Eq | Op::Ne => {
                        let (a, b, typ) = self.unify(a, b)?;
                        let primitive = matches!(&*typ, TypX::Int | TypX::Bool | TypX::Real);
                        const EXT: &str = "`==` between non-primitive values is checked as plain \
                            equality; Verus's own assert(a == b) on sequences, sets and maps also \
                            tries extensional equality, so it can prove what this check cannot";
                        if !primitive && !self.choices.iter().any(|c| c == EXT) {
                            self.choices.push(EXT.to_owned());
                        }
                        let eq = Arc::new(ExprX::Binary(BinaryOp::Eq, a, b));
                        Ok((
                            if *op == Op::Eq {
                                eq
                            } else {
                                Arc::new(ExprX::Unary(UnaryOp::Not, eq))
                            },
                            boolean(),
                        ))
                    }
                    Op::Lt | Op::Le | Op::Gt | Op::Ge => {
                        let (a, b) = (self.int(a)?, self.int(b)?);
                        let bin = match op {
                            Op::Lt => BinaryOp::Lt,
                            Op::Le => BinaryOp::Le,
                            Op::Gt => BinaryOp::Gt,
                            _ => BinaryOp::Ge,
                        };
                        Ok((Arc::new(ExprX::Binary(bin, a, b)), boolean()))
                    }
                    Op::Add
                        if [&a.1, &b.1]
                            .iter()
                            .any(|t| matches!(&***t, TypX::Named(_)) && !is_poly(t)) =>
                    {
                        // `+` on sequences is `spec_add`, which Verus writes
                        // as `Seq::add`; the query's applications tell which.
                        let mut candidates =
                            self.candidates(&["spec_add".to_owned()], &[Kind::Function]);
                        candidates.extend(self.candidates(&["add".to_owned()], &[Kind::Function]));
                        self.apply("+ (add)", candidates, vec![a, b])
                    }
                    Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Mod => {
                        let (a, b) = (self.int(a)?, self.int(b)?);
                        Ok((self.arith(*op, a, b), int()))
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn precedence_follows_verus() {
        let e = parse("a ==> b ==> c || d && x + 1 * 2 < y as int").unwrap();
        let Ast::Bin(Op::Implies, _, rest) = e else { panic!("{e:?}") };
        let Ast::Bin(Op::Implies, _, rest) = *rest else { panic!() };
        let Ast::Bin(Op::Or, _, rest) = *rest else { panic!() };
        let Ast::Bin(Op::And, _, rest) = *rest else { panic!() };
        let Ast::Bin(Op::Lt, sum, cast) = *rest else { panic!() };
        assert!(
            matches!(*sum, Ast::Bin(Op::Add, _, ref p) if matches!(**p, Ast::Bin(Op::Mul, ..)))
        );
        assert!(matches!(*cast, Ast::Cast(_, ref t) if t == "int"));
        assert_eq!(parse("assert(x > 0);").unwrap(), parse("x > 0").unwrap());
        assert!(matches!(parse("s@.len() == 3u64").unwrap(), Ast::Bin(Op::Eq, ..)));
    }

    #[test]
    fn unread_forms_say_why() {
        for (text, reason) in [
            ("forall|i| i > 0", "quantifier-free"),
            ("a < b < c", "chain"),
            ("f::<int>(x)", "turbofish"),
            ("(a, b)", "tuples"),
            ("a =~= b", "extensional"),
            ("if a { b }", "else"),
            ("x > 0 y", "unexpected text"),
        ] {
            let error = parse(text).unwrap_err();
            assert!(error.contains(reason), "{text}: {error}");
        }
    }

    /// A tiny query: `x: int` (param `x!`), `v: Poly` (`v!`), shadowed `n`,
    /// a spec `f(int) -> int` over boxes, and a generic `len` applied at one
    /// type in the query.
    fn env_parts() -> (SourceNames, Vec<(Ident, Typ)>, Occurrences) {
        let mut names = SourceNames::new();
        let sym = |s: &str| SourceName::Symbol(s.to_owned());
        names.insert("x!".into(), sym("x"));
        names.insert("v!".into(), sym("v"));
        names.insert("n@".into(), sym("n"));
        names.insert("n$2@".into(), sym("n (binding 2)"));
        names.insert("s!".into(), sym("s"));
        names.insert("t!".into(), sym("t"));
        names.insert("k!f.?".into(), SourceName::Function { name: "k::f".into(), type_args: 0 });
        names.insert(
            "vstd!seq.Seq.index.?".into(),
            SourceName::Function { name: "vstd::seq::Seq::index".into(), type_args: 2 },
        );
        names.insert(
            "vstd!seq.Seq.add.?".into(),
            SourceName::Function { name: "vstd::seq::Seq::add".into(), type_args: 2 },
        );
        names.insert(
            "vstd!seq.Seq.len.?".into(),
            SourceName::Function { name: "vstd::seq::Seq::len".into(), type_args: 2 },
        );
        names.insert(
            "vstd!set.Set.len.?".into(),
            SourceName::Function { name: "vstd::set::Set::len".into(), type_args: 2 },
        );
        names.insert("Add".into(), SourceName::Operator("+".into()));
        // a struct `P` with field `x` (its plain accessor and the `/?` twin),
        // another struct `Q` with a field `x`, and a pair's first position
        names.insert("k!P./P/x".into(), SourceName::Field("x".into()));
        names.insert("k!P./P/?x".into(), SourceName::Field("x".into()));
        names.insert("k!Q./Q/x".into(), SourceName::Field("x".into()));
        names.insert("tuple%2./tuple%2/0".into(), SourceName::Field("0".into()));
        names.insert("p!".into(), sym("p"));
        names.insert("q!".into(), sym("q"));
        names.insert(
            "vstd!view.View.view.?".into(),
            SourceName::Function { name: "vstd::view::View::view".into(), type_args: 2 },
        );
        let int: Typ = Arc::new(TypX::Int);
        let poly: Typ = Arc::new(TypX::Named(Arc::new("Poly".into())));
        let locals = vec![
            (Arc::new("p!".to_owned()), Arc::new(TypX::Named(Arc::new("k!P.".into())))),
            (Arc::new("q!".to_owned()), Arc::new(TypX::Named(Arc::new("tuple%2.".into())))),
            (Arc::new("x!".to_owned()), int.clone()),
            (Arc::new("v!".to_owned()), poly),
            (Arc::new("n@".to_owned()), int.clone()),
            (Arc::new("n$2@".to_owned()), int),
            (Arc::new("s!".to_owned()), Arc::new(TypX::Named(Arc::new("Poly".into())))),
            // a sequence local, in the monomorphic sort Verus declares it with
            (
                Arc::new("t!".to_owned()),
                Arc::new(TypX::Named(Arc::new("vstd!seq.Seq<u8.>.".into()))),
            ),
        ];
        let dcr = Arc::new(ExprX::Var(Arc::new("$".to_owned())));
        let ty = Arc::new(ExprX::Var(Arc::new("NAT".to_owned())));
        let v = Arc::new(ExprX::Var(Arc::new("v!".to_owned())));
        let mut occurrences = Occurrences::default();
        occurrences
            .applications
            .push((Arc::new("vstd!seq.Seq.len.?".to_owned()), Arc::new(vec![dcr, ty, v])));
        // a set's length too, so `len` alone names two applied methods
        occurrences.applications.push((
            Arc::new("vstd!set.Set.len.?".to_owned()),
            Arc::new(vec![
                Arc::new(ExprX::Var(Arc::new("$".to_owned()))),
                Arc::new(ExprX::Var(Arc::new("INT".to_owned()))),
                Arc::new(ExprX::Var(Arc::new("w!".to_owned()))),
            ]),
        ));
        occurrences.statement_variables.insert(Arc::new("n$2@".to_owned()));
        occurrences.applications.push((
            Arc::new("vstd!view.View.view.?".to_owned()),
            Arc::new(vec![
                Arc::new(ExprX::Var(Arc::new("$".to_owned()))),
                Arc::new(ExprX::Var(Arc::new("NAT".to_owned()))),
                Arc::new(ExprX::Var(Arc::new("v!".to_owned()))),
            ]),
        ));
        // `s` is stated to be a sequence; `v` is boxed with no type stated
        let var = |x: &str| Arc::new(ExprX::Var(Arc::new(x.to_owned())));
        let seq_type = Arc::new(ExprX::Apply(
            Arc::new("TYPE%vstd!seq.Seq.".to_owned()),
            Arc::new(vec![var("$"), var("NAT")]),
        ));
        occurrences
            .applications
            .push((Arc::new("has_type".to_owned()), Arc::new(vec![var("s!"), seq_type])));
        // the query indexes `t`, so `Seq::index` is applied at `t`'s type
        let apply = |head: &str, args: Vec<Expr>| {
            Arc::new(ExprX::Apply(Arc::new(head.to_owned()), Arc::new(args)))
        };
        let nat = |n: &str| Arc::new(ExprX::Const(Constant::Nat(Arc::new(n.to_owned()))));
        occurrences.applications.push((
            Arc::new("vstd!seq.Seq.index.?".to_owned()),
            Arc::new(vec![
                var("$"),
                apply("UINT", vec![nat("8")]),
                apply("Poly%vstd!seq.Seq<u8.>.", vec![var("t!")]),
                apply("I", vec![nat("0")]),
            ]),
        ));
        (names, locals, occurrences)
    }

    fn declared(name: &str) -> Option<Declared> {
        let int: Typ = Arc::new(TypX::Int);
        let poly: Typ = Arc::new(TypX::Named(Arc::new("Poly".into())));
        let t: Typ = Arc::new(TypX::Named(Arc::new("Type".into())));
        let dcr: Typ = Arc::new(TypX::Named(Arc::new("Dcr".into())));
        let fun = |params: Vec<Typ>, ret: &Typ| Some(Declared::Fun(Arc::new(params), ret.clone()));
        match name {
            "k!f.?" => fun(vec![poly.clone()], &int),
            "vstd!seq.Seq.len.?" => fun(vec![dcr.clone(), t.clone(), poly.clone()], &int),
            "vstd!seq.Seq.index.?" => {
                fun(vec![dcr.clone(), t.clone(), poly.clone(), poly.clone()], &poly)
            }
            "vstd!seq.Seq.add.?" => {
                fun(vec![dcr.clone(), t.clone(), poly.clone(), poly.clone()], &poly)
            }
            "vstd!set.Set.len.?" => fun(vec![dcr, t, poly.clone()], &int),
            "Poly%vstd!seq.Seq<u8.>." => {
                fun(vec![Arc::new(TypX::Named(Arc::new("vstd!seq.Seq<u8.>.".into())))], &poly)
            }
            "Add" => fun(vec![int.clone(), int.clone()], &int),
            "I" => fun(vec![int.clone()], &poly),
            "%I" => fun(vec![poly.clone()], &int),
            "k!P./P/x" | "k!P./P/?x" => {
                fun(vec![Arc::new(TypX::Named(Arc::new("k!P.".into())))], &int)
            }
            "k!Q./Q/x" => fun(vec![Arc::new(TypX::Named(Arc::new("k!Q.".into())))], &int),
            "tuple%2./tuple%2/0" => {
                fun(vec![Arc::new(TypX::Named(Arc::new("tuple%2.".into())))], &poly)
            }
            "vstd!view.View.view.?" => fun(vec![dcr.clone(), t.clone(), poly.clone()], &poly),
            vir::def::NAT_CLIP => fun(vec![int.clone()], &int),
            vir::def::U_CLIP | vir::def::I_CLIP => fun(vec![int.clone(), int.clone()], &int),
            _ => None,
        }
    }

    fn lowered(text: &str) -> Result<(String, Vec<String>), String> {
        let (names, locals, occurrences) = env_parts();
        let env = Env {
            names: &names,
            crate_name: "k",
            locals,
            bound: Vec::new(),
            declared: &declared,
            occurrences: &occurrences,
        };
        let printer = air::printer::Printer::new(
            Arc::new(vir::messages::VirMessageInterface {}),
            true,
            air::context::SmtSolver::Cvc5,
        );
        lower(text, &env).map(|l| {
            // the printer wraps long terms; compare them on one line
            let text = air::printer::node_to_string(&printer.expr_to_node(&l.expr));
            let flat = text.split_whitespace().collect::<Vec<_>>().join(" ");
            (flat.replace(" )", ")"), l.choices)
        })
    }

    #[test]
    fn names_resolve_and_values_are_boxed() {
        let (smt, _) = lowered("f(x + 1) > x").unwrap();
        assert_eq!(smt, "(> (k!f.? (I (Add x! 1))) x!)");
        let (smt, _) = lowered("crate::f(x) == 0").unwrap();
        assert_eq!(smt, "(= (k!f.? (I x!)) 0)");
        // the shadowing binding the statements use
        let (smt, choices) = lowered("n == 2").unwrap();
        assert_eq!(smt, "(= n$2@ 2)");
        assert_eq!(choices.len(), 1, "{choices:?}");
    }

    /// `s` is stated to be a `Seq<nat>`: `s.len()` is `Seq::len`, not the
    /// `Set::len` the query also applies, at the stated type arguments. `v`
    /// is boxed with no type stated, so `len` is ambiguous for it.
    #[test]
    fn a_stated_type_picks_the_method_and_its_type_arguments() {
        let (smt, choices) = lowered("s.len() >= 0").unwrap();
        assert_eq!(smt, "(>= (vstd!seq.Seq.len.? $ NAT s!) 0)");
        assert!(choices.is_empty(), "{choices:?}");
        let error = lowered("v.len() >= 0").unwrap_err();
        assert!(error.contains("could be any of"), "{error}");
        // named in full, the type arguments come from the query's application
        let (smt, _) = lowered("Seq::len(v) >= 0").unwrap();
        assert_eq!(smt, "(>= (vstd!seq.Seq.len.? $ NAT v!) 0)");
    }

    /// Verus declares a sequence local in a monomorphic sort and boxes it at
    /// generic calls. `t.len()` is applied nowhere, so it borrows the type
    /// arguments of `Seq::index`, which the query applies to a receiver
    /// boxed the same way; `t[i]` reads as `Seq::index` itself.
    #[test]
    fn a_sibling_lends_type_arguments_and_brackets_read_index() {
        let (smt, choices) = lowered("t.len() >= 0").unwrap();
        assert_eq!(smt, "(>= (vstd!seq.Seq.len.? $ (UINT 8) (Poly%vstd!seq.Seq<u8.>. t!)) 0)");
        assert!(choices.iter().any(|c| c.contains("Seq::index")), "{choices:?}");
        // `+` on sequences is `Seq::add`, whose result carries `add`'s type
        // arguments into `.len()`
        let (smt, _) = lowered("(t + t).len() >= 0").unwrap();
        let boxed = "(Poly%vstd!seq.Seq<u8.>. t!)";
        assert_eq!(
            smt,
            format!(
                "(>= (vstd!seq.Seq.len.? $ (UINT 8) (vstd!seq.Seq.add.? $ (UINT 8) {boxed} {boxed})) 0)"
            )
        );
        let (smt, _) = lowered("t[0] == 1").unwrap();
        assert_eq!(
            smt,
            "(= (%I (vstd!seq.Seq.index.? $ (UINT 8) (Poly%vstd!seq.Seq<u8.>. t!) (I 0))) 1)"
        );
    }

    /// A field is the plain accessor of the receiver's datatype, not the
    /// `/?` twin nor another datatype's field of the same name; a pair's
    /// position is an accessor too, its boxed value unboxed where compared.
    #[test]
    fn fields_read_the_receivers_accessor() {
        let (smt, choices) = lowered("p.x == 1").unwrap();
        assert_eq!(smt, "(= (k!P./P/x p!) 1)");
        assert!(choices.is_empty(), "{choices:?}");
        let (smt, _) = lowered("q.0 == 1").unwrap();
        assert_eq!(smt, "(= (%I (tuple%2./tuple%2/0 q!)) 1)");
    }

    /// `old`, `@` and casts, as Verus writes them in a function body.
    #[test]
    fn old_view_and_casts() {
        let (smt, _) = lowered("old(n) < n").unwrap();
        assert_eq!(smt, "(< (old snap%PRE n$2@) n$2@)");
        let (smt, _) = lowered("v@ == s").unwrap();
        assert_eq!(smt, "(= (vstd!view.View.view.? $ NAT v!) s!)");
        let (smt, _) = lowered("x as nat >= 0").unwrap();
        assert_eq!(smt, "(>= (nClip x!) 0)");
        let (smt, _) = lowered("x as u8 < 256").unwrap();
        assert_eq!(smt, "(< (uClip 8 x!) 256)");
        let (smt, _) = lowered("x as i32 < 0 || x as usize >= 0").unwrap();
        assert_eq!(smt, "(or (< (iClip 32 x!) 0) (>= (uClip SZ x!) 0))");
        let (smt, _) = lowered("x as int == x").unwrap();
        assert_eq!(smt, "(= x! x!)");
    }

    /// When only the query's own applications decide which function a name
    /// is, the reading is reported: `v`'s type is not stated, and the query
    /// applies `Seq::len` only, so `v.len()` reads as it with a note.
    #[test]
    fn a_reading_the_query_decides_is_reported() {
        let (names, locals, mut occurrences) = env_parts();
        occurrences.applications.retain(|(head, _)| **head != "vstd!set.Set.len.?");
        let env = Env {
            names: &names,
            crate_name: "k",
            locals,
            bound: Vec::new(),
            declared: &declared,
            occurrences: &occurrences,
        };
        let lowered = lower("v.len() >= 0", &env).unwrap();
        assert!(
            lowered.choices.iter().any(|c| c.contains("Seq::len") && c.contains("applies")),
            "{:?}",
            lowered.choices
        );
    }

    /// In an `if` condition, `{` after a path opens the branch.
    #[test]
    fn a_path_can_be_an_if_condition() {
        let e = parse("if a::b { 1 } else { 2 } == 1").unwrap();
        assert!(matches!(e, Ast::Bin(Op::Eq, ..)), "{e:?}");
        assert!(parse("a::B { x: 1 } == c").unwrap_err().contains("struct literals"));
    }

    #[test]
    fn misreadings_are_refused() {
        for (text, reason) in [
            ("g(x) > 0", "no function"),
            ("f(x, x) > 0", "argument"),
            ("x", "not a bool"),
            ("y > 0", "no variable"),
            ("x.len() > 0", "could be any of"),
            ("s + 1 > 0", "no integer"),
            ("s < x", "no integer"),
            ("s == 1", "no integer"),
            ("if x > 0 { s } else { 1 } == 1", "no integer"),
        ] {
            let error = lowered(text).unwrap_err();
            assert!(error.contains(reason), "{text}: {error}");
        }
        // a generic function applied nowhere in the query
        let (names, locals, _) = env_parts();
        let none = Occurrences::default();
        let env = Env {
            names: &names,
            crate_name: "k",
            locals,
            bound: Vec::new(),
            declared: &declared,
            occurrences: &none,
        };
        let error = lower("Seq::len(v) > 0", &env).err().unwrap();
        assert!(error.contains("never applies"), "{error}");
        let _ = HashMap::<(), ()>::new();
    }
}
