//! Query fingerprints: what the incremental cache compares a query by across
//! runs over edited source (ported from the Basis fork's resident sessions).
//!
//! A query's fingerprint is FNV-1a over the AIR of the declarations it reads
//! of those asserted below it (the prefix hash) and over the query itself
//! with its budget (the body hash), each printed as AIR. The printer writes
//! an assertion's labels as their notes and never a span, so a query that
//! only moved to other lines prints the same, and generated local names carry
//! per-function counters, not line numbers. A quantifier's triggers are
//! hashed sorted and once each (`sort_patterns`), and its `:qid` and
//! `:skolemid` without the counter they end in, which is the bucket's, not
//! the function's (`forget_quantifier_counters`).
//!
//! The prefix is every declaration asserted below the query: the bucket's
//! whole history. Hashing all of it would mark every query of the module
//! changed as soon as an edit adds a lemma or touches an unrelated spec
//! function. A fingerprint reads instead the declarations the query can
//! reach:
//!
//! - A quantified axiom is instantiated only on a term matching one of its
//!   triggers, so a query reads it once it reaches every name of the bucket
//!   in some trigger (`Condition::Trigger`). A trigger that names nothing of
//!   the bucket can match anywhere, and every query reads its axiom.
//! - Whatever an axiom asserts outside its quantifiers is asserted as it
//!   stands, so a query reads it once it reaches any name of the bucket in
//!   it (`Condition::Ground`), and every query reads one that names none.
//! - A declaration that only introduces a name the query never mentions is a
//!   fresh symbol to it, and dropping a fresh symbol from a signature cannot
//!   change what the query proves, so it is read by the queries that reach
//!   the name.
//! - Reading a declaration brings in every name it mentions, so the closure
//!   walks the call graph as the AIR spells it out.
//! - Every batch says what it is about (`BatchOwner`). An item's own
//!   declarations -- a function's declaration, its `req`/`ens` axioms, its
//!   definition axioms -- are read together, as soon as any one of them is.
//! - Module-wide axioms -- broadcast axioms, trait-impl axioms, the fuel
//!   constants' `distinct` -- are read by every query.
//! - Two module-wide declarations say what they are about item by item, and
//!   are hashed over the part the query reaches (`Projection`): the `distinct`
//!   axiom over a module's fuel constants, and its `declare-datatypes`.
//!
//! What is left is conservative: a broadcast lemma, a revealed group, a trait
//! bound, a trait impl or a word size still marks every query of the module
//! changed. What a fingerprint does not promise is that every declaration
//! below the query is identical, only that every declaration it can reach
//! is: an axiom the query cannot match on still costs the solver resource
//! units, so a verdict near the budget can in principle differ.

use air::ast::{
    BinaryOp, BindX, CommandX, Commands, Datatype, Decl, DeclX, Expr, ExprX, MultiOp, Quant, Query,
    UnaryOp,
};
use air::context::SmtSolver;
use sise::TreeNode;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir::ast_util::fun_as_friendly_rust_name;
use vir::messages::VirMessageInterface;

/// What a batch of declarations is about, as the verifier generates it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum BatchOwner {
    /// Read by every query: a module-wide declaration, a broadcast axiom, a
    /// trait-impl axiom. Whatever it asserts can fire anywhere.
    Module,
    /// A module's datatypes, whose declarations say what they are about: the
    /// names of the batch itself that each one mentions.
    Datatypes,
    /// One item's own declarations, read by the queries that reach a name it
    /// declares. The key groups an item's batches (a function's declaration,
    /// its `req`/`ens` axioms and its definition axioms).
    Item(Arc<String>),
}

impl BatchOwner {
    /// The batches of one function.
    pub(crate) fn function(fun: &vir::ast::Fun) -> Self {
        BatchOwner::Item(Arc::new(fun_as_friendly_rust_name(fun)))
    }
}

/// A query's identity across runs: the hash of the declarations it reads and
/// the hash of the query itself and its budget.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct Fingerprint {
    pub(crate) prefix: u64,
    pub(crate) body: u64,
}

/// FNV-1a over printed AIR.
pub(crate) struct Fnv(pub(crate) u64);

impl Fnv {
    pub(crate) fn new() -> Self {
        Self(0xcbf2_9ce4_8422_2325)
    }

    pub(crate) fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.0 ^= u64::from(*byte);
            self.0 = self.0.wrapping_mul(0x0000_0100_0000_01b3);
        }
    }

    pub(crate) fn node(&mut self, node: &TreeNode) {
        let mut node = node.clone();
        sort_patterns(&mut node);
        forget_quantifier_counters(&mut node);
        self.write(air::printer::node_to_string(&node).as_bytes());
        self.write(b"\n");
    }
}

/// Put every annotated term's `:pattern` groups in the order of their text,
/// once each, in place: `(! e :pattern (p) :pattern (q) :qid ...)` keeps its
/// other annotations where they are, and the patterns take the place of the
/// first. Automatic trigger selection lists a quantifier's triggers in an
/// order that varies from one compilation to the next, and sometimes lists
/// one twice; neither changes the query.
fn sort_patterns(node: &mut TreeNode) {
    let TreeNode::List(items) = node else { return };
    for item in items.iter_mut() {
        sort_patterns(item);
    }
    if !matches!(items.first(), Some(TreeNode::Atom(bang)) if bang == "!") {
        return;
    }
    let mut rest = Vec::with_capacity(items.len());
    let mut patterns: Vec<(String, TreeNode)> = Vec::new();
    let mut first = None;
    let mut i = 0;
    while i < items.len() {
        if matches!(&items[i], TreeNode::Atom(key) if key == ":pattern") && i + 1 < items.len() {
            first.get_or_insert(rest.len());
            patterns.push((air::printer::node_to_string(&items[i + 1]), items[i + 1].clone()));
            i += 2;
        } else {
            rest.push(items[i].clone());
            i += 1;
        }
    }
    let Some(first) = first else { return };
    patterns.sort_by(|a, b| a.0.cmp(&b.0));
    patterns.dedup_by(|a, b| a.0 == b.0);
    let tail = rest.split_off(first);
    for (_, pattern) in patterns {
        rest.push(TreeNode::Atom(":pattern".to_owned()));
        rest.push(pattern);
    }
    rest.extend(tail);
    *items = rest;
}

/// Drop the counter from every user quantifier's `:qid` and `:skolemid`, in
/// place: `user_f_12` becomes `user_f_`. The counter is kept per bucket, not
/// per function (`new_user_qid`), so it moves with every quantifier lowered
/// before this one in the bucket: one added to an earlier function, or a
/// recommends query lowered for an earlier function. None of those changes
/// this quantifier, whose own text is hashed with its name.
fn forget_quantifier_counters(node: &mut TreeNode) {
    let TreeNode::List(items) = node else { return };
    for item in items.iter_mut() {
        forget_quantifier_counters(item);
    }
    if !matches!(items.first(), Some(TreeNode::Atom(bang)) if bang == "!") {
        return;
    }
    let skolem_prefix = air::mk_skolem_id(air::profiler::USER_QUANT_PREFIX);
    for i in 1..items.len() {
        if !matches!(&items[i - 1], TreeNode::Atom(key) if key == ":qid" || key == ":skolemid") {
            continue;
        }
        let TreeNode::Atom(name) = &mut items[i] else { continue };
        if !name.starts_with(air::profiler::USER_QUANT_PREFIX) && !name.starts_with(&skolem_prefix)
        {
            continue;
        }
        let without = name.trim_end_matches(|c: char| c.is_ascii_digit()).len();
        if without < name.len() && name[..without].ends_with('_') {
            name.truncate(without);
        }
    }
}

/// An AIR name, interned so the closure over what a query reaches walks
/// `u32`s rather than strings.
type Symbol = u32;

#[derive(Default)]
struct SymbolTable {
    ids: HashMap<String, Symbol>,
}

impl SymbolTable {
    fn intern(&mut self, name: &str) -> Symbol {
        if let Some(id) = self.ids.get(name) {
            return *id;
        }
        let id = self.ids.len() as Symbol;
        self.ids.insert(name.to_owned(), id);
        id
    }
}

/// What a declaration is hashed over where a query reaches only part of it.
enum Projection {
    /// Hashed whole.
    Whole,
    /// `(distinct a b ...)`, hashed over the operands the query reaches: what
    /// the rest are distinct from cannot reach it. A module's fuel constants
    /// are asserted distinct in one such axiom, so without this every query
    /// of a module changed when a spec function was added to it.
    Distinct(Vec<(Symbol, String)>),
    /// `(declare-datatypes ...)`: every transparent datatype of the module in
    /// one declaration, hashed over the datatypes the query reaches, each by
    /// the names it declares and its own hash.
    Datatypes(Vec<DatatypePart>),
}

/// One datatype of a `declare-datatypes`, as a query reaches it.
struct DatatypePart {
    /// The names it declares: its sort, its variants and their fields.
    names: Vec<Symbol>,
    /// Every name it mentions, which is what reaching it brings in.
    mentions: Vec<Symbol>,
    /// FNV over that one datatype, printed alone.
    hash: u64,
}

/// What makes a query read an axiom, over the names in it. Only a name some
/// batch of the bucket declares can be absent from a query; the rest (the
/// prelude's, bound variables) are left out when the rules are built.
enum Condition {
    /// One trigger of a quantifier the axiom asserts: the axiom can be
    /// instantiated on it only once the query reaches every name in it.
    Trigger(Vec<Symbol>),
    /// An atom the axiom asserts outside any quantifier it can be triggered
    /// by: it holds as it stands, so a query that reaches any name in it
    /// reads it.
    Ground(Vec<Symbol>),
}

/// One declaration of a batch, hashed and indexed once per bucket.
struct DeclFacts {
    /// FNV over its printed AIR, as `Fnv::node` writes it.
    hash: u64,
    /// Every name in its AIR, over-approximated by the atoms of its printed
    /// form: a keyword or a label reads as a name that declares nothing.
    mentions: Vec<Symbol>,
    /// The names it declares, which a query reads it by.
    declares: Vec<Symbol>,
    /// For an axiom, what makes a query read it; empty for a declaration.
    conditions: Vec<Condition>,
    projection: Projection,
}

impl DeclFacts {
    /// Hash it into `hash` for a query that reaches `reached`, over the part
    /// of a projected declaration that query reaches.
    fn write(&self, hash: &mut Fnv, reached: &HashSet<Symbol>) {
        match &self.projection {
            Projection::Whole => hash.write(&self.hash.to_le_bytes()),
            Projection::Distinct(operands) => {
                let mut kept = Fnv::new();
                let mut count = 0;
                for (_, text) in operands.iter().filter(|(name, _)| reached.contains(name)) {
                    kept.write(text.as_bytes());
                    kept.write(b"\n");
                    count += 1;
                }
                // Distinctness of fewer than two constants says nothing.
                if count > 1 {
                    hash.write(&kept.0.to_le_bytes());
                }
            }
            Projection::Datatypes(datatypes) => {
                for datatype in datatypes {
                    if datatype.names.iter().any(|name| reached.contains(name)) {
                        hash.write(&datatype.hash.to_le_bytes());
                    }
                }
            }
        }
    }
}

/// One batch of declarations, hashed and indexed once per bucket.
struct BatchFacts {
    decls: Vec<DeclFacts>,
}

/// What reading something brings into a query's fingerprint.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Target {
    /// Every declaration of one item.
    Item(usize),
    /// One declaration of a batch that is not an item's.
    Decl(usize, usize),
    /// One datatype of a batch's `declare-datatypes`.
    Part(usize, usize, usize),
}

/// Where a part of an axiom is asserted: whether a quantifier there holds for
/// every binding or for some. A part asserted both ways (under an `iff` or
/// an `if` condition) is read by its names instead (`Prefix::ground`).
#[derive(Clone, Copy)]
enum Polarity {
    Positive,
    Negative,
}

impl Polarity {
    fn flip(self) -> Self {
        match self {
            Polarity::Positive => Polarity::Negative,
            Polarity::Negative => Polarity::Positive,
        }
    }
}

/// Every atom of a printed declaration or query.
fn atoms(node: &TreeNode, each: &mut impl FnMut(&str)) {
    match node {
        TreeNode::Atom(atom) => each(atom),
        TreeNode::List(items) => {
            for item in items.iter() {
                atoms(item, each);
            }
        }
    }
}

/// The declarations asserted below the queries of one bucket so far, indexed
/// as the verifier appends them (a batch is indexed once), and the rules that
/// say which query reads which of them. A batch's declarations may only
/// mention names declared at or before it, so indexing in order sees every
/// name a condition is over.
pub(crate) struct Prefix {
    symbols: SymbolTable,
    pub(crate) printer: air::printer::Printer,
    /// The prelude, hashed whole: it is one text for the crate, and a query
    /// that reaches none of what it declares still rests on its axioms.
    prelude: u64,
    batches: Vec<BatchFacts>,
    /// The names of the bucket: what a condition is over.
    bucket: HashSet<Symbol>,
    /// Every item's batches, and which item a batch belongs to.
    items: Vec<Vec<usize>>,
    item_of_batch: Vec<Option<usize>>,
    item_of_key: HashMap<String, usize>,
    /// What reads what: each rule is a set of names that, once a query
    /// reaches all of them, reads its target. A rule with no names reads its
    /// target for every query.
    rules: Vec<(Vec<Symbol>, Target)>,
    rules_of_name: HashMap<Symbol, Vec<usize>>,
    always: Vec<Target>,
}

impl Prefix {
    pub(crate) fn new(prelude: &Commands, solver: SmtSolver) -> Self {
        let printer = air::printer::Printer::new(Arc::new(VirMessageInterface {}), false, solver);
        let mut hash = Fnv::new();
        for command in prelude.iter() {
            if let CommandX::Global(decl) = &**command {
                hash.node(&printer.decl_to_node(decl));
            }
        }
        Prefix {
            symbols: SymbolTable::default(),
            printer,
            prelude: hash.0,
            batches: Vec::new(),
            bucket: HashSet::new(),
            items: Vec::new(),
            item_of_batch: Vec::new(),
            item_of_key: HashMap::new(),
            rules: Vec::new(),
            rules_of_name: HashMap::new(),
            always: Vec::new(),
        }
    }

    /// How many batches have been indexed.
    pub(crate) fn len(&self) -> usize {
        self.batches.len()
    }

    /// Index the next batch asserted below the queries to come.
    pub(crate) fn push(&mut self, commands: &Commands, owner: BatchOwner) {
        let at = self.batches.len();
        let mut decls = Vec::new();
        for command in commands.iter() {
            let CommandX::Global(decl) = &**command else { continue };
            let facts = self.decl(decl);
            self.bucket.extend(facts.declares.iter().copied());
            decls.push(facts);
        }
        let item = match &owner {
            BatchOwner::Item(key) => {
                let items = &mut self.items;
                let item = *self.item_of_key.entry((**key).clone()).or_insert_with(|| {
                    items.push(Vec::new());
                    items.len() - 1
                });
                self.items[item].push(at);
                Some(item)
            }
            _ => None,
        };
        self.item_of_batch.push(item);
        let module_wide = matches!(owner, BatchOwner::Module);
        for (which, decl) in decls.iter().enumerate() {
            let target = match item {
                Some(item) => Target::Item(item),
                None => Target::Decl(at, which),
            };
            if let Projection::Datatypes(datatypes) = &decl.projection {
                for (part, datatype) in datatypes.iter().enumerate() {
                    for name in &datatype.names {
                        self.rule(vec![*name], Target::Part(at, which, part));
                    }
                }
                continue;
            }
            for name in &decl.declares {
                self.rule(vec![*name], target);
            }
            if module_wide && decl.declares.is_empty() {
                // A module-wide axiom can fire anywhere.
                self.rule(Vec::new(), target);
                continue;
            }
            for condition in &decl.conditions {
                let (Condition::Trigger(names) | Condition::Ground(names)) = condition;
                let names: Vec<Symbol> =
                    names.iter().copied().filter(|name| self.bucket.contains(name)).collect();
                match condition {
                    Condition::Trigger(_) => self.rule(names, target),
                    Condition::Ground(_) if names.is_empty() => self.rule(Vec::new(), target),
                    Condition::Ground(_) => {
                        for name in names {
                            self.rule(vec![name], target);
                        }
                    }
                }
            }
        }
        self.batches.push(BatchFacts { decls });
    }

    fn rule(&mut self, names: Vec<Symbol>, target: Target) {
        if names.is_empty() {
            self.always.push(target);
            return;
        }
        let rule = self.rules.len();
        for name in &names {
            self.rules_of_name.entry(*name).or_default().push(rule);
        }
        self.rules.push((names, target));
    }

    /// The fingerprint of `query` over the batches indexed so far, with
    /// `salt` (the budget and whatever else decides a verdict) hashed into
    /// the body. A prelude-free query (`with_prefix` false: a bit-vector
    /// query, whose solver gets neither the prelude nor the bucket context)
    /// has an empty prefix.
    pub(crate) fn fingerprint(
        &mut self,
        query: &Query,
        salt: &[u8],
        with_prefix: bool,
    ) -> Fingerprint {
        let node = self.printer.query_to_node(query);
        let mut body = Fnv::new();
        body.node(&node);
        body.write(salt);
        if !with_prefix {
            return Fingerprint { prefix: 0, body: body.0 };
        }

        // What the query reaches: the names it mentions and then, rule by
        // rule, what reading a target brings in.
        let mut reached: HashSet<Symbol> = HashSet::new();
        let mut frontier: Vec<Symbol> = Vec::new();
        {
            let symbols = &mut self.symbols;
            atoms(&node, &mut |atom| {
                let name = symbols.intern(atom);
                if reached.insert(name) {
                    frontier.push(name);
                }
            });
        }
        let mut read: HashSet<Target> = HashSet::new();
        let mut missing: Vec<usize> = self.rules.iter().map(|(names, _)| names.len()).collect();
        let batches = &self.batches;
        let items = &self.items;
        let fire = |target: Target,
                    read: &mut HashSet<Target>,
                    reached: &mut HashSet<Symbol>,
                    frontier: &mut Vec<Symbol>| {
            if !read.insert(target) {
                return;
            }
            let mut bring = |names: &[Symbol]| {
                for name in names {
                    if reached.insert(*name) {
                        frontier.push(*name);
                    }
                }
            };
            match target {
                Target::Item(item) => {
                    for at in items[item].iter() {
                        for decl in &batches[*at].decls {
                            bring(&decl.mentions);
                        }
                    }
                }
                Target::Decl(at, which) => {
                    let decl = &batches[at].decls[which];
                    // A projected `distinct` brings in nothing: which of its
                    // operands the query reaches is what the projection
                    // decides.
                    if matches!(decl.projection, Projection::Whole) {
                        bring(&decl.mentions);
                    }
                }
                Target::Part(at, which, part) => {
                    if let Projection::Datatypes(datatypes) = &batches[at].decls[which].projection {
                        bring(&datatypes[part].mentions);
                    }
                }
            }
        };
        for target in &self.always {
            fire(*target, &mut read, &mut reached, &mut frontier);
        }
        while let Some(name) = frontier.pop() {
            for rule in self.rules_of_name.get(&name).map(Vec::as_slice).unwrap_or(&[]) {
                missing[*rule] -= 1;
                if missing[*rule] == 0 {
                    fire(self.rules[*rule].1, &mut read, &mut reached, &mut frontier);
                }
            }
        }

        // The declarations it reads, in the order they were asserted.
        let mut hash = Fnv::new();
        hash.write(&self.prelude.to_le_bytes());
        for (at, batch) in self.batches.iter().enumerate() {
            if let Some(item) = self.item_of_batch[at] {
                if read.contains(&Target::Item(item)) {
                    for decl in &batch.decls {
                        decl.write(&mut hash, &reached);
                    }
                }
                continue;
            }
            for (which, decl) in batch.decls.iter().enumerate() {
                let parts = match &decl.projection {
                    Projection::Datatypes(datatypes) => datatypes.len(),
                    _ => 0,
                };
                if read.contains(&Target::Decl(at, which))
                    || (0..parts).any(|part| read.contains(&Target::Part(at, which, part)))
                {
                    decl.write(&mut hash, &reached);
                }
            }
        }
        Fingerprint { prefix: hash.0, body: body.0 }
    }

    /// One declaration's facts.
    fn decl(&mut self, decl: &Decl) -> DeclFacts {
        let node = self.printer.decl_to_node(decl);
        let mut mentions = Vec::new();
        {
            let symbols = &mut self.symbols;
            atoms(&node, &mut |atom| mentions.push(symbols.intern(atom)));
        }
        mentions.sort_unstable();
        mentions.dedup();
        let mut hash = Fnv::new();
        hash.node(&node);
        let declares = match &**decl {
            DeclX::Sort(name)
            | DeclX::Const(name, _)
            | DeclX::Fun(name, _, _)
            | DeclX::Var(name, _) => vec![self.symbols.intern(name)],
            DeclX::Datatypes(datatypes) => {
                datatypes.iter().flat_map(|datatype| self.datatype_names(datatype)).collect()
            }
            DeclX::Axiom(_) => Vec::new(),
        };
        let mut conditions = Vec::new();
        if let DeclX::Axiom(axiom) = &**decl {
            self.conditions(&axiom.expr, Polarity::Positive, &mut conditions);
        }
        let projection = self.projection(decl);
        DeclFacts { hash: hash.0, mentions, declares, conditions, projection }
    }

    /// What makes a query read the formula `expr`, asserted at `polarity`.
    /// A quantifier that holds for every binding (a `forall` asserted, an
    /// `exists` denied) is instantiated through its triggers; every other
    /// part of the formula is asserted as it stands, and a quantifier under
    /// it is skolemized or nested inside a term, so it is read by its names.
    fn conditions(&mut self, expr: &Expr, polarity: Polarity, into: &mut Vec<Condition>) {
        match &**expr {
            ExprX::Unary(UnaryOp::Not, e) => self.conditions(e, polarity.flip(), into),
            ExprX::Binary(BinaryOp::Implies, lhs, rhs) => {
                self.conditions(lhs, polarity.flip(), into);
                self.conditions(rhs, polarity, into);
            }
            ExprX::Multi(MultiOp::And | MultiOp::Or, es) => {
                for e in es.iter() {
                    self.conditions(e, polarity, into);
                }
            }
            ExprX::LabeledAxiom(_, _, e) | ExprX::LabeledAssertion(_, _, _, e) => {
                self.conditions(e, polarity, into)
            }
            ExprX::Bind(bind, _) => match &**bind {
                BindX::Quant(quant, binders, triggers, _)
                    if matches!(
                        (quant, polarity),
                        (Quant::Forall, Polarity::Positive) | (Quant::Exists, Polarity::Negative)
                    ) =>
                {
                    let bound: HashSet<&str> =
                        binders.iter().map(|binder| binder.name.as_str()).collect();
                    if triggers.is_empty() {
                        // No trigger to match on: whatever instantiates it
                        // instantiates it anywhere.
                        into.push(Condition::Trigger(Vec::new()));
                    }
                    for trigger in triggers.iter() {
                        let mut names = Vec::new();
                        for term in trigger.iter() {
                            names_of(term, &mut |name| {
                                if !bound.contains(name) {
                                    names.push(name.to_owned())
                                }
                            });
                        }
                        let mut names: Vec<Symbol> =
                            names.iter().map(|name| self.symbols.intern(name)).collect();
                        names.sort_unstable();
                        names.dedup();
                        into.push(Condition::Trigger(names));
                    }
                }
                _ => self.ground(expr, into),
            },
            _ => self.ground(expr, into),
        }
    }

    /// An atom asserted as it stands, read by any name in it.
    fn ground(&mut self, expr: &Expr, into: &mut Vec<Condition>) {
        let mut names = Vec::new();
        names_of(expr, &mut |name| names.push(name.to_owned()));
        let mut names: Vec<Symbol> = names.iter().map(|name| self.symbols.intern(name)).collect();
        names.sort_unstable();
        names.dedup();
        into.push(Condition::Ground(names));
    }

    /// Every name one datatype declares: its sort, its variants and their
    /// fields, which is what a query mentions to reach it.
    fn datatype_names(&mut self, datatype: &Datatype) -> Vec<Symbol> {
        let mut names = vec![self.symbols.intern(&datatype.name)];
        for variant in datatype.a.iter() {
            names.push(self.symbols.intern(&variant.name));
            for field in variant.a.iter() {
                names.push(self.symbols.intern(&field.name));
            }
        }
        names
    }

    fn projection(&mut self, decl: &Decl) -> Projection {
        match &**decl {
            DeclX::Axiom(axiom) => {
                let ExprX::Multi(MultiOp::Distinct, operands) = &*axiom.expr else {
                    return Projection::Whole;
                };
                let mut names = Vec::new();
                for operand in operands.iter() {
                    // Only names: `(distinct (f x) ...)` says something about
                    // whatever its operands are built from.
                    let ExprX::Var(name) = &**operand else {
                        return Projection::Whole;
                    };
                    names.push((self.symbols.intern(name), (**name).clone()));
                }
                Projection::Distinct(names)
            }
            DeclX::Datatypes(datatypes) => Projection::Datatypes(
                datatypes
                    .iter()
                    .map(|datatype| {
                        let names = self.datatype_names(datatype);
                        let one: Decl =
                            Arc::new(DeclX::Datatypes(Arc::new(vec![datatype.clone()])));
                        let node = self.printer.decl_to_node(&one);
                        let mut mentions = Vec::new();
                        {
                            let symbols = &mut self.symbols;
                            atoms(&node, &mut |atom| mentions.push(symbols.intern(atom)));
                        }
                        mentions.sort_unstable();
                        mentions.dedup();
                        let mut hash = Fnv::new();
                        hash.node(&node);
                        DatatypePart { names, mentions, hash: hash.0 }
                    })
                    .collect(),
            ),
            _ => Projection::Whole,
        }
    }
}

/// Every name `expr` applies or refers to.
fn names_of(expr: &Expr, each: &mut impl FnMut(&str)) {
    match &**expr {
        ExprX::Const(_) => {}
        ExprX::Var(name) => each(name),
        ExprX::Old(_, name) => each(name),
        ExprX::Apply(name, args) => {
            each(name);
            for arg in args.iter() {
                names_of(arg, each);
            }
        }
        ExprX::ApplyFun(_, f, args) => {
            names_of(f, each);
            for arg in args.iter() {
                names_of(arg, each);
            }
        }
        ExprX::Unary(_, e) => names_of(e, each),
        ExprX::Binary(_, lhs, rhs) => {
            names_of(lhs, each);
            names_of(rhs, each);
        }
        ExprX::Multi(_, es) | ExprX::Array(es) => {
            for e in es.iter() {
                names_of(e, each);
            }
        }
        ExprX::IfElse(c, t, f) => {
            names_of(c, each);
            names_of(t, each);
            names_of(f, each);
        }
        ExprX::Bind(bind, body) => {
            match &**bind {
                BindX::Let(binders) => {
                    for binder in binders.iter() {
                        names_of(&binder.a, each);
                    }
                }
                BindX::Quant(_, _, triggers, _)
                | BindX::Lambda(_, triggers, _)
                | BindX::Choose(_, triggers, _, _) => {
                    for trigger in triggers.iter() {
                        for term in trigger.iter() {
                            names_of(term, each);
                        }
                    }
                }
            }
            if let BindX::Choose(_, _, _, cond) = &**bind {
                names_of(cond, each);
            }
            names_of(body, each);
        }
        ExprX::LabeledAxiom(_, _, e) | ExprX::LabeledAssertion(_, _, _, e) => names_of(e, each),
    }
}
