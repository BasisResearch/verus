//! Which declarations a retained query's fingerprint reads.
//!
//! A query's prefix is every declaration asserted below it, which is the
//! bucket's whole history. Hashing all of it tells a caller that every query
//! in the module changed as soon as an edit adds a lemma or touches an
//! unrelated spec function, and the refresh then re-checks the module it
//! meant to keep. A fingerprint reads instead the declarations the query can
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
//!   Which of an item's axioms a query can instantiate is decided by its
//!   triggers, not by whose batch it is in: a trait impl's spec definition is
//!   keyed on the trait method, and a function's `FnDef` axioms on the
//!   function's `FNDEF` type, neither of which the item declares.
//! - Module-wide axioms -- broadcast axioms, trait-impl axioms, the fuel
//!   constants' `distinct` -- are read by every query.
//! - Two module-wide declarations say what they are about item by item, and
//!   are hashed over the part the query reaches (`Projection`): the `distinct`
//!   axiom over a module's fuel constants, and its `declare-datatypes`. A
//!   datatype's other declarations are read by their triggers and names, as
//!   an item's are.
//!
//! What is left is conservative: a broadcast lemma, a revealed group, a trait
//! bound, a trait impl or a word size still marks every query of the module
//! changed.
//!
//! What a fingerprint no longer promises is that every declaration below the
//! query is identical, only that every declaration it can reach is. An axiom
//! it cannot match on can still change what a solver does with it: an `mbqi`
//! or `enum` rung instantiates without a trigger, and every assertion costs
//! resource units. A carried-over verdict is therefore the default schedule's;
//! a rung pinned by hand is what this trades away.

use super::{Batch, BatchOwner, Fingerprint, Fnv, QueryJournal};
use air::ast::{
    BinaryOp, BindX, CommandX, Datatype, Decl, DeclX, Expr, ExprX, MultiOp, Quant, UnaryOp,
};
use air::context::SmtSolver;
use sise::TreeNode;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir::messages::VirMessageInterface;

/// An AIR name, interned so the closure over what a query reaches walks
/// `u32`s rather than strings. The table is the bucket's, so the ids in a
/// batch's cached facts mean the same in every journal of that bucket.
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

/// One datatype of a `declare-datatypes`, as a query reaches it: a projected
/// declaration is reached part by part, so that mentioning one datatype of a
/// module's block does not read the block.
struct DatatypePart {
    /// The names it declares: its sort, its variants and their fields, which
    /// is what a query mentions to reach it.
    names: Vec<Symbol>,
    /// Every name it mentions printed alone, which is what reaching it brings
    /// in: a field's sort reaches that datatype's own declarations, and two
    /// mutually recursive datatypes reach each other.
    mentions: Vec<Symbol>,
    /// FNV over that one datatype, printed alone.
    hash: u64,
}

/// What makes a query read an axiom, over the names in it. Which of those
/// names count is the journal's: only a name some batch of the bucket
/// declares can be absent from a query, and the rest (the prelude's, bound
/// variables) are left out when the journal is fingerprinted.
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
    /// Over-approximating reads more declarations, never fewer.
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
    owner: BatchOwner,
    /// The names the batch declares.
    declares: Vec<Symbol>,
    decls: Vec<DeclFacts>,
}

/// The names and hashes of one bucket's declarations, built as its journals
/// are fingerprinted and shared between them: the batches below a spinoff
/// solver's queries are the batches below the main solver's, as the same
/// `Arc`s, and the prelude is one `Arc` for the bucket.
pub(crate) struct Index {
    symbols: SymbolTable,
    printer: air::printer::Printer,
    /// Keyed by the address of a batch's commands, which live as long as the
    /// journals the index is built from.
    facts: HashMap<usize, Arc<BatchFacts>>,
    preludes: HashMap<usize, u64>,
}

impl Index {
    pub(crate) fn new() -> Self {
        Index {
            symbols: SymbolTable::default(),
            printer: air::printer::Printer::new(
                Arc::new(VirMessageInterface {}),
                false,
                SmtSolver::Cvc5,
            ),
            facts: HashMap::new(),
            preludes: HashMap::new(),
        }
    }

    /// The prelude, hashed whole: it is one text for the crate, and a query
    /// that reaches none of what it declares still rests on its axioms.
    fn prelude(&mut self, prelude: &air::ast::Commands) -> u64 {
        let key = Arc::as_ptr(prelude) as usize;
        if let Some(hash) = self.preludes.get(&key) {
            return *hash;
        }
        let mut hash = Fnv::new();
        for command in prelude.iter() {
            if let CommandX::Global(decl) = &**command {
                hash.node(&self.printer.decl_to_node(decl));
            }
        }
        self.preludes.insert(key, hash.0);
        hash.0
    }

    fn batch(&mut self, batch: &Batch) -> Arc<BatchFacts> {
        // A batch's commands and what it is about come from one
        // `CommandBatch`, so the address of the commands decides both.
        let key = Arc::as_ptr(&batch.commands) as usize;
        if let Some(facts) = self.facts.get(&key) {
            return facts.clone();
        }
        let mut decls = Vec::new();
        let mut declares = Vec::new();
        for command in batch.commands.iter() {
            let CommandX::Global(decl) = &**command else { continue };
            let facts = self.decl(decl);
            declares.extend(facts.declares.iter().copied());
            decls.push(facts);
        }
        let facts = Arc::new(BatchFacts { owner: batch.owner.clone(), declares, decls });
        self.facts.insert(key, facts.clone());
        facts
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
                            self.names(term, &mut |name| {
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
        self.names(expr, &mut |name| names.push(name.to_owned()));
        let mut names: Vec<Symbol> = names.iter().map(|name| self.symbols.intern(name)).collect();
        names.sort_unstable();
        names.dedup();
        into.push(Condition::Ground(names));
    }

    /// Every name `expr` applies or refers to.
    fn names(&self, expr: &Expr, each: &mut impl FnMut(&str)) {
        match &**expr {
            ExprX::Const(_) => {}
            ExprX::Var(name) => each(name),
            ExprX::Old(_, name) => each(name),
            ExprX::Apply(name, args) => {
                each(name);
                for arg in args.iter() {
                    self.names(arg, each);
                }
            }
            ExprX::ApplyFun(_, f, args) => {
                self.names(f, each);
                for arg in args.iter() {
                    self.names(arg, each);
                }
            }
            ExprX::Unary(_, e) => self.names(e, each),
            ExprX::Binary(_, lhs, rhs) => {
                self.names(lhs, each);
                self.names(rhs, each);
            }
            ExprX::Multi(_, es) | ExprX::Array(es) => {
                for e in es.iter() {
                    self.names(e, each);
                }
            }
            ExprX::IfElse(c, t, f) => {
                self.names(c, each);
                self.names(t, each);
                self.names(f, each);
            }
            ExprX::Bind(bind, body) => {
                match &**bind {
                    BindX::Let(binders) => {
                        for binder in binders.iter() {
                            self.names(&binder.a, each);
                        }
                    }
                    BindX::Quant(_, _, triggers, _)
                    | BindX::Lambda(_, triggers, _)
                    | BindX::Choose(_, triggers, _, _) => {
                        for trigger in triggers.iter() {
                            for term in trigger.iter() {
                                self.names(term, each);
                            }
                        }
                    }
                }
                if let BindX::Choose(_, _, _, cond) = &**bind {
                    self.names(cond, each);
                }
                self.names(body, each);
            }
            ExprX::LabeledAxiom(_, _, e) | ExprX::LabeledAssertion(_, _, _, e) => {
                self.names(e, each)
            }
        }
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

/// Where a part of an axiom is asserted: whether a quantifier there holds for
/// every binding or for some. A part asserted both ways (under an `iff` or
/// an `if` condition) is read by its names instead (`Index::ground`).
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

/// Every retained query's fingerprint, in journal order: the hash of the
/// declarations it reads of the prelude and of the scopes below its prefix,
/// and the hash of the query itself and its rlimit.
pub(crate) fn fingerprints(journal: &QueryJournal, index: &mut Index) -> Vec<Fingerprint> {
    let prelude = journal.prelude.as_ref().map(|prelude| index.prelude(prelude)).unwrap_or(0);

    // The batches below the queries, and where each prefix ends among them.
    let mut batches: Vec<Arc<BatchFacts>> = Vec::new();
    for batch in &journal.base {
        batches.push(index.batch(batch));
    }
    let mut prefix_ends = vec![batches.len()];
    for scope in &journal.contexts {
        for batch in scope {
            batches.push(index.batch(batch));
        }
        prefix_ends.push(batches.len());
    }

    // The names of the bucket: what a condition is over. Everything else an
    // axiom names is the prelude's or bound, and is there for every query.
    let bucket: HashSet<Symbol> =
        batches.iter().flat_map(|batch| batch.declares.iter().copied()).collect();

    // Every item's batches.
    let mut items: Vec<Vec<usize>> = Vec::new();
    let mut item_of_batch: Vec<Option<usize>> = vec![None; batches.len()];
    let mut item_of_key: HashMap<String, usize> = HashMap::new();
    for at in 0..batches.len() {
        let BatchOwner::Item(key) = &batches[at].owner else { continue };
        let item = *item_of_key.entry((**key).clone()).or_insert_with(|| {
            items.push(Vec::new());
            items.len() - 1
        });
        items[item].push(at);
        item_of_batch[at] = Some(item);
    }

    // What reads what: each rule is a set of names that, once a query reaches
    // all of them, reads its target. A rule with no names reads its target
    // for every query. A rule counts only below the query's prefix, so each
    // carries the batch it comes from.
    let mut rules: Vec<(Vec<Symbol>, Target, usize)> = Vec::new();
    for (at, batch) in batches.iter().enumerate() {
        let item = item_of_batch[at];
        let module_wide = matches!(batch.owner, BatchOwner::Module);
        for (which, decl) in batch.decls.iter().enumerate() {
            let target = match item {
                Some(item) => Target::Item(item),
                None => Target::Decl(at, which),
            };
            if let Projection::Datatypes(datatypes) = &decl.projection {
                for (part, datatype) in datatypes.iter().enumerate() {
                    for name in &datatype.names {
                        rules.push((vec![*name], Target::Part(at, which, part), at));
                    }
                }
                continue;
            }
            for name in &decl.declares {
                rules.push((vec![*name], target, at));
            }
            if module_wide && decl.declares.is_empty() {
                // A module-wide axiom can fire anywhere.
                rules.push((Vec::new(), target, at));
                continue;
            }
            for condition in &decl.conditions {
                let (Condition::Trigger(names) | Condition::Ground(names)) = condition;
                let names: Vec<Symbol> =
                    names.iter().copied().filter(|name| bucket.contains(name)).collect();
                match condition {
                    Condition::Trigger(_) => rules.push((names, target, at)),
                    Condition::Ground(_) if names.is_empty() => {
                        rules.push((Vec::new(), target, at))
                    }
                    Condition::Ground(_) => {
                        for name in names {
                            rules.push((vec![name], target, at));
                        }
                    }
                }
            }
        }
    }
    let mut rules_of_name: HashMap<Symbol, Vec<usize>> = HashMap::new();
    for (rule, (names, _, _)) in rules.iter().enumerate() {
        for name in names {
            rules_of_name.entry(*name).or_default().push(rule);
        }
    }

    let mut fingerprints = Vec::with_capacity(journal.queries.len());
    for query in &journal.queries {
        let node = index.printer.query_to_node(&query.query);
        let mut body = Fnv::new();
        body.node(&node);
        // The budget a query checks at is part of what it is: raising or
        // lowering it can change its verdict.
        body.write(&query.rlimit.to_bits().to_le_bytes());

        let end = prefix_ends[query.prefix];

        // What the query reaches: the names it mentions and then, rule by
        // rule, what reading a target brings in.
        let mut reached: HashSet<Symbol> = HashSet::new();
        let mut frontier: Vec<Symbol> = Vec::new();
        {
            let symbols = &mut index.symbols;
            atoms(&node, &mut |atom| {
                let name = symbols.intern(atom);
                if reached.insert(name) {
                    frontier.push(name);
                }
            });
        }
        let mut read: HashSet<Target> = HashSet::new();
        let mut missing: Vec<usize> = rules.iter().map(|(names, _, _)| names.len()).collect();
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
                    for at in items[item].iter().filter(|at| **at < end) {
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
        for (names, target, at) in &rules {
            if names.is_empty() && *at < end {
                fire(*target, &mut read, &mut reached, &mut frontier);
            }
        }
        while let Some(name) = frontier.pop() {
            for rule in rules_of_name.get(&name).map(Vec::as_slice).unwrap_or(&[]) {
                missing[*rule] -= 1;
                let (_, target, at) = &rules[*rule];
                if missing[*rule] == 0 && *at < end {
                    fire(*target, &mut read, &mut reached, &mut frontier);
                }
            }
        }

        // The declarations it reads, in the order they were asserted.
        let mut hash = Fnv::new();
        hash.write(&prelude.to_le_bytes());
        for at in 0..end {
            if let Some(item) = item_of_batch[at] {
                if !read.contains(&Target::Item(item)) {
                    continue;
                }
                for decl in &batches[at].decls {
                    decl.write(&mut hash, &reached);
                }
                continue;
            }
            for (which, decl) in batches[at].decls.iter().enumerate() {
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

        fingerprints.push(Fingerprint { prefix: hash.0, body: body.0 });
    }
    fingerprints
}
