//! Which declarations a retained query's fingerprint reads.
//!
//! A query's prefix is every declaration asserted below it, which is the
//! bucket's whole history. Hashing all of it tells a caller that every query
//! in the module changed as soon as an edit adds a lemma or touches an
//! unrelated spec function, and the refresh then re-checks the module it
//! meant to keep. A fingerprint reads instead the declarations the query can
//! reach:
//!
//! - Every batch says what it is about (`BatchOwner`). An item's own
//!   declarations -- a function's declaration, its `req`/`ens` axioms, its
//!   definition axioms -- are read only by the queries that mention a symbol
//!   the item declares: every axiom among them is headed by one of those
//!   symbols, so a query with no term to match on cannot tell whether they
//!   were asserted. Module-wide declarations, broadcast axioms and trait-impl
//!   axioms can fire anywhere, so every query reads them.
//! - Reading an item brings in every symbol its declarations mention, so the
//!   closure walks the call graph as the AIR spells it out.
//! - A declaration that only introduces a name the query never mentions is a
//!   fresh symbol to it, and dropping a fresh symbol from a signature cannot
//!   change what the query proves.
//! - Two module-wide declarations say what they are about item by item, and
//!   are hashed over the part the query reaches (`Projection`): the `distinct`
//!   axiom over a module's fuel constants, and its `declare-datatypes`. A
//!   datatype's other declarations are read by the queries that reach its
//!   symbols.
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
use air::ast::{CommandX, Datatype, Decl, DeclX, ExprX, MultiOp};
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
    Datatypes(Vec<(Vec<Symbol>, u64)>),
}

/// One declaration of a batch, hashed and indexed once per bucket.
struct DeclFacts {
    /// FNV over its printed AIR, as `Fnv::node` writes it.
    hash: u64,
    /// Every name in its AIR, over-approximated by the atoms of its printed
    /// form: a keyword or a label reads as a name that declares nothing.
    /// Over-approximating reads more declarations, never fewer.
    mentions: Vec<Symbol>,
    /// The names that make a query read it, where its batch says what each
    /// declaration is about. `always` is what a batch cannot attribute: an
    /// axiom of a module-wide batch, which can fire anywhere.
    about: Vec<Symbol>,
    always: bool,
    projection: Projection,
}

impl DeclFacts {
    fn read(&self, reached: &HashSet<Symbol>) -> bool {
        self.always || self.about.iter().any(|name| reached.contains(name))
    }

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
                for (names, datatype) in datatypes {
                    if names.iter().any(|name| reached.contains(name)) {
                        hash.write(&datatype.to_le_bytes());
                    }
                }
            }
        }
    }
}

/// One batch of declarations, hashed and indexed once per bucket.
struct BatchFacts {
    owner: BatchOwner,
    /// The names the batch declares: for an item, what a query must mention
    /// to read the item at all.
    declares: Vec<Symbol>,
    /// The names a query reaches by reading the declarations of this batch
    /// that every query reads.
    seeds: Vec<Symbol>,
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
        let attributed = matches!(batch.owner, BatchOwner::Datatypes);
        let mut decls = Vec::new();
        let mut declares = Vec::new();
        for command in batch.commands.iter() {
            let CommandX::Global(decl) = &**command else { continue };
            let (facts, declared) = self.decl(decl, attributed);
            declares.extend(declared);
            decls.push(facts);
        }
        if attributed {
            // What each declaration of a datatype batch is about: the names
            // of its own batch that it mentions. One that names none of them
            // is read by every query.
            let declared: HashSet<Symbol> = declares.iter().copied().collect();
            for facts in decls.iter_mut() {
                facts.about =
                    facts.mentions.iter().copied().filter(|name| declared.contains(name)).collect();
                facts.always = facts.about.is_empty();
            }
        }
        let mut seeds = Vec::new();
        for facts in &decls {
            // A projected declaration seeds nothing: which of its parts the
            // query reaches is what the projection decides.
            if facts.always && matches!(facts.projection, Projection::Whole) {
                seeds.extend(facts.mentions.iter().copied());
            }
        }
        seeds.sort_unstable();
        seeds.dedup();
        let facts = Arc::new(BatchFacts { owner: batch.owner.clone(), declares, seeds, decls });
        self.facts.insert(key, facts.clone());
        facts
    }

    /// One declaration's facts, and the names it declares.
    fn decl(&mut self, decl: &Decl, attributed: bool) -> (DeclFacts, Vec<Symbol>) {
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
        let projection = self.projection(decl);
        // A declaration introduces names, so a query that mentions none of
        // them cannot tell it from a fresh symbol; an axiom of a module-wide
        // batch has nothing to attribute it to, and every query reads it. A
        // datatype batch attributes both, once its own names are known.
        let always = !attributed && declares.is_empty();
        let about = if attributed { Vec::new() } else { declares.clone() };
        (DeclFacts { hash: hash.0, mentions, about, always, projection }, declares)
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
                        let mut hash = Fnv::new();
                        hash.node(&self.printer.decl_to_node(&one));
                        (names, hash.0)
                    })
                    .collect(),
            ),
            _ => Projection::Whole,
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

    // Every item's batches, and which item a name belongs to.
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
    let mut item_of_symbol: HashMap<Symbol, Vec<usize>> = HashMap::new();
    // An item that declares nothing has no name to reach it by, so every
    // query reads it.
    let mut item_unattributed = vec![true; items.len()];
    for (item, of_item) in items.iter().enumerate() {
        for at in of_item {
            for name in &batches[*at].declares {
                item_unattributed[item] = false;
                item_of_symbol.entry(*name).or_default().push(item);
            }
        }
    }

    // The declarations a batch attributes, by the names they are about.
    let mut about_index: HashMap<Symbol, Vec<(usize, usize)>> = HashMap::new();
    for (at, batch) in batches.iter().enumerate() {
        if matches!(batch.owner, BatchOwner::Item(_)) {
            continue;
        }
        for (which, decl) in batch.decls.iter().enumerate() {
            for name in &decl.about {
                about_index.entry(*name).or_default().push((at, which));
            }
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

        // What the query reaches: the names it mentions, the names the
        // declarations every query reads mention, and then, item by item and
        // datatype by datatype, what reaching a name brings in.
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
        for at in (0..end).filter(|at| item_of_batch[*at].is_none()) {
            for name in &batches[at].seeds {
                if reached.insert(*name) {
                    frontier.push(*name);
                }
            }
        }
        let mut item_read = vec![false; items.len()];
        let mut item_queue: Vec<usize> = Vec::new();
        for (item, unattributed) in item_unattributed.iter().enumerate() {
            if *unattributed {
                item_read[item] = true;
                item_queue.push(item);
            }
        }
        let mut decl_read: HashSet<(usize, usize)> = HashSet::new();
        loop {
            // Reading an item brings in every name its declarations mention,
            // which reaches the items and the datatypes they are about.
            if let Some(item) = item_queue.pop() {
                for at in items[item].iter().filter(|at| **at < end) {
                    for decl in &batches[*at].decls {
                        for name in &decl.mentions {
                            if reached.insert(*name) {
                                frontier.push(*name);
                            }
                        }
                    }
                }
                continue;
            }
            let Some(name) = frontier.pop() else { break };
            for item in item_of_symbol.get(&name).map(Vec::as_slice).unwrap_or(&[]) {
                if !item_read[*item] {
                    item_read[*item] = true;
                    item_queue.push(*item);
                }
            }
            for (at, which) in about_index.get(&name).map(Vec::as_slice).unwrap_or(&[]) {
                if *at >= end || !decl_read.insert((*at, *which)) {
                    continue;
                }
                for name in &batches[*at].decls[*which].mentions {
                    if reached.insert(*name) {
                        frontier.push(*name);
                    }
                }
            }
        }

        // The declarations it reads, in the order they were asserted.
        let mut hash = Fnv::new();
        hash.write(&prelude.to_le_bytes());
        for at in 0..end {
            if let Some(item) = item_of_batch[at] {
                if !item_read[item] {
                    continue;
                }
                for decl in &batches[at].decls {
                    decl.write(&mut hash, &reached);
                }
                continue;
            }
            for decl in &batches[at].decls {
                if decl.read(&reached) {
                    decl.write(&mut hash, &reached);
                }
            }
        }

        fingerprints.push(Fingerprint { prefix: hash.0, body: body.0 });
    }
    fingerprints
}
