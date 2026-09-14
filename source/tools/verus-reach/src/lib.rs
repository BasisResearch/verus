//! Static reachability of verified code, across crates.
//!
//! `verus --reach DIR` writes one [`Report`] per crate: the crate's functions
//! with Verus's labels, and the edges out of every body, each labeled with
//! the context of the reference: a call, a contract, or a proof. Edges may
//! name items in other crates. This library merges the reports of all
//! crates and computes what is reachable from the chosen roots: which
//! functions run, and which ghost functions (specs and proofs) the running
//! code's contracts and proofs use. Coverage is the share of verified
//! functions, exec and ghost alike, that are reachable.

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};

pub const SCHEMA_VERSION: u32 = 4;

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Report {
    pub schema_version: u32,
    #[serde(rename = "crate")]
    pub krate: String,
    /// `bin`, `lib`, or `test`
    pub crate_type: String,
    /// Id of the entry point, if the crate has one
    pub main: Option<String>,
    /// The crate's own functions
    pub nodes: Vec<Node>,
    /// By id. Either end may be an item this crate does not define: a
    /// function of another crate, a trait method, a type.
    pub edges: Vec<Edge>,
}

/// The context a body refers to an item in.
#[derive(Serialize, Deserialize, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[serde(rename_all = "lowercase")]
pub enum EdgeKind {
    /// Compiled code: the item is called, constructed, or used as a value
    Call,
    /// A `requires`, `ensures`, `recommends`, or `returns` clause, or the
    /// spec a function stands for in ghost code (`when_used_as_spec`, type
    /// invariants)
    Contract,
    /// Other ghost code: assertions, proof blocks, loop invariants,
    /// decreases clauses
    Proof,
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Edge {
    pub from: String,
    pub to: String,
    pub kind: EdgeKind,
}

impl Edge {
    pub fn new(from: impl Into<String>, to: impl Into<String>, kind: EdgeKind) -> Edge {
        Edge { from: from.into(), to: to.into(), kind }
    }
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Node {
    /// Canonical name, the same from every crate that refers to this item
    pub id: String,
    /// Name for display and for matching globs
    pub def_path: String,
    /// The module the function is defined in
    pub module: String,
    pub span: Span,
    pub mode: String,
    /// Verus checks this function. Whether the check passed is the exit
    /// status of the verus run.
    pub verified: bool,
    /// The body is not checked: `external_body`, the target of an
    /// `assume_specification`, or an uninterpreted spec
    pub external_body: bool,
    /// Stands for another function: an `assume_specification` item, or the
    /// twin `verus!` gives a `const fn`
    pub proxy: bool,
    /// Part of the crate's public API
    pub exported: bool,
    /// Marked `#[verifier::reach_root]`: always a root of the analysis
    #[serde(default)]
    pub root: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Span {
    pub file: String,
    pub start_line: usize,
    pub end_line: usize,
}

impl Node {
    /// The functions coverage counts: verified exec code with a real body,
    /// and every spec and proof function.
    pub fn is_verified(&self) -> bool {
        self.is_verified_exec() || self.is_ghost()
    }

    /// The functions we want wired in: verified exec code with a real body.
    pub fn is_verified_exec(&self) -> bool {
        self.verified && self.mode == "exec" && !self.external_body && !self.proxy
    }

    /// The ghost functions we want used: spec and proof functions, with or
    /// without a body.
    pub fn is_ghost(&self) -> bool {
        self.mode != "exec"
    }

    /// A ghost function whose claim is assumed, not checked: an
    /// `external_body` proof function (an axiom) or an uninterpreted spec.
    /// Counted as verified, since the proofs around it rely on it, but
    /// labeled.
    pub fn is_trusted(&self) -> bool {
        self.is_ghost() && self.external_body
    }

    /// Not code the user wrote: an `assume_specification` proxy, the twin
    /// `verus!` gives a `const fn`, the twin holding a trait method's spec,
    /// or a helper `reveal` synthesizes. Newer reports leave most of these
    /// out; older ones carry them.
    pub fn is_synthesized(&self) -> bool {
        let name = self.name();
        self.proxy
            || name.starts_with("VERUS_UNERASED_PROXY__")
            || name.starts_with("VERUS_SPEC__")
            || name.ends_with("__VERUS_REVEAL_INTERNAL__")
    }

    pub fn name(&self) -> &str {
        self.def_path.rfind("::").map_or(&self.def_path, |i| &self.def_path[i + 2..])
    }

    /// The function's place in the module tree. Differs from `def_path` for
    /// methods, which `def_path` files under their type.
    pub fn module_path(&self) -> String {
        format!("{}::{}", self.module, self.name())
    }
}

impl Report {
    pub fn file_name(&self) -> String {
        format!("{}.{}.json", self.krate, self.crate_type)
    }

    /// `name (type)`, for display
    pub fn label(&self) -> String {
        format!("{} ({})", self.krate, self.crate_type)
    }
}

/// Reads reports from files and directories of `*.json` files. A directory
/// keeps the report of a crate that was renamed or removed, so clear it
/// when the set of crates changes.
pub fn load(paths: &[PathBuf]) -> Result<Vec<Report>, String> {
    let mut files = vec![];
    for path in paths {
        if path.is_dir() {
            let dir = std::fs::read_dir(path).map_err(|e| format!("{}: {e}", path.display()))?;
            let mut json: Vec<PathBuf> = dir
                .filter_map(|entry| entry.ok().map(|e| e.path()))
                .filter(|p| p.extension().map_or(false, |x| x == "json"))
                .collect();
            json.sort();
            files.extend(json);
        } else {
            files.push(path.clone());
        }
    }
    let reports: Vec<Report> = files.iter().map(|f| load_file(f)).collect::<Result<_, _>>()?;
    // A test build holds the library's functions again, under another id
    for test in reports.iter().filter(|r| r.crate_type == "test") {
        if reports.iter().any(|r| r.krate == test.krate && r.crate_type != "test") {
            return Err(format!(
                "crate `{}` has both a test report and a lib or bin report: a test build \
                 includes the library's functions, which would count twice; keep one",
                test.krate
            ));
        }
    }
    Ok(reports)
}

fn load_file(path: &Path) -> Result<Report, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let report: Report =
        serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
    if report.schema_version != SCHEMA_VERSION {
        return Err(format!(
            "{}: schema version {} (expected {SCHEMA_VERSION})",
            path.display(),
            report.schema_version
        ));
    }
    Ok(report)
}

/// How to pick the roots of the reachability analysis. Functions marked
/// `#[verifier::reach_root]` are always roots.
pub struct Roots {
    /// Def paths to add
    pub add: Vec<String>,
    /// Globs removing implicit roots, matched against `def_path` and
    /// `module_path`
    pub exclude: Vec<glob::Pattern>,
    /// Take the implicit roots too: the `main` of every executable crate,
    /// or, when no crate has one, every exported function
    pub implicit: bool,
}

impl Default for Roots {
    fn default() -> Roots {
        Roots { add: vec![], exclude: vec![], implicit: true }
    }
}

impl Roots {
    fn excludes(&self, node: &Node) -> bool {
        self.exclude.iter().any(|g| g.matches(&node.def_path) || g.matches(&node.module_path()))
    }
}

/// The merged reports of all crates.
pub struct Graph {
    /// Every function the user wrote, of every crate, by id. Synthesized
    /// items (see [`Node::is_synthesized`]) are left out; their edges stay.
    pub nodes: BTreeMap<String, Node>,
    pub roots: Vec<String>,
    /// Runs: reached from a root through calls only
    pub reachable: HashSet<String>,
    /// Used by ghost code: reached from a running function through a
    /// contract or proof, then through anything
    pub used: HashSet<String>,
    /// The reachable and used functions, plus whatever mentions them or is
    /// mentioned by them, transitively, through edges between functions in
    /// either direction. Edges to types and to other crates' items are not
    /// walked: everything constructs an `Option` or holds an `Expression`,
    /// and walking those backwards would join the whole crate. The rest of
    /// this set is where explicit roots hide: theorems about reachable
    /// functions that nothing calls.
    pub connected: HashSet<String>,
    /// Ids some function refers to
    referred: HashSet<String>,
    /// Ghost functions whose contract is stated in the vocabulary of the
    /// reachable code: it mentions a reachable verified exec function, a
    /// spec the contract of one is stated in, or a spec those are defined
    /// by. Sharing a helper lemma or a utility spec does not count.
    states_reached: HashSet<String>,
}

impl Graph {
    /// Roots are the functions marked `#[verifier::reach_root]`, plus, unless
    /// `roots.implicit` is off, the `main` of every executable crate, or,
    /// when no crate has one, every exported function.
    pub fn new(reports: &[Report], roots: &Roots) -> Result<Graph, String> {
        let nodes: BTreeMap<String, Node> = reports
            .iter()
            .flat_map(|r| r.nodes.iter())
            .filter(|n| !n.is_synthesized())
            .map(|n| (n.id.clone(), n.clone()))
            .collect();
        let mains: Vec<String> = reports.iter().filter_map(|r| r.main.clone()).collect();
        let implicit: Vec<&Node> = if !roots.implicit {
            vec![]
        } else if mains.is_empty() {
            nodes.values().filter(|n| n.exported).collect()
        } else {
            mains.iter().filter_map(|id| nodes.get(id)).collect()
        };
        let mut root_ids: Vec<String> =
            implicit.into_iter().filter(|n| !roots.excludes(n)).map(|n| n.id.clone()).collect();
        root_ids.extend(nodes.values().filter(|n| n.root).map(|n| n.id.clone()));
        for def_path in &roots.add {
            let added: Vec<&Node> = nodes.values().filter(|n| &n.def_path == def_path).collect();
            if added.is_empty() {
                return Err(format!("--root {def_path}: no such function"));
            }
            root_ids.extend(added.iter().map(|n| n.id.clone()));
        }
        root_ids.sort();
        root_ids.dedup();

        let mut out: HashMap<&str, Vec<&Edge>> = HashMap::new();
        for edge in reports.iter().flat_map(|r| r.edges.iter()) {
            out.entry(&edge.from).or_default().push(edge);
        }

        // One search in two contexts. A call from running code runs its
        // target; anything referenced from ghost code, or from something
        // ghost code reached, is only used. A spec or proof function is
        // ghost code whatever context it was entered in: a ghost root, or
        // a dispatch edge to a spec-mode impl method.
        let mut reachable = HashSet::new();
        let mut used = HashSet::new();
        let mut queue: VecDeque<(&str, bool)> = VecDeque::new();
        for root in &root_ids {
            if reachable.insert(root.clone()) {
                queue.push_back((root, false));
            }
        }
        while let Some((id, ghost)) = queue.pop_front() {
            let ghost = ghost || nodes.get(id).map_or(false, |n| n.is_ghost());
            for edge in out.get(id).map_or(&[][..], |v| v) {
                let ghost = ghost || edge.kind != EdgeKind::Call;
                let set = if ghost { &mut used } else { &mut reachable };
                if set.insert(edge.to.clone()) {
                    queue.push_back((&edge.to, ghost));
                }
            }
        }

        // From everything reached, ignore direction and context, but only
        // between functions of the analyzed crates
        let mut adjacent: HashMap<&str, Vec<&str>> = HashMap::new();
        let mut referred = HashSet::new();
        for edge in reports.iter().flat_map(|r| r.edges.iter()) {
            if nodes.contains_key(&edge.from) {
                referred.insert(edge.to.clone());
                if nodes.contains_key(&edge.to) {
                    adjacent.entry(&edge.from).or_default().push(&edge.to);
                    adjacent.entry(&edge.to).or_default().push(&edge.from);
                }
            }
        }
        let covered: Vec<&String> = nodes
            .values()
            .filter(|n| reachable.contains(&n.id) || (n.is_ghost() && used.contains(&n.id)))
            .map(|n| &n.id)
            .collect();
        let mut connected: HashSet<String> = covered.iter().map(|id| (*id).clone()).collect();
        let mut queue: VecDeque<&str> = covered.iter().map(|id| id.as_str()).collect();
        while let Some(id) = queue.pop_front() {
            for next in adjacent.get(id).map_or(&[][..], |v| v) {
                if connected.insert(next.to_string()) {
                    queue.push_back(next);
                }
            }
        }

        // The vocabulary the reachable code's contracts are stated in
        let mut vocabulary: HashSet<String> = nodes
            .values()
            .filter(|n| n.is_verified_exec() && reachable.contains(&n.id))
            .map(|n| n.id.clone())
            .collect();
        let mut queue: VecDeque<String> = vocabulary.iter().cloned().collect();
        while let Some(id) = queue.pop_front() {
            let from_exec = nodes.get(&id).map_or(false, |n| !n.is_ghost());
            for edge in out.get(id.as_str()).map_or(&[][..], |v| v) {
                let spec = nodes.get(&edge.to).map_or(false, |n| n.mode == "spec");
                if spec && (!from_exec || edge.kind == EdgeKind::Contract) {
                    if vocabulary.insert(edge.to.clone()) {
                        queue.push_back(edge.to.clone());
                    }
                }
            }
        }
        let states_reached: HashSet<String> = nodes
            .values()
            .filter(|n| n.is_ghost())
            .filter(|n| {
                out.get(n.id.as_str()).map_or(false, |edges| {
                    edges.iter().any(|e| e.kind == EdgeKind::Contract && vocabulary.contains(&e.to))
                })
            })
            .map(|n| n.id.clone())
            .collect();
        Ok(Graph { nodes, roots: root_ids, reachable, used, connected, referred, states_reached })
    }

    /// Verified functions connected to reached code but not reachable: what
    /// the roots miss, one step of direction away.
    pub fn connected_unreachable(&self) -> Vec<&Node> {
        self.nodes
            .values()
            .filter(|n| n.is_verified() && self.connected.contains(&n.id) && !self.is_reachable(n))
            .collect()
    }

    /// Candidates for `#[verifier::reach_root]`: ghost functions that
    /// nothing refers to, so they are top-level statements, whose contract
    /// is stated about reachable code (see `states_reached`). Being merely
    /// connected is not enough: a theorem about a dead printer shares helper
    /// lemmas and utility specs with the parser without saying anything
    /// about it.
    pub fn suggested_roots(&self) -> Vec<&Node> {
        self.connected_unreachable()
            .into_iter()
            .filter(|n| {
                n.is_ghost()
                    && !self.referred.contains(&n.id)
                    && self.states_reached.contains(&n.id)
            })
            .collect()
    }

    /// An exec function is reachable when it runs; a ghost function, when
    /// running code uses it.
    pub fn is_reachable(&self, node: &Node) -> bool {
        self.reachable.contains(&node.id) || (node.is_ghost() && self.used.contains(&node.id))
    }

    /// The roots, by display name
    pub fn root_names(&self) -> Vec<&str> {
        self.roots.iter().map(|id| self.nodes[id].def_path.as_str()).collect()
    }

    /// Verified functions, exec and ghost: (reachable, total)
    pub fn coverage(&self) -> (usize, usize) {
        self.count(Node::is_verified)
    }

    /// Verified exec functions: (reachable, total)
    pub fn exec_coverage(&self) -> (usize, usize) {
        self.count(Node::is_verified_exec)
    }

    /// Ghost functions: (used, total)
    pub fn ghost_coverage(&self) -> (usize, usize) {
        self.count(Node::is_ghost)
    }

    fn count(&self, select: fn(&Node) -> bool) -> (usize, usize) {
        let fns = self.nodes.values().filter(|n| select(n));
        let total = fns.clone().count();
        (fns.filter(|n| self.is_reachable(n)).count(), total)
    }
}

/// Hand-built reports for tests.
#[doc(hidden)]
pub mod fixture {
    use super::*;

    pub fn node(id: &str, verified: bool, exported: bool) -> Node {
        let module = id.rfind("::").map_or("", |i| &id[..i]).to_string();
        Node {
            id: id.to_string(),
            def_path: id.to_string(),
            module,
            span: Span { file: "x.rs".into(), start_line: 1, end_line: 3 },
            mode: "exec".into(),
            verified,
            external_body: false,
            proxy: false,
            exported,
            root: false,
        }
    }

    pub fn spec(id: &str) -> Node {
        let mut n = node(id, true, false);
        n.mode = "spec".into();
        n
    }

    pub fn proof(id: &str) -> Node {
        let mut n = node(id, true, false);
        n.mode = "proof".into();
        n
    }

    pub fn call(from: &str, to: &str) -> Edge {
        Edge::new(from, to, EdgeKind::Call)
    }

    pub fn contract(from: &str, to: &str) -> Edge {
        Edge::new(from, to, EdgeKind::Contract)
    }

    pub fn report(
        krate: &str,
        crate_type: &str,
        main: Option<&str>,
        nodes: Vec<Node>,
        edges: Vec<Edge>,
    ) -> Report {
        Report {
            schema_version: SCHEMA_VERSION,
            krate: krate.into(),
            crate_type: crate_type.into(),
            main: main.map(String::from),
            nodes,
            edges,
        }
    }

    /// A library with a wired verified function and a public verified twin
    /// of an unverified one, and a binary whose main calls only the wired
    /// and unverified ones. The wired function's contract uses one spec
    /// and its body a lemma; the twin's contract uses another spec.
    pub fn lib_and_bin() -> Vec<Report> {
        let lib = report(
            "lib",
            "lib",
            None,
            vec![
                node("lib::wired", true, true),
                node("lib::verified::inc", true, true),
                node("lib::inc", false, true),
                node("lib::helper", true, false),
                spec("lib::spec_wired"),
                spec("lib::verified::spec_inc"),
                proof("lib::lemma"),
            ],
            vec![
                call("lib::wired", "lib::helper"),
                contract("lib::wired", "lib::spec_wired"),
                Edge::new("lib::wired", "lib::lemma", EdgeKind::Proof),
                contract("lib::verified::inc", "lib::verified::spec_inc"),
            ],
        );
        let bin = report(
            "app",
            "bin",
            Some("app(bin)::main"),
            vec![node("app(bin)::main", false, false)],
            vec![call("app(bin)::main", "lib::wired"), call("app(bin)::main", "lib::inc")],
        );
        vec![lib, bin]
    }
}

#[cfg(test)]
mod tests {
    use super::fixture::*;
    use super::*;

    #[test]
    fn main_reaches_into_other_crate() {
        let graph = Graph::new(&lib_and_bin(), &Roots::default()).unwrap();
        assert_eq!(graph.roots, vec!["app(bin)::main"]);
        assert!(graph.reachable.contains("lib::wired"));
        assert!(graph.reachable.contains("lib::helper"));
        assert!(!graph.reachable.contains("lib::verified::inc"));
        assert_eq!(graph.exec_coverage(), (2, 3));
        assert!(graph.used.contains("lib::spec_wired"));
        assert!(graph.used.contains("lib::lemma"));
        assert!(!graph.used.contains("lib::verified::spec_inc"));
        assert_eq!(graph.ghost_coverage(), (2, 3));
        // Coverage counts exec, spec, and proof functions alike
        assert_eq!(graph.coverage(), (4, 6));
    }

    #[test]
    fn ghost_context_uses_but_does_not_run() {
        // main's contract names a spec, which is defined in terms of an exec
        // function (`when_used_as_spec`) and a lemma's ensures
        let lib = report(
            "lib",
            "bin",
            Some("lib(bin)::main"),
            vec![
                node("lib(bin)::main", true, false),
                node("lib(bin)::exec_len", true, false),
                spec("lib(bin)::spec_len"),
                spec("lib(bin)::by_lemma"),
                spec("lib(bin)::dead"),
                proof("lib(bin)::lemma"),
            ],
            vec![
                contract("lib(bin)::main", "lib(bin)::exec_len"),
                contract("lib(bin)::exec_len", "lib(bin)::spec_len"),
                Edge::new("lib(bin)::main", "lib(bin)::lemma", EdgeKind::Proof),
                contract("lib(bin)::lemma", "lib(bin)::by_lemma"),
                call("lib(bin)::dead", "lib(bin)::spec_len"),
            ],
        );
        let graph = Graph::new(&[lib], &Roots::default()).unwrap();
        assert!(!graph.reachable.contains("lib(bin)::exec_len"));
        assert!(!graph.is_reachable(&graph.nodes["lib(bin)::exec_len"]));
        assert!(graph.is_reachable(&graph.nodes["lib(bin)::spec_len"]));
        assert!(graph.is_reachable(&graph.nodes["lib(bin)::by_lemma"]));
        assert!(!graph.is_reachable(&graph.nodes["lib(bin)::dead"]));
        assert!(graph.is_reachable(&graph.nodes["lib(bin)::lemma"]));
        assert_eq!(graph.ghost_coverage(), (3, 4));
    }

    #[test]
    fn exported_items_are_roots_without_a_main() {
        let lib = lib_and_bin().remove(0);
        let graph = Graph::new(&[lib], &Roots::default()).unwrap();
        assert_eq!(graph.roots, vec!["lib::inc", "lib::verified::inc", "lib::wired"]);
        assert!(graph.reachable.contains("lib::verified::inc"));
    }

    #[test]
    fn marked_roots_are_always_roots() {
        // A theorem about `wired`, never called, marked as a root
        let mut reports = lib_and_bin();
        let mut theorem = proof("lib::theorem");
        theorem.root = true;
        reports[0].nodes.push(theorem);
        reports[0].edges.push(contract("lib::theorem", "lib::verified::spec_inc"));
        let graph = Graph::new(&reports, &Roots::default()).unwrap();
        assert_eq!(graph.roots, vec!["app(bin)::main", "lib::theorem"]);
        assert!(graph.is_reachable(&graph.nodes["lib::verified::spec_inc"]));
        assert!(!graph.reachable.contains("lib::verified::spec_inc"));

        // Without implicit roots only the theorem is a root, and nothing runs
        let roots = Roots { implicit: false, ..Roots::default() };
        let graph = Graph::new(&reports, &roots).unwrap();
        assert_eq!(graph.roots, vec!["lib::theorem"]);
        assert!(!graph.is_reachable(&graph.nodes["lib::wired"]));
        assert_eq!(graph.exec_coverage(), (0, 3));

        // An exclusion glob does not remove a marked root
        let roots =
            Roots { exclude: vec![glob::Pattern::new("lib::*").unwrap()], ..Roots::default() };
        let graph = Graph::new(&reports, &roots).unwrap();
        assert_eq!(graph.roots, vec!["app(bin)::main", "lib::theorem"]);
    }

    #[test]
    fn connected_holds_the_reachable_and_the_theorems_about_it() {
        // A theorem about `wired`, and a lemma the theorem uses; neither is
        // called. A spec about the unreachable twin is connected to nothing.
        let mut reports = lib_and_bin();
        reports[0].nodes.push(proof("lib::theorem"));
        reports[0].nodes.push(proof("lib::lemma_for_theorem"));
        reports[0].edges.push(contract("lib::theorem", "lib::spec_wired"));
        reports[0].edges.push(Edge::new("lib::theorem", "lib::lemma_for_theorem", EdgeKind::Proof));
        let graph = Graph::new(&reports, &Roots::default()).unwrap();
        for n in graph.nodes.values().filter(|n| graph.is_reachable(n)) {
            assert!(graph.connected.contains(&n.id), "{} reachable but not connected", n.id);
        }
        assert!(graph.connected.contains("lib::theorem"));
        assert!(graph.connected.contains("lib::lemma_for_theorem"));
        assert!(!graph.connected.contains("lib::verified::spec_inc"));
        fn names(v: Vec<&Node>) -> Vec<&str> {
            v.iter().map(|n| n.id.as_str()).collect()
        }
        assert_eq!(
            names(graph.connected_unreachable()),
            vec!["lib::lemma_for_theorem", "lib::theorem"]
        );
        assert_eq!(names(graph.suggested_roots()), vec!["lib::theorem"]);
    }

    #[test]
    fn exclude_and_add_roots() {
        let lib = lib_and_bin().remove(0);
        let roots = Roots {
            add: vec!["lib::helper".into()],
            exclude: vec![glob::Pattern::new("lib::verified::*").unwrap()],
            implicit: true,
        };
        let graph = Graph::new(&[lib], &roots).unwrap();
        assert_eq!(graph.roots, vec!["lib::helper", "lib::inc", "lib::wired"]);
        assert!(!graph.reachable.contains("lib::verified::inc"));
    }

    #[test]
    fn exclude_matches_the_module_of_a_method() {
        // `def_path` files a method under its type (`lib::Wrapper::fmt`),
        // which may be defined in another module than the impl
        let mut method = node("lib::verified::impl&%0::fmt", true, true);
        method.def_path = "lib::Wrapper::fmt".into();
        method.module = "lib::verified".into();
        let lib = report("lib", "lib", None, vec![method], vec![]);
        let roots = Roots {
            exclude: vec![glob::Pattern::new("lib::verified::*").unwrap()],
            ..Roots::default()
        };
        assert!(Graph::new(&[lib], &roots).unwrap().roots.is_empty());
    }

    #[test]
    fn unknown_root_is_an_error() {
        let roots = Roots { add: vec!["lib::nope".into()], ..Roots::default() };
        assert!(Graph::new(&lib_and_bin(), &roots).is_err());
    }

    #[test]
    fn a_ghost_root_uses_but_never_runs() {
        // An exported spec fn, defined through a `when_used_as_spec` exec fn
        let lib = report(
            "lib",
            "lib",
            None,
            vec![
                {
                    let mut n = spec("lib::spec_len");
                    n.exported = true;
                    n
                },
                node("lib::len", true, false),
            ],
            vec![call("lib::spec_len", "lib::len")],
        );
        let graph = Graph::new(&[lib], &Roots::default()).unwrap();
        assert_eq!(graph.roots, vec!["lib::spec_len"]);
        assert!(!graph.reachable.contains("lib::len"));
        assert!(graph.used.contains("lib::len"));
        assert!(!graph.is_reachable(&graph.nodes["lib::len"]));
    }

    #[test]
    fn synthesized_items_are_not_nodes_but_keep_their_edges() {
        let mut twin = node("lib::Tr::VERUS_SPEC__m", false, false);
        twin.def_path = "lib::Tr::VERUS_SPEC__m".into();
        let mut helper = node("lib::f::__VERUS_REVEAL_INTERNAL__", false, false);
        helper.def_path = "lib::f::__VERUS_REVEAL_INTERNAL__".into();
        let mut proxy = node("lib::ext_spec", true, false);
        proxy.proxy = true;
        let lib = report(
            "lib",
            "bin",
            Some("lib(bin)::main"),
            vec![node("lib(bin)::main", false, false), twin, helper, proxy, spec("lib::p")],
            vec![
                call("lib(bin)::main", "lib::Tr::m"),
                contract("lib::Tr::m", "lib::Tr::VERUS_SPEC__m"),
                contract("lib::Tr::VERUS_SPEC__m", "lib::p"),
            ],
        );
        let graph = Graph::new(&[lib], &Roots::default()).unwrap();
        let ids: Vec<&String> = graph.nodes.keys().collect();
        assert_eq!(ids, vec!["lib(bin)::main", "lib::p"]);
        assert!(graph.is_reachable(&graph.nodes["lib::p"]));
    }

    #[test]
    fn a_test_report_beside_the_library_is_rejected() {
        let dir = tempfile::tempdir().unwrap();
        for (name, ty) in [("lib", "lib"), ("lib", "test")] {
            let r = report(name, ty, None, vec![], vec![]);
            std::fs::write(dir.path().join(r.file_name()), serde_json::to_string(&r).unwrap())
                .unwrap();
        }
        let err = load(&[dir.path().to_path_buf()]).unwrap_err();
        assert!(err.contains("test report"), "{err}");
    }

    #[test]
    fn trusted_ghost_functions_are_labeled() {
        let mut axiom = proof("lib::axiom");
        axiom.external_body = true;
        assert!(axiom.is_trusted() && axiom.is_verified());
        let mut ext = node("lib::ext", true, false);
        ext.external_body = true;
        assert!(!ext.is_trusted() && !ext.is_verified());
    }

    #[test]
    fn trait_call_fans_out_through_the_defining_crate() {
        // The binary calls a trait method; only the library knows its impls.
        let lib = report(
            "lib",
            "lib",
            None,
            vec![node("lib::impl&%0::fmt", true, false)],
            vec![call("core::fmt::Display::fmt", "lib::impl&%0::fmt")],
        );
        let bin = report(
            "app",
            "bin",
            Some("app(bin)::main"),
            vec![node("app(bin)::main", false, false)],
            vec![call("app(bin)::main", "core::fmt::Display::fmt")],
        );
        let graph = Graph::new(&[lib, bin], &Roots::default()).unwrap();
        assert!(graph.reachable.contains("lib::impl&%0::fmt"));
    }
}
