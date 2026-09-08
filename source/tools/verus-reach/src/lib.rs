//! Static reachability of verified code, across crates.
//!
//! `verus --reach DIR` writes one [`Report`] per crate: the crate's functions
//! with Verus's labels, and the edges out of every body, each labeled with
//! the context of the reference: a call, a contract, or a proof. Edges may
//! name items in other crates. This library merges the reports of all
//! crates and computes what is reachable from the chosen roots: which
//! functions run, and which ghost functions the running code's contracts
//! and proofs use.

use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::path::{Path, PathBuf};

pub const SCHEMA_VERSION: u32 = 3;

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
    pub external_body: bool,
    pub proxy: bool,
    /// Part of the crate's public API
    pub exported: bool,
}

#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct Span {
    pub file: String,
    pub start_line: usize,
    pub end_line: usize,
}

impl Node {
    /// The functions we want wired in: verified exec code with a real body.
    pub fn is_verified_exec(&self) -> bool {
        self.verified && self.mode == "exec" && !self.external_body && !self.proxy
    }

    /// Ghost code: a spec or proof function.
    pub fn is_ghost(&self) -> bool {
        self.mode != "exec"
    }

    /// The specs we want used: spec functions, with or without a body.
    pub fn is_spec(&self) -> bool {
        self.verified && self.mode == "spec" && !self.proxy
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
    files.iter().map(|f| load_file(f)).collect()
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

/// How to pick the roots of the reachability analysis.
#[derive(Default)]
pub struct Roots {
    /// Def paths to add
    pub add: Vec<String>,
    /// Globs removing default roots, matched against `def_path` and
    /// `module_path`
    pub exclude: Vec<glob::Pattern>,
}

impl Roots {
    fn excludes(&self, node: &Node) -> bool {
        self.exclude.iter().any(|g| g.matches(&node.def_path) || g.matches(&node.module_path()))
    }
}

/// The merged reports of all crates.
pub struct Graph {
    /// Every function of every crate, by id
    pub nodes: BTreeMap<String, Node>,
    pub roots: Vec<String>,
    /// Runs: reached from a root through calls only
    pub reachable: HashSet<String>,
    /// Used by ghost code: reached from a running function through a
    /// contract or proof, then through anything
    pub used: HashSet<String>,
}

impl Graph {
    /// Default roots are the `main` of every executable crate, or, when no
    /// crate has one, every exported function.
    pub fn new(reports: &[Report], roots: &Roots) -> Result<Graph, String> {
        let nodes: BTreeMap<String, Node> = reports
            .iter()
            .flat_map(|r| r.nodes.iter())
            .map(|n| (n.id.clone(), n.clone()))
            .collect();
        let mains: Vec<String> = reports.iter().filter_map(|r| r.main.clone()).collect();
        let defaults: Vec<&Node> = if mains.is_empty() {
            nodes.values().filter(|n| n.exported).collect()
        } else {
            mains.iter().filter_map(|id| nodes.get(id)).collect()
        };
        let mut root_ids: Vec<String> =
            defaults.into_iter().filter(|n| !roots.excludes(n)).map(|n| n.id.clone()).collect();
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
        // ghost code reached, is only used.
        let mut reachable = HashSet::new();
        let mut used = HashSet::new();
        let mut queue: VecDeque<(&str, bool)> = VecDeque::new();
        for root in &root_ids {
            if reachable.insert(root.clone()) {
                queue.push_back((root, false));
            }
        }
        while let Some((id, ghost)) = queue.pop_front() {
            for edge in out.get(id).map_or(&[][..], |v| v) {
                let ghost = ghost || edge.kind != EdgeKind::Call;
                let set = if ghost { &mut used } else { &mut reachable };
                if set.insert(edge.to.clone()) {
                    queue.push_back((&edge.to, ghost));
                }
            }
        }
        Ok(Graph { nodes, roots: root_ids, reachable, used })
    }

    /// An exec function is reachable when it runs; a ghost function, when
    /// running code uses it.
    pub fn is_reachable(&self, node: &Node) -> bool {
        self.reachable.contains(&node.id) || (node.is_ghost() && self.used.contains(&node.id))
    }

    /// Verified exec functions: (reachable, total)
    pub fn coverage(&self) -> (usize, usize) {
        self.count(Node::is_verified_exec)
    }

    /// Spec functions: (used, total)
    pub fn spec_coverage(&self) -> (usize, usize) {
        self.count(Node::is_spec)
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
    /// and unverified ones. The wired function's contract uses one spec;
    /// the twin's uses another.
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
        assert_eq!(graph.coverage(), (2, 3));
        assert!(graph.used.contains("lib::spec_wired"));
        assert!(!graph.used.contains("lib::verified::spec_inc"));
        assert_eq!(graph.spec_coverage(), (1, 2));
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
        assert_eq!(graph.spec_coverage(), (2, 3));
    }

    #[test]
    fn exported_items_are_roots_without_a_main() {
        let lib = lib_and_bin().remove(0);
        let graph = Graph::new(&[lib], &Roots::default()).unwrap();
        assert_eq!(graph.roots, vec!["lib::inc", "lib::verified::inc", "lib::wired"]);
        assert!(graph.reachable.contains("lib::verified::inc"));
    }

    #[test]
    fn exclude_and_add_roots() {
        let lib = lib_and_bin().remove(0);
        let roots = Roots {
            add: vec!["lib::helper".into()],
            exclude: vec![glob::Pattern::new("lib::verified::*").unwrap()],
        };
        let graph = Graph::new(&[lib], &roots).unwrap();
        assert_eq!(graph.roots, vec!["lib::helper", "lib::inc", "lib::wired"]);
        assert!(!graph.reachable.contains("lib::verified::inc"));
    }

    #[test]
    fn exclude_matches_the_module_of_a_method() {
        // `def_path` files a method under its type, which may live elsewhere
        let mut method = node("lib::verified::impl&%0::fmt", true, true);
        method.def_path = "core::fmt::Display::fmt".into();
        method.module = "lib::verified".into();
        let lib = report("lib", "lib", None, vec![method], vec![]);
        let roots =
            Roots { add: vec![], exclude: vec![glob::Pattern::new("lib::verified::*").unwrap()] };
        assert!(Graph::new(&[lib], &roots).unwrap().roots.is_empty());
    }

    #[test]
    fn unknown_root_is_an_error() {
        let roots = Roots { add: vec!["lib::nope".into()], exclude: vec![] };
        assert!(Graph::new(&lib_and_bin(), &roots).is_err());
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
