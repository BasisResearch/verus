//! Dynamic verified coverage: joining the run-time profiles written by
//! `vstd::contrib::dyncov` with the static reports.
//!
//! A profile counts, per wrapped function, its calls and the verdicts of
//! its lowered `requires` (and, for `external_body` functions, `ensures`),
//! plus the verified frames that were on the stack when a trusted
//! assumption was observed false ("tainted"). This module merges the
//! profiles of all processes, matches each function to its static node by
//! the `file:line` of its definition, classifies every false precondition
//! by the caller's static label, and computes the sets of §2 of the
//! design: D (called) and T (true verified reachable), over the static
//! denominator V and next to the static S.

use crate::{Graph, Node};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};

pub const PROFILE_SCHEMA_VERSION: u32 = 1;

/// One process's profile, as written by the runtime.
#[derive(Serialize, Deserialize, Debug, Clone, Default)]
pub struct Profile {
    pub schema_version: u32,
    /// By `file:line:name`
    pub functions: BTreeMap<String, FnProfile>,
    #[serde(default)]
    pub tainted: BTreeMap<String, u64>,
    #[serde(default)]
    pub trust_violations: BTreeMap<String, u64>,
    /// By `assume@file:line:col`, `[true, unknown, false]`
    #[serde(default)]
    pub assumes: BTreeMap<String, [u64; 3]>,
}

#[derive(Serialize, Deserialize, Debug, Clone, Default)]
pub struct FnProfile {
    #[serde(default)]
    pub path: String,
    pub calls: u64,
    /// `[true, unknown, false]`
    pub pre: [u64; 3],
    #[serde(default)]
    pub post: [u64; 3],
    #[serde(default)]
    pub pre_false_sites: BTreeMap<String, u64>,
    #[serde(default)]
    pub pre_unknown_reasons: BTreeMap<String, u64>,
    #[serde(default)]
    pub post_unknown_reasons: BTreeMap<String, u64>,
    /// Per clause (`pre:0`, `post:1`, ...)
    #[serde(default)]
    pub clauses: BTreeMap<String, [u64; 3]>,
}

fn add_counts(into: &mut BTreeMap<String, u64>, from: &BTreeMap<String, u64>) {
    for (k, v) in from {
        *into.entry(k.clone()).or_default() += v;
    }
}

fn add_triple(into: &mut [u64; 3], from: &[u64; 3]) {
    for i in 0..3 {
        into[i] += from[i];
    }
}

impl Profile {
    /// Sums another process's counters into this one.
    pub fn merge(&mut self, other: &Profile) {
        for (id, f) in &other.functions {
            let g = self.functions.entry(id.clone()).or_default();
            if g.path.is_empty() {
                g.path = f.path.clone();
            }
            g.calls += f.calls;
            add_triple(&mut g.pre, &f.pre);
            add_triple(&mut g.post, &f.post);
            add_counts(&mut g.pre_false_sites, &f.pre_false_sites);
            add_counts(&mut g.pre_unknown_reasons, &f.pre_unknown_reasons);
            add_counts(&mut g.post_unknown_reasons, &f.post_unknown_reasons);
            for (k, v) in &f.clauses {
                add_triple(g.clauses.entry(k.clone()).or_default(), v);
            }
        }
        add_counts(&mut self.tainted, &other.tainted);
        add_counts(&mut self.trust_violations, &other.trust_violations);
        for (k, v) in &other.assumes {
            add_triple(self.assumes.entry(k.clone()).or_default(), v);
        }
    }
}

/// Reads and merges profiles from files and directories (every
/// `dyncov*.json` in a directory).
pub fn load_profiles(paths: &[PathBuf]) -> Result<Profile, String> {
    let mut files = vec![];
    for path in paths {
        if path.is_dir() {
            let dir = std::fs::read_dir(path).map_err(|e| format!("{}: {e}", path.display()))?;
            let mut json: Vec<PathBuf> = dir
                .filter_map(|entry| entry.ok().map(|e| e.path()))
                .filter(|p| {
                    p.extension().map_or(false, |x| x == "json")
                        && p.file_name()
                            .map_or(false, |n| n.to_string_lossy().starts_with("dyncov"))
                })
                .collect();
            json.sort();
            files.extend(json);
        } else {
            files.push(path.clone());
        }
    }
    if files.is_empty() {
        return Err("no dyncov profiles found".into());
    }
    let mut merged = Profile { schema_version: PROFILE_SCHEMA_VERSION, ..Default::default() };
    for file in &files {
        merged.merge(&load_profile(file)?);
    }
    Ok(merged)
}

fn load_profile(path: &Path) -> Result<Profile, String> {
    let text = std::fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let profile: Profile =
        serde_json::from_str(&text).map_err(|e| format!("{}: {e}", path.display()))?;
    if profile.schema_version != PROFILE_SCHEMA_VERSION {
        return Err(format!(
            "{}: profile schema version {} (expected {PROFILE_SCHEMA_VERSION})",
            path.display(),
            profile.schema_version
        ));
    }
    Ok(profile)
}

/// A function's `file:line:name` id, split.
fn parse_fn_id(id: &str) -> Option<(&str, usize, &str)> {
    let (rest, name) = id.rsplit_once(':')?;
    let (file, line) = rest.rsplit_once(':')?;
    Some((file, line.parse().ok()?, name))
}

/// `path:line:col` of a call site
fn parse_site(site: &str) -> Option<(&str, usize)> {
    let (rest, _col) = site.rsplit_once(':')?;
    let (file, line) = rest.rsplit_once(':')?;
    Some((file, line.parse().ok()?))
}

fn same_file(a: &str, b: &str) -> bool {
    // The runtime reports `file!()`, the static side the diagnostics
    // file name; both are the path rustc was given, but tolerate one being
    // a suffix of the other (different working directories)
    a == b || a.ends_with(&format!("/{b}")) || b.ends_with(&format!("/{a}"))
}

/// A false precondition at a call site, classified by the caller.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Violation {
    /// The caller is a verified exec function: Verus proved the
    /// precondition there, so the lowering disagrees with Verus. A tool
    /// error; does not affect coverage but fails the run.
    LoweringDisagreement { site: String, caller: String, count: u64 },
    /// The caller is unverified (or unknown): the program uses the
    /// function outside its verified domain.
    Violation { site: String, caller: Option<String>, count: u64 },
}

/// Why a called function is not in T.
#[derive(Debug, Clone)]
pub struct Exclusion {
    pub violations: Vec<Violation>,
    pub tainted: u64,
}

/// The dynamic sets, over the static graph.
pub struct Dynamic {
    /// Id → canonical id (see [`canonical_ids`])
    pub canonical: HashMap<String, String>,
    /// Static node id → merged profile of the function
    pub profiled: BTreeMap<String, FnProfile>,
    /// D: called at least once
    pub called: BTreeSet<String>,
    /// T: in D, never a false precondition, never tainted
    pub true_reachable: BTreeSet<String>,
    /// D \ T, with the reason
    pub excluded: BTreeMap<String, Exclusion>,
    pub lowering_disagreements: Vec<(String, Violation)>,
    /// Profile ids no static node matched
    pub unmatched: Vec<String>,
    /// Static id → number of tainted pops
    pub tainted: BTreeMap<String, u64>,
    /// Sources of trust violations (a trusted fn's static id or its raw
    /// profile key, or `assume@...`) with counts
    pub trust_violations: BTreeMap<String, u64>,
    pub assumes: BTreeMap<String, [u64; 3]>,
}

impl Dynamic {
    pub fn new(graph: &Graph, profile: &Profile) -> Dynamic {
        // Index static nodes by (file, start line)
        let mut by_span: HashMap<(String, usize), Vec<&Node>> = HashMap::new();
        for n in graph.nodes.values() {
            by_span.entry((n.span.file.clone(), n.span.start_line)).or_default().push(n);
        }
        // Several nodes may start on one line (a one-line impl); the
        // name decides, else the first
        let find_node = |file: &str, line: usize, name: &str| -> Option<&Node> {
            let candidates: Vec<&Node> = by_span
                .iter()
                .filter(|((f, l), _)| *l == line && same_file(f, file))
                .flat_map(|(_, v)| v.iter().copied())
                .collect();
            candidates
                .iter()
                .copied()
                .find(|n| n.name() == name)
                .or_else(|| candidates.first().copied())
        };
        let node_containing = |file: &str, line: usize| -> Option<&Node> {
            graph
                .nodes
                .values()
                .filter(|n| {
                    same_file(&n.span.file, file)
                        && n.span.start_line <= line
                        && line <= n.span.end_line
                })
                // The innermost function (nested fns are rare; pick the
                // latest start)
                .max_by_key(|n| n.span.start_line)
        };

        let canonical = graph.canonical.clone();
        let mut profiled: BTreeMap<String, FnProfile> = BTreeMap::new();
        let mut unmatched = vec![];
        let mut key_to_id: HashMap<String, String> = HashMap::new();
        for (id, f) in &profile.functions {
            match parse_fn_id(id).and_then(|(file, line, name)| find_node(file, line, name)) {
                Some(node) => {
                    let cid = canonical[&node.id].clone();
                    key_to_id.insert(id.clone(), cid.clone());
                    profiled.entry(cid).or_default().merge_into(f);
                }
                None => unmatched.push(id.clone()),
            }
        }

        let mut tainted: BTreeMap<String, u64> = BTreeMap::new();
        for (id, n) in &profile.tainted {
            match key_to_id.get(id) {
                Some(sid) => *tainted.entry(sid.clone()).or_default() += n,
                None => unmatched.push(id.clone()),
            }
        }
        let mut trust_violations: BTreeMap<String, u64> = BTreeMap::new();
        for (id, n) in &profile.trust_violations {
            let key = key_to_id.get(id).cloned().unwrap_or_else(|| id.clone());
            *trust_violations.entry(key).or_default() += n;
        }
        unmatched.sort();
        unmatched.dedup();

        let mut called = BTreeSet::new();
        let mut true_reachable = BTreeSet::new();
        let mut excluded = BTreeMap::new();
        let mut lowering_disagreements = vec![];
        for (id, f) in &profiled {
            let node = &graph.nodes[id];
            if !node.is_verified_exec() || f.calls == 0 {
                continue;
            }
            called.insert(id.clone());
            let mut violations = vec![];
            for (site, count) in &f.pre_false_sites {
                let caller = parse_site(site).and_then(|(file, line)| node_containing(file, line));
                match caller {
                    Some(c) if c.is_verified_exec() => {
                        let v = Violation::LoweringDisagreement {
                            site: site.clone(),
                            caller: c.def_path.clone(),
                            count: *count,
                        };
                        lowering_disagreements.push((id.clone(), v));
                    }
                    c => violations.push(Violation::Violation {
                        site: site.clone(),
                        caller: c.map(|c| c.def_path.clone()),
                        count: *count,
                    }),
                }
            }
            let taint = tainted.get(id).copied().unwrap_or(0);
            if violations.is_empty() && taint == 0 {
                true_reachable.insert(id.clone());
            } else {
                excluded.insert(id.clone(), Exclusion { violations, tainted: taint });
            }
        }

        Dynamic {
            canonical,
            profiled,
            called,
            true_reachable,
            excluded,
            lowering_disagreements,
            unmatched,
            tainted,
            trust_violations,
            assumes: profile.assumes.clone(),
        }
    }

    /// Verified exec functions: (in T, total)
    pub fn coverage(&self, graph: &Graph) -> (usize, usize) {
        (self.true_reachable.len(), self.nodes(graph).filter(|n| n.is_verified_exec()).count())
    }

    /// The nodes counted once: every canonical node
    pub fn nodes<'a>(&'a self, graph: &'a Graph) -> impl Iterator<Item = &'a Node> + 'a {
        graph.counted()
    }

    /// Statically reachable through any of its copies
    pub fn static_reachable(&self, graph: &Graph, node: &Node) -> bool {
        graph.is_reachable_any(node)
    }

    /// The hit count LCOV shows: calls with a precondition that was not
    /// false, for functions in T; 0 otherwise.
    pub fn hits(&self, node: &Node) -> u64 {
        if !self.true_reachable.contains(&node.id) {
            return 0;
        }
        self.profiled
            .get(&node.id)
            .map_or(0, |f| f.pre[0] + f.pre[1] + (f.calls - f.pre.iter().sum::<u64>()))
    }

    /// Functions in S \ D that have an executed static caller: a workload
    /// gap rather than a static over-approximation.
    pub fn has_called_caller(
        &self,
        graph: &Graph,
        callers: &HashMap<&str, Vec<&str>>,
        id: &str,
    ) -> bool {
        callers.get(id).map_or(false, |cs| {
            cs.iter().any(|c| {
                self.called.contains(*c)
                    || graph.roots.iter().any(|r| r == c)
                    || graph.nodes.get(*c).map_or(false, |n| {
                        !n.is_verified_exec()
                            && graph.reachable.contains(*c)
                            && self.profiled.is_empty()
                    })
            })
        })
    }
}

impl FnProfile {
    fn merge_into(&mut self, other: &FnProfile) {
        let mut tmp = Profile::default();
        tmp.functions.insert("x".into(), std::mem::take(self));
        let mut o = Profile::default();
        o.functions.insert("x".into(), other.clone());
        tmp.merge(&o);
        *self = tmp.functions.remove("x").unwrap();
    }
}

/// Functions the LLVM export saw run, matched to static nodes by file
/// and line: the executed functions, verified or not.
pub fn llvm_executed(
    graph: &Graph,
    export: &serde_json::Value,
) -> Result<BTreeSet<String>, String> {
    let mut executed = BTreeSet::new();
    let data = export.get("data").and_then(|d| d.as_array()).ok_or("llvm export: no data")?;
    for d in data {
        let Some(functions) = d.get("functions").and_then(|f| f.as_array()) else { continue };
        for f in functions {
            let count = f.get("count").and_then(|c| c.as_u64()).unwrap_or(0);
            if count == 0 {
                continue;
            }
            let files: Vec<&str> = f
                .get("filenames")
                .and_then(|x| x.as_array())
                .map_or(vec![], |a| a.iter().filter_map(|s| s.as_str()).collect());
            let Some(regions) = f.get("regions").and_then(|r| r.as_array()) else { continue };
            let Some(first) = regions.first().and_then(|r| r.as_array()) else { continue };
            let line = first.first().and_then(|l| l.as_u64()).unwrap_or(0) as usize;
            let file_index = first.get(6).and_then(|i| i.as_u64()).unwrap_or(0) as usize;
            let Some(file) = files.get(file_index) else { continue };
            for n in graph.nodes.values() {
                if same_file(&n.span.file, file)
                    && n.span.start_line <= line
                    && line <= n.span.end_line
                {
                    executed.insert(n.id.clone());
                }
            }
        }
    }
    Ok(executed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Roots;
    use crate::fixture::*;

    fn profile(entries: &[(&str, u64, [u64; 3], &[(&str, u64)])]) -> Profile {
        let mut p = Profile { schema_version: 1, ..Default::default() };
        for (id, calls, pre, sites) in entries {
            let mut f = FnProfile { calls: *calls, pre: *pre, ..Default::default() };
            for (s, n) in sites.iter() {
                f.pre_false_sites.insert(s.to_string(), *n);
            }
            p.functions.insert(id.to_string(), f);
        }
        p
    }

    /// wired at x.rs:1-3 (default fixture), helper at 10-12, inc at 20-22,
    /// main (unverified) at 30-40
    fn graph() -> Graph {
        let mut reports = lib_and_bin();
        for n in reports[0].nodes.iter_mut() {
            match n.id.as_str() {
                "lib::helper" => n.span.start_line = 10,
                "lib::verified::inc" => n.span.start_line = 20,
                _ => {}
            }
            n.span.end_line = n.span.start_line + 2;
        }
        reports[1].nodes[0].span.start_line = 30;
        reports[1].nodes[0].span.end_line = 40;
        Graph::new(&reports, &Roots::default()).unwrap()
    }

    #[test]
    fn matches_by_file_and_line_and_computes_sets() {
        let g = graph();
        let p = profile(&[
            ("x.rs:1:wired", 3, [3, 0, 0], &[]),
            ("x.rs:10:helper", 2, [1, 1, 0], &[]),
            ("src/x.rs:20:inc", 1, [0, 0, 1], &[("x.rs:35:5", 1)]),
            ("y.rs:7:nope", 1, [1, 0, 0], &[]),
        ]);
        let d = Dynamic::new(&g, &p);
        assert_eq!(d.unmatched, vec!["y.rs:7:nope"]);
        assert!(d.called.contains("lib::wired"));
        assert!(d.called.contains("lib::helper"));
        assert!(d.called.contains("lib::verified::inc"));
        // Unknown counts as covered; a false pre from unverified main is a violation
        assert!(d.true_reachable.contains("lib::wired"));
        assert!(d.true_reachable.contains("lib::helper"));
        assert!(!d.true_reachable.contains("lib::verified::inc"));
        let ex = &d.excluded["lib::verified::inc"];
        assert!(
            matches!(&ex.violations[0], Violation::Violation { caller: Some(c), count: 1, .. } if c == "app(bin)::main")
        );
        assert!(d.lowering_disagreements.is_empty());
        assert_eq!(d.coverage(&g), (2, 3));
        assert_eq!(d.hits(&g.nodes["lib::helper"]), 2);
        assert_eq!(d.hits(&g.nodes["lib::verified::inc"]), 0);
    }

    #[test]
    fn false_pre_from_verified_caller_is_a_lowering_disagreement() {
        let g = graph();
        let p = profile(&[("x.rs:10:helper", 1, [0, 0, 1], &[("x.rs:2:9", 1)])]);
        let d = Dynamic::new(&g, &p);
        assert_eq!(d.lowering_disagreements.len(), 1);
        assert!(
            matches!(&d.lowering_disagreements[0].1, Violation::LoweringDisagreement { caller, .. } if caller == "lib::wired")
        );
        // Does not affect coverage
        assert!(d.true_reachable.contains("lib::helper"));
    }

    #[test]
    fn taint_excludes_and_mixed_calls_exclude() {
        let g = graph();
        let mut p = profile(&[
            ("x.rs:1:wired", 2, [1, 0, 1], &[("x.rs:35:5", 1)]),
            ("x.rs:10:helper", 1, [1, 0, 0], &[]),
        ]);
        p.tainted.insert("x.rs:10:helper".into(), 1);
        p.trust_violations.insert("assume@x.rs:11:3".into(), 1);
        let d = Dynamic::new(&g, &p);
        assert!(!d.true_reachable.contains("lib::wired"));
        assert!(!d.true_reachable.contains("lib::helper"));
        assert_eq!(d.excluded["lib::helper"].tainted, 1);
        assert_eq!(d.trust_violations["assume@x.rs:11:3"], 1);
        assert_eq!(d.coverage(&g), (0, 3));
    }

    #[test]
    fn a_test_crate_copy_of_the_library_counts_once() {
        // The library's unit-test build reports the same functions under
        // `lib(test)::`, reachable from the harness main; the lib copy is
        // canonical, and reachability through either copy counts
        let mut reports = lib_and_bin();
        for n in reports[0].nodes.iter_mut() {
            match n.id.as_str() {
                "lib::helper" => n.span.start_line = 10,
                "lib::verified::inc" => n.span.start_line = 20,
                "lib::inc" => n.span.start_line = 30,
                _ => {}
            }
        }
        let mut test_report = reports[0].clone();
        test_report.crate_type = "test".into();
        test_report.main = Some("lib(test)::main".into());
        for n in test_report.nodes.iter_mut() {
            n.id = n.id.replace("lib::", "lib(test)::");
        }
        test_report.nodes.push(node("lib(test)::main", false, false));
        test_report.edges = vec![call("lib(test)::main", "lib(test)::verified::inc")];
        reports.push(test_report);
        let g = Graph::new(&reports, &Roots::default()).unwrap();
        let p = profile(&[("x.rs:20:inc", 1, [1, 0, 0], &[])]);
        let d = Dynamic::new(&g, &p);
        assert_eq!(d.canonical["lib(test)::wired"], "lib::wired");
        assert_eq!(d.coverage(&g), (1, 3));
        assert!(d.called.contains("lib::verified::inc"));
        assert!(d.static_reachable(&g, &g.nodes["lib::verified::inc"]));
        assert!(
            !d.static_reachable(&g, &g.nodes["lib::helper"])
                || g.is_reachable(&g.nodes["lib::helper"])
        );
        assert_eq!(d.nodes(&g).filter(|n| n.is_verified_exec()).count(), 3);
    }

    #[test]
    fn profiles_merge_by_summing() {
        let mut a = profile(&[("x.rs:1:wired", 1, [1, 0, 0], &[("s", 0)])]);
        let b = profile(&[
            ("x.rs:1:wired", 2, [0, 1, 1], &[("s", 1)]),
            ("x.rs:10:helper", 1, [1, 0, 0], &[]),
        ]);
        a.merge(&b);
        assert_eq!(a.functions["x.rs:1:wired"].calls, 3);
        assert_eq!(a.functions["x.rs:1:wired"].pre, [1, 1, 1]);
        assert_eq!(a.functions["x.rs:1:wired"].pre_false_sites["s"], 1);
        assert_eq!(a.functions.len(), 2);
    }
}
