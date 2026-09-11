//! Renders the reports written by `verus --reach DIR`.
//!
//!   verus-reach DIR...            text summary
//!   verus-reach --lcov DIR...     LCOV, for grcov, genhtml, Codecov, IDE gutters
//!   verus-reach --html OUT DIR...  a directory of pages like genhtml's:
//!                                 the files with verified code and their
//!                                 sources, rated by the share of verified
//!                                 functions nothing reaches and the share
//!                                 of reachable functions that are verified
//!   verus-reach --dynamic PROFILES DIR...
//!                                 the same, joined with the profiles of a
//!                                 `verus --dyncov` run: a verified exec
//!                                 function counts as reachable only when
//!                                 it ran with its precondition holding and
//!                                 untainted (add --diff, --spec-report,
//!                                 --lcov, --html)
//!
//! Pass every crate's report (a directory of them, or files) so that calls
//! across crates are followed.

mod html;

use clap::Parser;
use std::collections::BTreeMap;
use std::collections::{BTreeSet, HashMap};
use std::fmt::Write;
use std::path::PathBuf;
use verus_reach::dyncov::{Dynamic, Violation};
use verus_reach::{Graph, Node, Report, Roots};

#[derive(Parser)]
struct Args {
    /// Report files or directories of reports. Clear a directory when
    /// crates are renamed or removed; old reports are not overwritten.
    #[arg(required = true)]
    reports: Vec<PathBuf>,
    /// Add a root (def path). Defaults: `main` of every executable crate,
    /// or every exported function if there is none
    #[arg(long = "root")]
    roots: Vec<String>,
    /// Remove default roots matching a glob, e.g. 'mycrate::verified::*'
    #[arg(long = "roots-exclude")]
    roots_exclude: Vec<String>,
    /// Exit with an error if fewer than this percentage of verified
    /// functions (exec, spec, and proof) are reachable
    #[arg(long)]
    fail_under: Option<u64>,
    /// Write an LCOV trace file to stdout instead of the summary
    #[arg(long, conflicts_with = "html")]
    lcov: bool,
    /// Write an HTML report into this directory (index.html and a page per
    /// file) instead of printing the summary
    #[arg(long, value_name = "OUT")]
    html: Option<PathBuf>,
    /// With --html, the directory the crates were compiled from, where the
    /// source files named by the reports are read for the source views
    #[arg(long, default_value = ".")]
    src: PathBuf,
    /// With --html, the title of the report
    #[arg(long, default_value = "verus-reach")]
    title: String,
    /// With --lcov, include only verified exec functions
    #[arg(long, conflicts_with = "only_verified")]
    only_verified_exec: bool,
    /// With --lcov, include only verified exec, spec, and proof functions
    #[arg(long)]
    only_verified: bool,
    /// Dynamic coverage: profiles written by a `verus --dyncov` build
    /// (files, or directories of `dyncov*.json`). The summary, --lcov and
    /// --fail-under then report true verified reachable functions
    #[arg(long = "dynamic", value_name = "PROFILE", value_delimiter = ',')]
    dynamic: Vec<PathBuf>,
    /// With --dynamic, an `llvm-cov export` JSON of the same run, to also
    /// count the executed functions that are not verified
    #[arg(long, requires = "dynamic")]
    llvm_export: Option<PathBuf>,
    /// With --dynamic, list the differences between the static and dynamic
    /// sets instead of the summary
    #[arg(long, requires = "dynamic")]
    diff: bool,
    /// With --dynamic, list every contract clause with its verdict counts
    /// instead of the summary
    #[arg(long, requires = "dynamic")]
    spec_report: bool,
}

/// Which functions an LCOV trace covers.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Only {
    All,
    Verified,
    VerifiedExec,
}

impl Only {
    fn includes(self, node: &Node) -> bool {
        match self {
            Only::All => true,
            Only::Verified => node.is_verified(),
            Only::VerifiedExec => node.is_verified_exec(),
        }
    }
}

fn pct(part: usize, total: usize) -> u64 {
    (100 * part).checked_div(total).map_or(100, |p| p as u64)
}

fn loc(node: &Node) -> usize {
    node.span.end_line - node.span.start_line + 1
}

fn summary(reports: &[Report], graph: &Graph) -> String {
    let mut out = String::new();
    let crates: Vec<String> =
        reports.iter().map(|r| format!("{} ({})", r.krate, r.crate_type)).collect();
    writeln!(out, "crates: {}", crates.join(", ")).unwrap();
    let roots: Vec<&str> = graph.roots.iter().map(|id| graph.nodes[id].def_path.as_str()).collect();
    match roots.len() {
        0..=3 => writeln!(out, "roots: {}", roots.join(", ")).unwrap(),
        n => writeln!(out, "roots: {n} functions").unwrap(),
    }

    let fns: Vec<&Node> = graph.nodes.values().filter(|n| n.is_verified()).collect();
    let reached: Vec<&Node> = fns.iter().copied().filter(|n| graph.is_reachable(n)).collect();
    writeln!(
        out,
        "\nverified functions: {:>6}   reachable: {:>6}  ({}%)",
        fns.len(),
        reached.len(),
        pct(reached.len(), fns.len())
    )
    .unwrap();
    for mode in ["exec", "spec", "proof"] {
        let total = fns.iter().filter(|n| n.mode == mode).count();
        let hit = reached.iter().filter(|n| n.mode == mode).count();
        writeln!(out, "  {mode:<17} {total:>6}   reachable: {hit:>6}  ({}%)", pct(hit, total))
            .unwrap();
    }
    let total_loc: usize = fns.iter().map(|n| loc(n)).sum();
    let reached_loc: usize = reached.iter().map(|n| loc(n)).sum();
    writeln!(
        out,
        "verified LoC:       {:>6}   reachable: {:>6}  ({}%)",
        total_loc,
        reached_loc,
        pct(reached_loc, total_loc)
    )
    .unwrap();
    writeln!(out, "(LoC counts every line of the function, including proof blocks)").unwrap();
    writeln!(
        out,
        "(an exec function is reachable when it runs; a spec or proof function, when the ghost code of reachable code mentions it)"
    )
    .unwrap();

    // (reachable fns, fns, reachable loc, loc, reachable exec, exec, used ghosts, ghosts) per module
    let mut modules: BTreeMap<&str, [usize; 8]> = BTreeMap::new();
    for f in &fns {
        let m = modules.entry(&f.module).or_default();
        let hit = graph.is_reachable(f) as usize;
        m[0] += hit;
        m[1] += 1;
        m[2] += hit * loc(f);
        m[3] += loc(f);
        let (r, t) = if f.is_ghost() { (6, 7) } else { (4, 5) };
        m[r] += hit;
        m[t] += 1;
    }
    writeln!(out, "\nby module:").unwrap();
    let width = modules.keys().map(|m| m.len()).max().unwrap_or(0);
    for (module, [rf, tf, rl, tl, re, te, rg, tg]) in &modules {
        writeln!(
            out,
            "  {module:width$}  {rf:>4}/{tf:<4} fns  {rl:>6}/{tl:<6} LoC  {re:>4}/{te:<4} exec  {rg:>4}/{tg:<4} ghost"
        )
        .unwrap();
    }

    let unreachable: Vec<&Node> = fns.iter().copied().filter(|n| !graph.is_reachable(n)).collect();
    if !unreachable.is_empty() {
        writeln!(out, "\nunreachable verified functions:").unwrap();
    }
    for f in unreachable {
        writeln!(out, "  {}:{}   {:<5} {}", f.span.file, f.span.start_line, f.mode, f.name())
            .unwrap();
    }
    out
}

fn lcov(graph: &Graph, only: Only) -> String {
    use lcov::report::section::{function, line};
    let mut report = lcov::Report::new();
    for n in graph.nodes.values().filter(|n| only.includes(n)) {
        let hits = graph.is_reachable(n) as u64;
        let key = lcov::report::section::Key {
            test_name: String::new(),
            source_file: PathBuf::from(&n.span.file),
        };
        let section = report.sections.entry(key).or_default();
        section.functions.insert(
            function::Key { name: n.id.clone() },
            function::Value { start_line: Some(n.span.start_line as u32), count: hits },
        );
        for l in n.span.start_line..=n.span.end_line {
            section.lines.entry(line::Key { line: l as u32 }).or_default().count |= hits;
        }
    }
    report.into_records().map(|record| format!("{record}\n")).collect()
}

fn dynamic_summary(
    reports: &[Report],
    graph: &Graph,
    dynamic: &Dynamic,
    llvm: Option<&BTreeSet<String>>,
) -> String {
    let mut out = String::new();
    let crates: Vec<String> =
        reports.iter().map(|r| format!("{} ({})", r.krate, r.crate_type)).collect();
    writeln!(out, "crates: {}", crates.join(", ")).unwrap();
    let fns: Vec<&Node> = dynamic.nodes(graph).filter(|n| n.is_verified_exec()).collect();
    let v = fns.len();
    let s = fns.iter().filter(|n| dynamic.static_reachable(graph, n)).count();
    let d = dynamic.called.len();
    let t = dynamic.true_reachable.len();
    writeln!(out, "\nverified exec functions (V):        {v:>6}").unwrap();
    writeln!(out, "statically reachable (S):           {s:>6}  ({}% of V)", pct(s, v)).unwrap();
    writeln!(out, "called (D):                         {d:>6}  ({}% of V)", pct(d, v)).unwrap();
    writeln!(out, "true verified reachable (T):        {t:>6}  ({}% of V)", pct(t, v)).unwrap();
    writeln!(
        out,
        "(T: called, precondition never false, never tainted by a false trusted ensures or assume)"
    )
    .unwrap();
    if let Some(executed) = llvm {
        let all = graph.nodes.len();
        writeln!(out, "executed functions (LLVM, any mode): {:>5} of {all}", executed.len())
            .unwrap();
    }

    // (S, D, T, V) per module
    let mut modules: BTreeMap<&str, [usize; 4]> = BTreeMap::new();
    for f in &fns {
        let m = modules.entry(&f.module).or_default();
        m[3] += 1;
        m[0] += dynamic.static_reachable(graph, f) as usize;
        m[1] += dynamic.called.contains(&f.id) as usize;
        m[2] += dynamic.true_reachable.contains(&f.id) as usize;
    }
    writeln!(out, "\nby module:").unwrap();
    let width = modules.keys().map(|m| m.len()).max().unwrap_or(0);
    for (module, [s, d, t, v]) in &modules {
        writeln!(out, "  {module:width$}  S {s:>4}/{v:<4} D {d:>4}/{v:<4} T {t:>4}/{v:<4}")
            .unwrap();
    }

    let not_true: Vec<&Node> =
        fns.iter().copied().filter(|n| !dynamic.true_reachable.contains(&n.id)).collect();
    if !not_true.is_empty() {
        writeln!(out, "\nverified exec functions not in T:").unwrap();
    }
    for f in not_true {
        let why = if let Some(ex) = dynamic.excluded.get(&f.id) {
            let mut parts = vec![];
            if !ex.violations.is_empty() {
                parts.push(format!("precondition false at {} call site(s)", ex.violations.len()));
            }
            if ex.tainted > 0 {
                parts.push(format!("tainted {} time(s)", ex.tainted));
            }
            parts.join(", ")
        } else if dynamic.static_reachable(graph, f) {
            "statically reachable, never called".to_string()
        } else {
            "unreachable".to_string()
        };
        writeln!(out, "  {}:{}   {}   ({why})", f.span.file, f.span.start_line, f.name()).unwrap();
    }
    out.push_str(&trust_findings(graph, dynamic));
    out.push_str(&diagnostics(graph, dynamic, llvm));
    out
}

fn trust_findings(graph: &Graph, dynamic: &Dynamic) -> String {
    let mut out = String::new();
    let trusted: Vec<(&Node, &verus_reach::dyncov::FnProfile)> = dynamic
        .profiled
        .iter()
        .filter_map(|(id, f)| graph.nodes.get(id).map(|n| (n, f)))
        .filter(|(n, f)| n.external_body && f.post.iter().sum::<u64>() > 0)
        .collect();
    if !trusted.is_empty() || !dynamic.trust_violations.is_empty() {
        writeln!(out, "\ntrust findings:").unwrap();
    }
    for (n, f) in trusted {
        writeln!(
            out,
            "  {}:{}   {}   ensures [true {}, unknown {}, false {}]",
            n.span.file,
            n.span.start_line,
            n.name(),
            f.post[0],
            f.post[1],
            f.post[2]
        )
        .unwrap();
    }
    for (source, count) in &dynamic.trust_violations {
        let name = graph.nodes.get(source).map_or(source.clone(), |n| {
            format!("{}:{}   {}", n.span.file, n.span.start_line, n.name())
        });
        writeln!(out, "  violated {count} time(s): {name}").unwrap();
    }
    for (site, counts) in &dynamic.assumes {
        writeln!(
            out,
            "  {site}   [true {}, unknown {}, false {}]",
            counts[0], counts[1], counts[2]
        )
        .unwrap();
    }
    out
}

fn diagnostics(graph: &Graph, dynamic: &Dynamic, llvm: Option<&BTreeSet<String>>) -> String {
    let mut out = String::new();
    let missed: Vec<&String> = dynamic
        .called
        .iter()
        .filter(|id| !dynamic.static_reachable(graph, &graph.nodes[*id]))
        .collect();
    let mut lines = vec![];
    for id in &dynamic.unmatched {
        lines.push(format!("profile id matches no static function: {id}"));
    }
    for id in missed {
        let n = &graph.nodes[id];
        lines.push(format!(
            "called but not statically reachable from the roots (a workload root the static graph lacks, e.g. a test, or a missed static edge): {}:{}   {}",
            n.span.file,
            n.span.start_line,
            n.name()
        ));
    }
    for (id, v) in &dynamic.lowering_disagreements {
        if let Violation::LoweringDisagreement { site, caller, count } = v {
            let n = &graph.nodes[id];
            lines.push(format!(
                "LOWERING DISAGREEMENT: {} precondition false {count} time(s) at {site} in verified {caller}",
                n.name()
            ));
        }
    }
    if let Some(executed) = llvm {
        for id in &dynamic.called {
            if !executed.contains(id) {
                let n = &graph.nodes[id];
                lines.push(format!(
                    "counted by dyncov but not by LLVM: {}:{}   {}",
                    n.span.file,
                    n.span.start_line,
                    n.name()
                ));
            }
        }
    }
    if !lines.is_empty() {
        writeln!(out, "\ndiagnostics:").unwrap();
        for l in lines {
            writeln!(out, "  {l}").unwrap();
        }
    }
    out
}

fn dynamic_diff(graph: &Graph, dynamic: &Dynamic) -> String {
    let mut out = String::new();
    let mut callers: HashMap<&str, Vec<&str>> = HashMap::new();
    fn canon<'a>(dynamic: &'a Dynamic, id: &'a str) -> &'a str {
        dynamic.canonical.get(id).map_or(id, |c| c.as_str())
    }
    for edge in graph.edges() {
        if edge.kind == verus_reach::EdgeKind::Call {
            callers.entry(canon(dynamic, &edge.to)).or_default().push(canon(dynamic, &edge.from));
        }
    }
    let fns: Vec<&Node> = dynamic.nodes(graph).filter(|n| n.is_verified_exec()).collect();
    let loc = |n: &Node| format!("{}:{}   {}", n.span.file, n.span.start_line, n.name());

    let s_not_d: Vec<&Node> = fns
        .iter()
        .copied()
        .filter(|n| dynamic.static_reachable(graph, n) && !dynamic.called.contains(&n.id))
        .collect();
    let (gap, over): (Vec<&Node>, Vec<&Node>) = s_not_d.into_iter().partition(|n| {
        callers.get(n.id.as_str()).map_or(false, |cs| {
            cs.iter().any(|c| dynamic.called.contains(*c) || graph.roots.iter().any(|r| r == c))
        })
    });
    writeln!(
        out,
        "S \\ D, never called with an executed static caller (workload gap): {}",
        gap.len()
    )
    .unwrap();
    for n in gap {
        writeln!(out, "  {}", loc(n)).unwrap();
    }
    writeln!(out, "\nS \\ D, never called and no executed static caller (likely static over-approximation): {}", over.len()).unwrap();
    for n in over {
        writeln!(out, "  {}", loc(n)).unwrap();
    }
    let violated: Vec<(&Node, &verus_reach::dyncov::Exclusion)> = dynamic
        .excluded
        .iter()
        .filter(|(_, ex)| !ex.violations.is_empty())
        .map(|(id, ex)| (&graph.nodes[id], ex))
        .collect();
    writeln!(out, "\nD \\ T, precondition violated: {}", violated.len()).unwrap();
    for (n, ex) in violated {
        writeln!(out, "  {}", loc(n)).unwrap();
        for v in &ex.violations {
            if let Violation::Violation { site, caller, count } = v {
                writeln!(
                    out,
                    "      {count} time(s) at {site} in {}",
                    caller.as_deref().unwrap_or("unknown caller")
                )
                .unwrap();
            }
        }
    }
    let tainted: Vec<(&Node, u64)> = dynamic
        .excluded
        .iter()
        .filter(|(_, ex)| ex.tainted > 0)
        .map(|(id, ex)| (&graph.nodes[id], ex.tainted))
        .collect();
    writeln!(out, "\nD \\ T, tainted: {}", tainted.len()).unwrap();
    for (n, count) in tainted {
        writeln!(out, "  {}   {count} time(s)", loc(n)).unwrap();
    }
    if !dynamic.trust_violations.is_empty() {
        writeln!(out, "  sources:").unwrap();
        for (source, count) in &dynamic.trust_violations {
            let name = graph.nodes.get(source).map_or(source.clone(), |n| loc(n));
            writeln!(out, "      {name}   false {count} time(s)").unwrap();
        }
    }
    let d_not_s: Vec<&Node> = fns
        .iter()
        .copied()
        .filter(|n| dynamic.called.contains(&n.id) && !dynamic.static_reachable(graph, n))
        .collect();
    writeln!(
        out,
        "\nD \\ S, called but not statically reachable from the roots (workload roots the static graph lacks, or missed static edges): {}",
        d_not_s.len()
    )
    .unwrap();
    for n in d_not_s {
        writeln!(out, "  {}", loc(n)).unwrap();
    }
    out
}

fn spec_report(graph: &Graph, dynamic: &Dynamic) -> String {
    let mut out = String::new();
    writeln!(out, "contract clauses, [true, unknown, false] per evaluation:").unwrap();
    for (id, f) in &dynamic.profiled {
        let Some(n) = graph.nodes.get(id) else { continue };
        if f.clauses.is_empty() && f.pre_unknown_reasons.is_empty() {
            continue;
        }
        writeln!(out, "  {}:{}   {}   calls {}", n.span.file, n.span.start_line, n.name(), f.calls)
            .unwrap();
        for (clause, c) in &f.clauses {
            writeln!(out, "      {clause:<8} [{}, {}, {}]", c[0], c[1], c[2]).unwrap();
        }
        for (reason, count) in &f.pre_unknown_reasons {
            writeln!(out, "      requires unknown: {reason} ({count})").unwrap();
        }
        for (reason, count) in &f.post_unknown_reasons {
            writeln!(out, "      ensures unknown: {reason} ({count})").unwrap();
        }
    }
    out
}

fn dynamic_lcov(graph: &Graph, dynamic: &Dynamic, only: Only) -> String {
    use lcov::report::section::{function, line};
    let mut report = lcov::Report::new();
    for n in dynamic.nodes(graph).filter(|n| only.includes(n)) {
        let hits = if n.is_verified_exec() {
            dynamic.hits(n)
        } else if n.is_ghost() {
            dynamic.static_reachable(graph, n) as u64
        } else {
            dynamic.profiled.get(&n.id).map_or(0, |f| f.calls)
        };
        let key = lcov::report::section::Key {
            test_name: String::new(),
            source_file: PathBuf::from(&n.span.file),
        };
        let section = report.sections.entry(key).or_default();
        section.functions.insert(
            function::Key { name: n.id.clone() },
            function::Value { start_line: Some(n.span.start_line as u32), count: hits },
        );
        for l in n.span.start_line..=n.span.end_line {
            let entry = section.lines.entry(line::Key { line: l as u32 }).or_default();
            entry.count = entry.count.max(hits);
        }
        // Each contract clause is a branch point on its own line: branch 0
        // is the clause holding, branch 1 the clause failing, branch 2 the
        // clause being unknown
        if let Some(f) = dynamic.profiled.get(&n.id) {
            for (i, (clause, counts)) in f.clauses.iter().enumerate() {
                let Some((_, line)) = clause.split_once('@') else { continue };
                let Ok(line) = line.parse::<u32>() else { continue };
                for (branch, taken) in [(0, counts[0]), (1, counts[2]), (2, counts[1])] {
                    section.branches.insert(
                        lcov::report::section::branch::Key { line, block: i as u32, branch },
                        lcov::report::section::branch::Value { taken: Some(taken) },
                    );
                }
            }
        }
    }
    report.into_records().map(|record| format!("{record}\n")).collect()
}

fn below_threshold(graph: &Graph, threshold: u64) -> Option<String> {
    let (reached, total) = graph.coverage();
    let pct = pct(reached, total);
    (pct < threshold).then(|| {
        format!(
            "{reached} of {total} verified functions reachable ({pct}%), below --fail-under {threshold}"
        )
    })
}

fn fail(msg: String) -> ! {
    eprintln!("verus-reach: {msg}");
    std::process::exit(1)
}

fn main() {
    let args = Args::parse();
    let reports = verus_reach::load(&args.reports).unwrap_or_else(|e| fail(e));
    let roots = Roots {
        add: args.roots,
        exclude: args
            .roots_exclude
            .iter()
            .map(|g| glob::Pattern::new(g).unwrap_or_else(|e| fail(format!("bad glob {g}: {e}"))))
            .collect(),
    };
    let graph = Graph::new(&reports, &roots).unwrap_or_else(|e| fail(e));
    let only = if args.only_verified_exec {
        Only::VerifiedExec
    } else if args.only_verified {
        Only::Verified
    } else {
        Only::All
    };
    if !args.dynamic.is_empty() {
        let profile = verus_reach::dyncov::load_profiles(&args.dynamic).unwrap_or_else(|e| fail(e));
        let dynamic = Dynamic::new(&graph, &profile);
        let llvm = args.llvm_export.as_ref().map(|path| {
            let text = std::fs::read_to_string(path)
                .unwrap_or_else(|e| fail(format!("{}: {e}", path.display())));
            let json: serde_json::Value = serde_json::from_str(&text)
                .unwrap_or_else(|e| fail(format!("{}: {e}", path.display())));
            verus_reach::dyncov::llvm_executed(&graph, &json).unwrap_or_else(|e| fail(e))
        });
        if let Some(out) = &args.html {
            html::write(&reports, &graph, Some(&dynamic), &args.src, &args.title, out)
                .unwrap_or_else(|e| fail(e));
            eprintln!("verus-reach: wrote {}", out.join("index.html").display());
        } else {
            let text = if args.lcov {
                dynamic_lcov(&graph, &dynamic, only)
            } else if args.diff {
                dynamic_diff(&graph, &dynamic)
            } else if args.spec_report {
                spec_report(&graph, &dynamic)
            } else {
                dynamic_summary(&reports, &graph, &dynamic, llvm.as_ref())
            };
            print!("{text}");
        }
        if !dynamic.lowering_disagreements.is_empty() {
            fail(format!(
                "{} lowering disagreement(s): a precondition Verus proved was observed false (see diagnostics)",
                dynamic.lowering_disagreements.len()
            ));
        }
        if let Some(threshold) = args.fail_under {
            let (t, v) = dynamic.coverage(&graph);
            let pct = pct(t, v);
            if pct < threshold {
                fail(format!(
                    "{t} of {v} verified exec functions true verified reachable ({pct}%), below --fail-under {threshold}"
                ));
            }
        }
        return;
    }
    if let Some(out) = &args.html {
        html::write(&reports, &graph, None, &args.src, &args.title, out)
            .unwrap_or_else(|e| fail(e));
        eprintln!("verus-reach: wrote {}", out.join("index.html").display());
    } else {
        let text = if args.lcov { lcov(&graph, only) } else { summary(&reports, &graph) };
        print!("{text}");
    }
    if let Some(msg) = args.fail_under.and_then(|t| below_threshold(&graph, t)) {
        fail(msg);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use verus_reach::fixture::lib_and_bin;

    fn graph() -> (Vec<Report>, Graph) {
        let reports = lib_and_bin();
        let graph = Graph::new(&reports, &Roots::default()).unwrap();
        (reports, graph)
    }

    #[test]
    fn summary_counts_exec_spec_and_proof_functions() {
        let (reports, graph) = graph();
        let text = summary(&reports, &graph);
        assert!(text.contains("verified functions:      6   reachable:      4  (66%)"), "{text}");
        assert!(text.contains("  exec                   3   reachable:      2  (66%)"), "{text}");
        assert!(text.contains("  spec                   2   reachable:      1  (50%)"), "{text}");
        assert!(text.contains("  proof                  1   reachable:      1  (100%)"), "{text}");
        assert!(text.contains("verified LoC:           18   reachable:     12  (66%)"), "{text}");
        assert!(
            text.contains(
                "  lib               4/4    fns      12/12     LoC     2/2    exec     2/2    ghost"
            ),
            "{text}"
        );
        assert!(
            text.contains(
                "  lib::verified     0/2    fns       0/6      LoC     0/1    exec     0/1    ghost"
            ),
            "{text}"
        );
    }

    #[test]
    fn summary_lists_unreachable_verified_functions_with_their_mode() {
        let (reports, graph) = graph();
        let text = summary(&reports, &graph);
        assert!(
            text.contains(
                "unreachable verified functions:\n  x.rs:1   exec  inc\n  x.rs:1   spec  spec_inc\n"
            ),
            "{text}"
        );
    }

    #[test]
    fn lcov_marks_hits_by_id() {
        let (_, graph) = graph();
        let text = lcov(&graph, Only::VerifiedExec);
        assert!(text.contains("SF:x.rs\n"), "{text}");
        assert!(text.contains("FN:1,lib::wired\n"), "{text}");
        assert!(text.contains("FNDA:1,lib::wired\n"), "{text}");
        assert!(text.contains("FNDA:0,lib::verified::inc\n"), "{text}");
        assert!(text.contains("FNF:3\nFNH:2\n"), "{text}");
        assert!(!text.contains("app(bin)::main"), "{text}");
        assert!(!text.contains("spec_wired"), "{text}");

        let verified = lcov(&graph, Only::Verified);
        assert!(verified.contains("FNDA:1,lib::spec_wired\n"), "{verified}");
        assert!(verified.contains("FNDA:0,lib::verified::spec_inc\n"), "{verified}");
        assert!(verified.contains("FNDA:1,lib::lemma\n"), "{verified}");
        assert!(!verified.contains("lib::inc\n"), "{verified}");
        assert!(lcov(&graph, Only::All).contains("FNDA:1,lib::inc\n"));
    }

    #[test]
    fn fail_under_uses_the_summary_percentage() {
        let (_, graph) = graph();
        assert_eq!(below_threshold(&graph, 66), None);
        let msg = below_threshold(&graph, 67).unwrap();
        assert!(msg.contains("4 of 6 verified functions reachable (66%)"), "{msg}");
    }
}
