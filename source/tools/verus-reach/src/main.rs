//! Renders the reports written by `verus --reach DIR`.
//!
//!   verus-reach DIR...            text summary
//!   verus-reach --lcov DIR...     LCOV, for grcov, genhtml, Codecov, IDE gutters
//!
//! Pass every crate's report (a directory of them, or files) so that calls
//! across crates are followed.

use clap::Parser;
use std::collections::BTreeMap;
use std::fmt::Write;
use std::path::PathBuf;
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
    /// Exit with an error if fewer than this percentage of verified exec
    /// functions are reachable
    #[arg(long)]
    fail_under: Option<u64>,
    /// Write an LCOV trace file to stdout instead of the summary
    #[arg(long)]
    lcov: bool,
    /// With --lcov, include only verified exec functions
    #[arg(long, conflicts_with = "only_verified")]
    only_verified_exec: bool,
    /// With --lcov, include only verified exec, spec, and proof functions
    #[arg(long)]
    only_verified: bool,
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
            Only::Verified => node.is_verified_exec() || node.is_ghost(),
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

    let fns: Vec<&Node> = graph.nodes.values().filter(|n| n.is_verified_exec()).collect();
    let reached: Vec<&Node> = fns.iter().copied().filter(|n| graph.is_reachable(n)).collect();
    let total_loc: usize = fns.iter().map(|n| loc(n)).sum();
    let reached_loc: usize = reached.iter().map(|n| loc(n)).sum();
    writeln!(
        out,
        "\nverified exec functions: {:>6}   reachable: {:>6}  ({}%)",
        fns.len(),
        reached.len(),
        pct(reached.len(), fns.len())
    )
    .unwrap();
    writeln!(
        out,
        "verified exec LoC:       {:>6}   reachable: {:>6}  ({}%)",
        total_loc,
        reached_loc,
        pct(reached_loc, total_loc)
    )
    .unwrap();
    writeln!(out, "(LoC counts every line of the function, including proof blocks)").unwrap();
    let ghosts: Vec<&Node> = graph.nodes.values().filter(|n| n.is_ghost()).collect();
    let used = ghosts.iter().filter(|n| graph.is_reachable(n)).count();
    writeln!(
        out,
        "ghost functions:         {:>6}   used:      {:>6}  ({}%)",
        ghosts.len(),
        used,
        pct(used, ghosts.len())
    )
    .unwrap();
    writeln!(out, "(a ghost function is used when the ghost code of reachable code mentions it)")
        .unwrap();

    // (reachable fns, fns, reachable loc, loc, used ghosts, ghosts) per module
    let mut modules: BTreeMap<&str, [usize; 6]> = BTreeMap::new();
    for f in &fns {
        let m = modules.entry(&f.module).or_default();
        m[1] += 1;
        m[3] += loc(f);
        if graph.is_reachable(f) {
            m[0] += 1;
            m[2] += loc(f);
        }
    }
    for f in &ghosts {
        let m = modules.entry(&f.module).or_default();
        m[5] += 1;
        m[4] += graph.is_reachable(f) as usize;
    }
    writeln!(out, "\nby module:").unwrap();
    let width = modules.keys().map(|m| m.len()).max().unwrap_or(0);
    for (module, [rf, tf, rl, tl, us, ts]) in &modules {
        writeln!(
            out,
            "  {module:width$}  {rf:>4}/{tf:<4} fns  {rl:>6}/{tl:<6} LoC  {us:>4}/{ts:<4} ghost"
        )
        .unwrap();
    }

    let unreachable: Vec<&Node> = fns.iter().copied().filter(|n| !graph.is_reachable(n)).collect();
    if !unreachable.is_empty() {
        writeln!(out, "\nunreachable verified exec functions:").unwrap();
    }
    for f in unreachable {
        writeln!(out, "  {}:{}   {}", f.span.file, f.span.start_line, f.name()).unwrap();
    }

    let unused: Vec<&Node> = ghosts.iter().copied().filter(|n| !graph.is_reachable(n)).collect();
    if !unused.is_empty() {
        writeln!(out, "\nunused ghost functions:").unwrap();
    }
    for f in unused {
        writeln!(out, "  {}:{}   {}", f.span.file, f.span.start_line, f.name()).unwrap();
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

fn below_threshold(graph: &Graph, threshold: u64) -> Option<String> {
    let (reached, total) = graph.coverage();
    let pct = pct(reached, total);
    (pct < threshold).then(|| {
        format!(
            "{reached} of {total} verified exec functions reachable ({pct}%), below --fail-under {threshold}"
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
    let text = if args.lcov { lcov(&graph, only) } else { summary(&reports, &graph) };
    print!("{text}");
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
    fn summary_lists_unreachable_verified_exec() {
        let (reports, graph) = graph();
        let text = summary(&reports, &graph);
        assert!(
            text.contains("verified exec functions:      3   reachable:      2  (66%)"),
            "{text}"
        );
        assert!(text.contains("unreachable verified exec functions:\n  x.rs:1   inc\n"), "{text}");
        assert!(
            text.contains("  lib               2/2    fns       6/6      LoC     2/2    ghost"),
            "{text}"
        );
        assert!(
            text.contains("  lib::verified     0/1    fns       0/3      LoC     0/1    ghost"),
            "{text}"
        );
    }

    #[test]
    fn summary_lists_unused_ghost_functions() {
        let (reports, graph) = graph();
        let text = summary(&reports, &graph);
        assert!(
            text.contains("ghost functions:              3   used:           2  (66%)"),
            "{text}"
        );
        assert!(text.contains("unused ghost functions:\n  x.rs:1   spec_inc\n"), "{text}");
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
        assert!(below_threshold(&graph, 67).unwrap().contains("(66%)"));
    }
}
