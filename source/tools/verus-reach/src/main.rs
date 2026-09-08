//! Renders the reports written by `verus --reach DIR`.
//!
//!   verus-reach DIR...            text summary
//!   verus-reach --lcov DIR...     LCOV, for grcov, genhtml, Codecov, IDE gutters
//!
//! Pass every crate's report (a directory of them, or files) so that calls
//! across crates are followed.

use clap::Parser;
use std::collections::BTreeMap;
use std::path::PathBuf;
use verus_reach::{Graph, Node, Report, Roots};

#[derive(Parser)]
struct Args {
    /// Report files or directories of reports
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
    fail_under: Option<f64>,
    /// Write an LCOV trace file to stdout instead of the summary
    #[arg(long)]
    lcov: bool,
    /// With --lcov, include only verified exec functions
    #[arg(long)]
    only_verified_exec: bool,
}

fn pct(part: usize, total: usize) -> u64 {
    if total == 0 { 100 } else { (100 * part / total) as u64 }
}

fn loc(node: &Node) -> usize {
    node.span.end_line - node.span.start_line + 1
}

fn module(def_path: &str) -> &str {
    def_path.rfind("::").map_or("", |i| &def_path[..i])
}

fn name(def_path: &str) -> &str {
    def_path.rfind("::").map_or(def_path, |i| &def_path[i + 2..])
}

/// Number of leading `::` segments two paths share.
fn shared_prefix(a: &str, b: &str) -> usize {
    a.split("::").zip(b.split("::")).take_while(|(x, y)| x == y).count()
}

fn summary(reports: &[Report], graph: &Graph) {
    let crates: Vec<String> =
        reports.iter().map(|r| format!("{} ({})", r.krate, r.crate_type)).collect();
    println!("crates: {}", crates.join(", "));
    let roots: Vec<&str> = graph.roots.iter().map(|id| graph.nodes[id].def_path.as_str()).collect();
    match roots.len() {
        0..=3 => println!("roots: {}", roots.join(", ")),
        n => println!("roots: {n} functions"),
    }

    let fns: Vec<&Node> = graph.nodes.values().filter(|n| n.is_verified_exec()).collect();
    let reached: Vec<&Node> = fns.iter().copied().filter(|n| graph.is_reachable(n)).collect();
    let total_loc: usize = fns.iter().map(|n| loc(n)).sum();
    let reached_loc: usize = reached.iter().map(|n| loc(n)).sum();
    println!(
        "\nverified exec functions: {:>6}   reachable: {:>6}  ({}%)",
        fns.len(),
        reached.len(),
        pct(reached.len(), fns.len())
    );
    println!(
        "verified exec LoC:       {:>6}   reachable: {:>6}  ({}%)",
        total_loc,
        reached_loc,
        pct(reached_loc, total_loc)
    );
    println!("(LoC counts every line of the function, including proof blocks)");

    // (reachable fns, fns, reachable loc, loc) per module
    let mut modules: BTreeMap<&str, (usize, usize, usize, usize)> = BTreeMap::new();
    for f in &fns {
        let m = modules.entry(module(&f.def_path)).or_default();
        m.1 += 1;
        m.3 += loc(f);
        if graph.is_reachable(f) {
            m.0 += 1;
            m.2 += loc(f);
        }
    }
    println!("\nby module:");
    let width = modules.keys().map(|m| m.len()).max().unwrap_or(0);
    for (module, (rf, tf, rl, tl)) in &modules {
        println!("  {module:width$}  {rf:>4}/{tf:<4} fns  {rl:>6}/{tl:<6} LoC");
    }

    let unreachable: Vec<&Node> = fns.iter().copied().filter(|n| !graph.is_reachable(n)).collect();
    if unreachable.is_empty() {
        return;
    }
    println!("\nunreachable verified exec functions:");
    for f in unreachable {
        // A reachable, unverified function with the same name nearby suggests a "verified twin"
        let twin = graph
            .nodes
            .values()
            .filter(|g| {
                graph.is_reachable(g) && !g.verified && name(&g.def_path) == name(&f.def_path)
            })
            .map(|g| (shared_prefix(&g.def_path, &f.def_path), g))
            .filter(|(shared, _)| *shared >= 2)
            .max_by_key(|(shared, _)| *shared)
            .map(|(_, g)| format!("   (same name reachable: {})", g.def_path))
            .unwrap_or_default();
        println!("  {}:{}   {}{}", f.span.file, f.span.start_line, name(&f.def_path), twin);
    }
}

fn lcov(graph: &Graph, only_verified_exec: bool) {
    use lcov::report::section::{function, line};
    let mut report = lcov::Report::new();
    for n in graph.nodes.values().filter(|n| !only_verified_exec || n.is_verified_exec()) {
        let hits = graph.is_reachable(n) as u64;
        let key = lcov::report::section::Key {
            test_name: String::new(),
            source_file: PathBuf::from(&n.span.file),
        };
        let section = report.sections.entry(key).or_default();
        section.functions.insert(
            function::Key { name: n.def_path.clone() },
            function::Value { start_line: Some(n.span.start_line as u32), count: hits },
        );
        for l in n.span.start_line..=n.span.end_line {
            section.lines.entry(line::Key { line: l as u32 }).or_default().count |= hits;
        }
    }
    for record in report.into_records() {
        println!("{record}");
    }
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
    let graph = Graph::new(&reports, &roots);
    if args.lcov {
        lcov(&graph, args.only_verified_exec);
    } else {
        summary(&reports, &graph);
    }
    if let Some(threshold) = args.fail_under {
        let fns: Vec<&Node> = graph.nodes.values().filter(|n| n.is_verified_exec()).collect();
        let reached = fns.iter().filter(|n| graph.is_reachable(n)).count();
        let pct = if fns.is_empty() { 100.0 } else { 100.0 * reached as f64 / fns.len() as f64 };
        if pct < threshold {
            fail(format!(
                "{reached} of {} verified exec functions reachable ({pct:.0}%), below --fail-under {threshold}",
                fns.len()
            ));
        }
    }
}
