//! Renders the reports written by `verus --reach DIR`.
//!
//!   verus-reach DIR...            text summary
//!   verus-reach --lcov DIR...     LCOV, for grcov, genhtml, Codecov, IDE gutters
//!   verus-reach --html DIR...     a page with two per-file metrics: the
//!                                 share of verified functions nothing
//!                                 reaches, and the share of reachable
//!                                 functions that are verified
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
    /// Exit with an error if fewer than this percentage of verified
    /// functions (exec, spec, and proof) are reachable
    #[arg(long)]
    fail_under: Option<u64>,
    /// Write an LCOV trace file to stdout instead of the summary
    #[arg(long, conflicts_with = "html")]
    lcov: bool,
    /// Write an HTML page of per-file metrics to stdout instead of the
    /// summary
    #[arg(long)]
    html: bool,
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

/// The function counts of one file behind the per-file metrics.
#[derive(Default, Clone, Copy)]
struct Counts {
    /// Verified functions
    verified: usize,
    /// Verified functions something reaches
    verified_reachable: usize,
    /// Functions something reaches, verified or not
    reachable: usize,
}

impl Counts {
    fn add(&mut self, node: &Node, graph: &Graph) {
        // A proxy stands for another function's spec; it is not code
        if node.proxy {
            return;
        }
        let reachable = graph.is_reachable(node);
        self.verified += node.is_verified() as usize;
        self.verified_reachable += (node.is_verified() && reachable) as usize;
        self.reachable += reachable as usize;
    }

    fn dead(&self) -> usize {
        self.verified - self.verified_reachable
    }

    /// Verified functions nothing reaches, as a share of verified
    /// functions: 1 minus the coverage
    fn dead_pct(&self) -> Option<u64> {
        ratio(self.dead(), self.verified)
    }

    /// Verified functions as a share of reachable functions
    fn verified_pct(&self) -> Option<u64> {
        ratio(self.verified_reachable, self.reachable)
    }
}

/// None when there is nothing to divide by
fn ratio(part: usize, total: usize) -> Option<u64> {
    (total > 0).then(|| (100 * part / total) as u64)
}

fn escape(text: &str) -> String {
    text.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
}

fn html(graph: &Graph) -> String {
    let mut files: BTreeMap<&str, Counts> = BTreeMap::new();
    let mut total = Counts::default();
    for n in graph.nodes.values() {
        files.entry(&n.span.file).or_default().add(n, graph);
        total.add(n, graph);
    }
    let mut out = String::new();
    out.push_str(
        "<!DOCTYPE html>\n<html>\n<head>\n<meta charset=\"utf-8\">\n<title>verus-reach</title>\n\
         <style>\n\
         body { font-family: sans-serif; margin: 2em; }\n\
         table { border-collapse: collapse; }\n\
         th, td { padding: 0.3em 1em; border-bottom: 1px solid #ddd; text-align: right; }\n\
         th:first-child, td:first-child { text-align: left; }\n\
         th { vertical-align: bottom; }\n\
         tr.total td { font-weight: bold; border-top: 2px solid #888; }\n\
         </style>\n</head>\n<body>\n",
    );
    out.push_str(
        "<p>A function is <b>verified</b> when Verus checks it: exec code with a real body, and \
         every spec and proof function. It is <b>reachable</b> when it runs from a root or when \
         the ghost code of reachable code mentions it.</p>\n",
    );
    out.push_str(
        "<table>\n<tr><th>file</th><th>verified</th><th>reachable<br>verified</th>\
         <th>dead verified<br>(unreachable / verified)</th>\
         <th>reachable</th><th>verified share<br>(reachable verified / reachable)</th></tr>\n",
    );
    let row = |out: &mut String, class: &str, name: &str, c: &Counts| {
        let pct = |p: Option<u64>| p.map_or("-".to_string(), |p| format!("{p}%"));
        writeln!(
            out,
            "<tr{class}><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td><td>{}</td></tr>",
            escape(name),
            c.verified,
            c.verified_reachable,
            pct(c.dead_pct()),
            c.reachable,
            pct(c.verified_pct()),
        )
        .unwrap();
    };
    for (file, counts) in &files {
        row(&mut out, "", file, counts);
    }
    row(&mut out, " class=\"total\"", "total", &total);
    out.push_str("</table>\n</body>\n</html>\n");
    out
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
    let text = if args.lcov {
        lcov(&graph, only)
    } else if args.html {
        html(&graph)
    } else {
        summary(&reports, &graph)
    };
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
    fn html_rates_each_file() {
        // Put the library's public twin and its spec in a file of their own
        let mut reports = lib_and_bin();
        for n in reports[0].nodes.iter_mut().filter(|n| n.module == "lib::verified") {
            n.span.file = "verified.rs".into();
        }
        let graph = Graph::new(&reports, &Roots::default()).unwrap();
        let text = html(&graph);
        // x.rs: wired, helper, spec_wired, lemma verified and reached; inc and
        // main reached but unverified
        assert!(
            text.contains(
                "<tr><td>x.rs</td><td>4</td><td>4</td><td>0%</td><td>6</td><td>66%</td></tr>"
            ),
            "{text}"
        );
        // verified.rs: inc and spec_inc verified, nothing reached
        assert!(
            text.contains(
                "<tr><td>verified.rs</td><td>2</td><td>0</td><td>100%</td><td>0</td><td>-</td></tr>"
            ),
            "{text}"
        );
        assert!(
            text.contains(
                "<tr class=\"total\"><td>total</td><td>6</td><td>4</td><td>33%</td><td>6</td><td>66%</td></tr>"
            ),
            "{text}"
        );
    }

    #[test]
    fn fail_under_uses_the_summary_percentage() {
        let (_, graph) = graph();
        assert_eq!(below_threshold(&graph, 66), None);
        let msg = below_threshold(&graph, 67).unwrap();
        assert!(msg.contains("4 of 6 verified functions reachable (66%)"), "{msg}");
    }
}
