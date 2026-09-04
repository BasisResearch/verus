//! Renders the `reach.json` written by `verus --reach FILE`.
//!
//!   verus-reach summary reach.json          text summary (default)
//!   verus-reach lcov reach.json [--only verified-exec]
//!
//! The LCOV output feeds grcov, genhtml, Codecov, and IDE coverage gutters.

use serde::Deserialize;
use std::collections::BTreeMap;

#[derive(Deserialize)]
struct Report {
    functions: Vec<Function>,
}

#[derive(Deserialize)]
struct Function {
    def_path: String,
    span: Span,
    mode: String,
    verified: bool,
    external_body: bool,
    proxy: bool,
    reachable: bool,
}

#[derive(Deserialize)]
struct Span {
    file: String,
    start_line: usize,
    end_line: usize,
}

impl Function {
    /// The functions we want wired in: verified exec code with a real body.
    fn is_verified_exec(&self) -> bool {
        self.verified && self.mode == "exec" && !self.external_body && !self.proxy
    }

    fn loc(&self) -> usize {
        self.span.end_line - self.span.start_line + 1
    }

    fn module(&self) -> &str {
        match self.def_path.rfind("::") {
            Some(i) => &self.def_path[..i],
            None => "",
        }
    }

    fn name(&self) -> &str {
        match self.def_path.rfind("::") {
            Some(i) => &self.def_path[i + 2..],
            None => &self.def_path,
        }
    }
}

/// Number of leading `::` segments two paths share.
fn shared_prefix(a: &str, b: &str) -> usize {
    a.split("::").zip(b.split("::")).take_while(|(x, y)| x == y).count()
}

fn pct(part: usize, total: usize) -> u64 {
    if total == 0 { 100 } else { (100 * part / total) as u64 }
}

fn summary(report: &Report) {
    let fns: Vec<&Function> = report.functions.iter().filter(|f| f.is_verified_exec()).collect();
    let reached: Vec<&Function> = fns.iter().copied().filter(|f| f.reachable).collect();
    let loc: usize = fns.iter().map(|f| f.loc()).sum();
    let reached_loc: usize = reached.iter().map(|f| f.loc()).sum();
    println!(
        "verified exec functions: {:>6}   reachable: {:>6}  ({}%)",
        fns.len(),
        reached.len(),
        pct(reached.len(), fns.len())
    );
    println!(
        "verified exec LoC:       {:>6}   reachable: {:>6}  ({}%)",
        loc,
        reached_loc,
        pct(reached_loc, loc)
    );
    println!("(LoC counts every line of the function, including proof blocks)");

    // (reachable fns, fns, reachable loc, loc) per module
    let mut modules: BTreeMap<&str, (usize, usize, usize, usize)> = BTreeMap::new();
    for f in &fns {
        let m = modules.entry(f.module()).or_default();
        m.1 += 1;
        m.3 += f.loc();
        if f.reachable {
            m.0 += 1;
            m.2 += f.loc();
        }
    }
    println!("\nby module:");
    let width = modules.keys().map(|m| m.len()).max().unwrap_or(0);
    for (module, (rf, tf, rl, tl)) in &modules {
        println!("  {module:width$}  {rf:>4}/{tf:<4} fns  {rl:>6}/{tl:<6} LoC");
    }

    let unreachable: Vec<&Function> = fns.iter().copied().filter(|f| !f.reachable).collect();
    if unreachable.is_empty() {
        return;
    }
    println!("\nunreachable verified exec functions:");
    for f in unreachable {
        // A reachable, unverified function with the same name nearby suggests a "verified twin"
        let twin = report
            .functions
            .iter()
            .filter(|g| g.reachable && !g.verified && g.name() == f.name())
            .map(|g| (shared_prefix(&g.def_path, &f.def_path), g))
            .filter(|(shared, _)| *shared >= 2)
            .max_by_key(|(shared, _)| *shared)
            .map(|(_, g)| format!("   (same name reachable: {})", g.def_path))
            .unwrap_or_default();
        println!("  {}:{}   {}{}", f.span.file, f.span.start_line, f.name(), twin);
    }
}

fn lcov(report: &Report, only_verified_exec: bool) {
    let mut by_file: BTreeMap<&str, Vec<&Function>> = BTreeMap::new();
    for f in &report.functions {
        if !only_verified_exec || f.is_verified_exec() {
            by_file.entry(&f.span.file).or_default().push(f);
        }
    }
    for (file, fns) in by_file {
        println!("TN:");
        println!("SF:{file}");
        for f in &fns {
            println!("FN:{},{}", f.span.start_line, f.def_path);
            println!("FNDA:{},{}", f.reachable as u8, f.def_path);
        }
        println!("FNF:{}", fns.len());
        println!("FNH:{}", fns.iter().filter(|f| f.reachable).count());
        let mut lines: BTreeMap<usize, u8> = BTreeMap::new();
        for f in &fns {
            for line in f.span.start_line..=f.span.end_line {
                let hit = lines.entry(line).or_default();
                *hit |= f.reachable as u8;
            }
        }
        for (line, hit) in &lines {
            println!("DA:{line},{hit}");
        }
        println!("LF:{}", lines.len());
        println!("LH:{}", lines.values().filter(|h| **h > 0).count());
        println!("end_of_record");
    }
}

fn usage() -> ! {
    eprintln!("usage: verus-reach [summary|lcov] reach.json [--only verified-exec]");
    std::process::exit(2)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (command, rest) = match args.first().map(|s| s.as_str()) {
        Some("summary") | Some("lcov") => (args[0].as_str(), &args[1..]),
        Some(_) => ("summary", &args[..]),
        None => usage(),
    };
    let Some(path) = rest.first() else { usage() };
    let only = match rest.get(1).map(|s| s.as_str()) {
        None => false,
        Some("--only") if rest.get(2).map(|s| s.as_str()) == Some("verified-exec") => true,
        _ => usage(),
    };
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("cannot read {path}: {e}");
        std::process::exit(1)
    });
    let report: Report = serde_json::from_str(&text).unwrap_or_else(|e| {
        eprintln!("{path} is not a reach.json: {e}");
        std::process::exit(1)
    });
    match command {
        "lcov" => lcov(&report, only),
        _ => summary(&report),
    }
}
