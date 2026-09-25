#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

use std::path::{Path, PathBuf};
use tempfile::TempDir;

/// What `-V tla-export` wrote for one module.
struct Exported {
    dir: TempDir,
    module: String,
    tla: String,
    cfg: String,
    report: serde_json::Value,
}

impl Exported {
    fn spec(&self) -> PathBuf {
        self.dir.path().join("log").join(format!("{}.tla", self.module))
    }
}

/// Export `module` of the file at `entry` and read back what was written.
/// The crate is `test_crate`, so its root module is `test_crate`.
fn export(entry: &Path, module: &str) -> Exported {
    let dir = TempDir::new().expect("temp dir");
    let log = dir.path().join("log");
    let options = [format!("-V tla-export={module}"), format!("--log-dir {}", log.display())];
    let options: Vec<&str> = options.iter().map(|s| s.as_str()).collect();
    let output = run_verus(&options, dir.path(), &entry.to_path_buf(), true, true);
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert!(output.status.success(), "verus failed:\n{}", stderr);
    let line = stderr.lines().find(|l| l.starts_with("tla-export:")).unwrap_or_else(|| {
        panic!("no tla-export line:\n{}", stderr);
    });
    // TLC loads a module only from a file of the same name.
    let tla_path = PathBuf::from(line.rsplit("wrote ").next().unwrap().trim());
    let module = tla_path.file_stem().unwrap().to_str().unwrap().to_string();
    assert_eq!(tla_path.parent(), Some(log.as_path()), "{line}");
    let tla = std::fs::read_to_string(&tla_path).expect("the .tla");
    assert!(tla.starts_with(&format!("---- MODULE {module} ----\n")), "{}", tla);
    let cfg = std::fs::read_to_string(log.join(format!("{module}.cfg"))).expect("the .cfg");
    let json = std::fs::read_to_string(log.join(format!("{module}.tla.json"))).expect("report");
    let report = serde_json::from_str(&json).expect("the report is json");
    Exported { dir, module, tla, cfg, report }
}

/// Write `code` (with the usual prelude) to a file and export `module`.
fn export_code(code: &str, module: &str) -> Exported {
    let src = TempDir::new().expect("temp dir");
    let entry = src.path().join("test.rs");
    std::fs::write(&entry, format!("{}\n{}\n{}\n", FEATURE_PRELUDE, USE_PRELUDE, code)).unwrap();
    export(&entry, module)
}

fn fixture(name: &str) -> PathBuf {
    PathBuf::from("../../examples/tla").join(name)
}

fn names(v: &serde_json::Value) -> Vec<String> {
    v.as_array()
        .expect("array")
        .iter()
        .map(|x| x.as_str().map(str::to_string).unwrap_or_else(|| x["constant"].to_string()))
        .collect()
}

/// The TLA+ tools, when `TLA2TOOLS_JAR` names a `tla2tools.jar`; without
/// it the SANY and TLC checks are skipped (the export checks still run).
fn tla_tools() -> Option<String> {
    match std::env::var("TLA2TOOLS_JAR") {
        Ok(jar) if Path::new(&jar).exists() => Some(jar),
        _ => {
            eprintln!("TLA2TOOLS_JAR is not set: skipping the SANY and TLC checks");
            None
        }
    }
}

fn java(jar: &str, dir: &Path, args: &[&str]) -> String {
    let out = std::process::Command::new("java")
        .arg(format!("-Djava.io.tmpdir={}", dir.display()))
        .args(["-cp", jar])
        .args(args)
        .current_dir(dir)
        .output()
        .expect("could not run java");
    format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr))
}

/// SANY's verdict on a spec: panics with its output on any error.
fn sany(jar: &str, spec: &Path) {
    let out = java(jar, spec.parent().unwrap(), &["tla2sany.SANY", spec.to_str().unwrap()]);
    assert!(
        !out.contains("*** Errors") && !out.contains("Fatal errors") && !out.contains("error"),
        "SANY rejected {}:\n{out}",
        spec.display()
    );
}

/// What a TLC run found.
#[derive(Debug, PartialEq)]
struct Tlc {
    generated: u64,
    distinct: u64,
    violated: Vec<String>,
}

/// TLC's output on `spec` with `cfg` (deadlock is not an error, and it
/// continues past a violation).
fn tlc_output(jar: &str, spec: &Path, cfg: &str) -> String {
    let dir = spec.parent().unwrap();
    let cfg_path = spec.with_extension("cfg");
    std::fs::write(&cfg_path, cfg).unwrap();
    let meta = dir.join("states");
    java(
        jar,
        dir,
        &[
            "tlc2.TLC",
            "-workers",
            "1",
            "-deadlock",
            "-continue",
            "-metadir",
            meta.to_str().unwrap(),
            "-config",
            cfg_path.to_str().unwrap(),
            spec.to_str().unwrap(),
        ],
    )
}

/// Run TLC to completion on `spec` with `cfg`, counting every violation;
/// panics on any other error.
fn tlc(jar: &str, spec: &Path, cfg: &str) -> Tlc {
    let out = tlc_output(jar, spec, cfg);
    let re = regex::Regex::new(r"(\d+) states generated, (\d+) distinct states found").unwrap();
    let caps =
        re.captures_iter(&out).last().unwrap_or_else(|| panic!("TLC did not finish:\n{}", out));
    let violated_re = regex::Regex::new(r"^Error: Invariant (\S+) is violated").unwrap();
    let mut violated = Vec::new();
    for line in out.lines() {
        if let Some(c) = violated_re.captures(line) {
            violated.push(c[1].to_string());
        } else if (line.starts_with("Error:") && !line.starts_with("Error: The behavior up to"))
            || line.contains("Assert evaluated to FALSE")
        {
            panic!("TLC failed on {}:\n{out}", spec.display());
        }
    }
    Tlc { generated: caps[1].parse().unwrap(), distinct: caps[2].parse().unwrap(), violated }
}

#[test]
fn tla_export_counter_matches_the_hand_written_spec() {
    let ex = export(&fixture("counter.rs"), "test_crate");
    assert_eq!(ex.report["shape"], "hand-rolled");
    assert_eq!(names(&ex.report["variables"]), ["x", "y"]);
    assert_eq!(names(&ex.report["invariants"]), ["bounded", "sum_small"]);
    // Each step is a transition (`next` and `next_step` only branch), and
    // each primes both variables.
    assert_eq!(
        ex.report["transitions"],
        serde_json::json!([
            {"operator": "t_dbl", "unassigned": []},
            {"operator": "t_inc", "unassigned": []},
        ])
    );
    assert_eq!(ex.report["holes"], serde_json::json!([]));
    assert_eq!(ex.report["refusals"], serde_json::json!([]));
    assert!(ex.cfg.contains("INVARIANTS\n  bounded\n  sum_small\n"), "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let exported = tlc(&jar, &ex.spec(), &ex.cfg);

    // The same system written by hand, checked the same way.
    let hand = TempDir::new().unwrap();
    let hand_spec = hand.path().join("Counter.tla");
    std::fs::copy(fixture("Counter.tla"), &hand_spec).unwrap();
    let hand_cfg = std::fs::read_to_string(fixture("Counter.cfg")).unwrap();
    let by_hand = tlc(&jar, &hand_spec, &hand_cfg);

    assert_eq!(exported.distinct, 18, "{exported:?}");
    assert_eq!(exported.generated, by_hand.generated);
    assert_eq!(exported.distinct, by_hand.distinct);
    assert_eq!(exported.violated.len(), by_hand.violated.len(), "{exported:?} {by_hand:?}");
    assert!(exported.violated.iter().all(|v| v == "bounded"), "{:?}", exported);
    assert!(by_hand.violated.iter().all(|v| v == "Bounded"), "{:?}", by_hand);
}

#[test]
fn tla_export_verussync_leaves_the_step_parameter_as_a_hole() {
    let ex = export(&fixture("adder_sync.rs"), "test_crate::Adder");
    assert_eq!(ex.report["shape"], "verussync");
    assert_eq!(names(&ex.report["variables"]), ["x", "y"]);
    assert_eq!(names(&ex.report["invariants"]), ["x_eq_y"]);
    assert_eq!(ex.report["refusals"], serde_json::json!([]));
    let holes = ex.report["holes"].as_array().unwrap();
    assert_eq!(holes.len(), 1, "{holes:?}");
    assert_eq!(holes[0]["constant"], "Dom_Step_add_v0");
    // `next_by`'s `dummy_to_use_type_params => false` arm never holds, so
    // it assigns nothing and leaves nothing unassigned (in Next or Init).
    assert_eq!(
        ex.report["transitions"],
        serde_json::json!([{"operator": "add", "unassigned": []}])
    );
    assert_eq!(ex.report["init_unassigned"], serde_json::json!([]));
    assert!(!ex.cfg.contains("never assigns"), "{}", ex.cfg);
    // The hole is left unassigned, so TLC stops until it is given a domain
    // rather than quantifying over an empty set.
    assert!(ex.cfg.contains("\\*   Dom_Step_add_v0 = { ... }"), "{}", ex.cfg);
    assert!(!ex.cfg.lines().any(|l| l.trim() == "CONSTANTS"), "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let cfg = format!("{}CONSTANTS Dom_Step_add_v0 = {{0, 1, 2}}\nCONSTRAINT x < 4\n", ex.cfg);
    // The state space is unbounded: bound it with a constraint.
    let end = ex.tla.trim_end().rfind('\n').unwrap();
    std::fs::write(ex.spec(), format!("{}\nBound == x < 4{}", &ex.tla[..end], &ex.tla[end..]))
        .unwrap();
    let run = tlc(&jar, &ex.spec(), &cfg.replace("CONSTRAINT x < 4", "CONSTRAINT Bound"));
    assert_eq!(run.violated, Vec::<String>::new());
    assert!(run.distinct >= 4, "{:?}", run);
}

#[test]
fn tla_export_verus_tla_reduces_the_action_records() {
    let ex = export(&fixture("mutex_tla.rs"), "test_crate");
    assert_eq!(ex.report["shape"], "verus-tla");
    assert_eq!(names(&ex.report["variables"]), ["holder", "count"]);
    assert_eq!(names(&ex.report["invariants"]), ["count_bounded", "held_after_acquire"]);
    // `acquire(thread)`'s parameter is `t`: the record's closures read it
    // through a LET, not by the accident of a shared name.
    assert_eq!(ex.report["refusals"], serde_json::json!([]));
    assert_eq!(ex.report["holes"], serde_json::json!([]), "`thread: nat` with `thread < 2`");
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new());
    // holder None at every count 0..3, and Some(0) or Some(1) at 1..3.
    assert_eq!(run.distinct, 10, "{run:?}");
}

/// Shapes the export once printed as TLA+ that SANY rejects or that meant
/// something else: names reused in their own scope, a parameter named like a
/// variable, a guard reading a pattern binding, a shadowing `let`, a
/// two-argument recursive function, `Seq::new`, and a callee given `post`
/// alongside an argument that reads the pre state.
const PROBES: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub count: int, pub m: Map<int, int>, pub o: Option<int>, pub s: Seq<int> }

pub open spec fn init(s: State) -> bool {
    s == State { count: 0, m: Map::<int, int>::empty().insert(0, 0).insert(6, 6), o: None, s: Seq::empty() }
}

pub open spec fn bump(count: int) -> int { count + 1 }

pub open spec fn pos(o: Option<int>) -> bool {
    match o { Some(v) if v > 0 => true, _ => false }
}

pub open spec fn drop_key(o: Option<int>, m: Map<int, int>) -> Map<int, int> {
    match o {
        Some(k) => if m.dom().contains(k) { m.remove(k) } else { m },
        None => m,
    }
}

pub open spec fn twice(a: int) -> int { let a2 = a + 1; let a2 = a2 * 2; a2 }

pub open spec fn sumto(n: int, acc: int) -> int decreases n {
    if n <= 0 { acc } else { sumto(n - 1, acc + 1) }
}

pub open spec fn is_val(s: State, v: int) -> bool { s.count == v }

pub open spec fn next(pre: State, post: State) -> bool {
    &&& pre.count < 3
    &&& post.count == bump(pre.count)
    &&& is_val(post, pre.count + 1)
    &&& post.m == drop_key(pre.o, pre.m)
    &&& post.o == (if pos(pre.o) { Some(twice(pre.count) + sumto(2, 0)) } else { Some(1int) })
    &&& post.s == Seq::new(2, |i: int| twice(i))
}

pub open spec fn m_nonneg(s: State) -> bool {
    forall|k: int| #![trigger s.m[k]] s.m.dom().contains(k) ==> s.m[k] >= 0
}

pub open spec fn count_range(s: State) -> bool { 0 <= s.count <= 3 }

pub open spec fn s_values(s: State) -> bool {
    forall|i: int| #![trigger s.s[i]] 0 <= i < s.s.len() ==> s.s[i] == 2 * (i + 1)
}

pub open spec fn o_values(s: State) -> bool {
    s.o is None || s.o == Some(1int) || s.o == Some(6int) || s.o == Some(8int)
}
}
"#;

#[test]
fn tla_export_probes_parse_and_check() {
    let ex = export_code(PROBES, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(ex.report["holes"], serde_json::json!([]), "{}", ex.tla);
    assert!(ex.tla.contains("RECURSIVE sumto(_, _)"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // One behaviour, count 0..3: a callee given `post` reads only `count'`,
    // so `is_val(post, pre.count + 1)` agrees with `count' = count + 1`.
    assert_eq!(run.distinct, 4, "{run:?}\n{}", ex.tla);
}

const RECURSIVE_STATE: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub v: Seq<int>, pub n: nat }

pub open spec fn sum(s: State, i: nat) -> int decreases i {
    if i == 0 || i > s.v.len() { 0 } else { s.v[i - 1] + sum(s, (i - 1) as nat) }
}

pub open spec fn init(s: State) -> bool { s.v == Seq::<int>::empty() && s.n == 0 }

pub open spec fn next(pre: State, post: State) -> bool {
    &&& pre.n < 3
    &&& post.v == pre.v.push(1)
    &&& post.n == pre.n + 1
    &&& sum(post, post.v.len()) == sum(pre, pre.v.len()) + 1
}

pub open spec fn sum_is_n(s: State) -> bool { sum(s, s.v.len()) == s.n }
}
"#;

#[test]
fn tla_export_passes_the_state_to_a_recursive_function() {
    // A primed variant of a RECURSIVE operator would raise the level of
    // every recursive operator to an action's (SANY), so `sum_is_n` would
    // not be a state predicate: the state is passed as a record instead.
    let ex = export_code(RECURSIVE_STATE, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["sum_is_n"]);
    assert!(ex.tla.contains("RECURSIVE sum(_, _)"), "{}", ex.tla);
    assert!(!ex.tla.contains("sum_post"), "{}", ex.tla);
    assert!(ex.tla.contains("sum([v |-> v', n |-> n'], Len(v'))"), "{}", ex.tla);
    assert!(ex.tla.contains("sum([v |-> v, n |-> n], Len(v))"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 4, "{run:?}\n{}", ex.tla);
}

const SYMBOLIC_ARGUMENT: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: int }

pub open spec fn apply(f: spec_fn(int) -> int, v: int) -> int { f(v) }

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn next(pre: State, post: State) -> bool {
    let f = |v: int| v + 1;
    pre.x < 3 && post.x == apply(f, pre.x)
}

pub open spec fn small(s: State) -> bool { s.x <= 3 }
}
"#;

#[test]
fn tla_export_refuses_a_closure_passed_as_a_value() {
    // `f` is held only symbolically; passing it on is a refusal (an
    // Assert), never its bare name, which SANY would reject.
    let ex = export_code(SYMBOLIC_ARGUMENT, "test_crate");
    let refusals: Vec<String> = ex.report["refusals"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r["what"].as_str().unwrap().to_string())
        .collect();
    assert!(
        refusals.iter().any(|w| w.contains("closure value `f` used other than in an application")),
        "{:?}",
        refusals
    );
    assert!(!ex.tla.contains("apply(f, x)"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
}

const REFUSED: &str = r#"
verus! {
pub enum List { Nil, Cons(int, Box<List>) }

pub open spec fn len(l: List) -> nat decreases l {
    match l { List::Nil => 0, List::Cons(_, t) => 1 + len(*t) }
}

pub struct State { pub x: int }

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn next(pre: State, post: State) -> bool { pre.x < 2 && post.x == pre.x + 1 }

pub open spec fn small(s: State) -> bool { s.x <= 2 }

pub open spec fn same(y: int) -> int { y }

pub open spec fn picked(s: State) -> bool { (choose|y: int| #[trigger] same(y) == s.x) == s.x }

pub open spec fn lists(s: State) -> bool { forall|l: List| #![trigger len(l)] len(l) >= 0 }
}
"#;

#[test]
fn tla_export_refusals_stop_tlc_and_leave_the_invariant_out() {
    let ex = export_code(REFUSED, "test_crate");
    let refusals = ex.report["refusals"].as_array().unwrap();
    assert_eq!(refusals.len(), 1, "{refusals:?}");
    assert!(refusals[0]["what"].as_str().unwrap().contains("choose"));
    assert_eq!(names(&ex.report["skipped_invariants"]), ["picked"]);
    assert_eq!(names(&ex.report["invariants"]), ["small", "lists"]);
    assert!(ex.cfg.contains("\\* INVARIANT picked is left out"), "{}", ex.cfg);
    assert!(!ex.cfg.contains("  picked\n"), "{}", ex.cfg);
    // A refusal is never TRUE: TLC stops wherever it is evaluated.
    assert!(ex.tla.contains("Assert(FALSE, \"tla-export refused: choose"), "{}", ex.tla);
    // A recursive datatype is a hole, not an endless recursion.
    let holes = ex.report["holes"].as_array().unwrap();
    assert!(holes.iter().any(|h| h["constant"] == "Dom_List_Cons_v1"), "{:?}", holes);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
}

/// The candidates the report lists, as (function's last segment, included).
fn candidates(report: &serde_json::Value) -> Vec<(String, bool)> {
    report["candidates"]
        .as_array()
        .expect("candidates")
        .iter()
        .map(|c| {
            let f = c["function"].as_str().unwrap();
            (f.rsplit("::").next().unwrap().to_string(), c["included"].as_bool().unwrap())
        })
        .collect()
}

/// Add `Bound == <pred>` to an export and constrain the model with it.
fn bounded(ex: &Exported, pred: &str) -> String {
    let end = ex.tla.trim_end().rfind('\n').unwrap();
    std::fs::write(ex.spec(), format!("{}\nBound == {pred}{}", &ex.tla[..end], &ex.tla[end..]))
        .unwrap();
    format!("{}CONSTRAINT Bound\n", ex.cfg)
}

#[test]
fn tla_export_verussync_takes_the_invariants_from_state_invariant() {
    let ex = export(&fixture("toggle_sync.rs"), "test_crate::Toggle");
    assert_eq!(ex.report["shape"], "verussync");
    // `flip_enabled`/`reset_enabled` have an invariant's signature but are
    // not `#[invariant]`s: checking them would report spurious violations.
    assert_eq!(names(&ex.report["invariants"]), ["n_nonneg"]);
    let c = candidates(&ex.report);
    assert!(c.contains(&("n_nonneg".into(), true)), "{:?}", c);
    assert!(c.contains(&("flip_enabled".into(), false)), "{:?}", c);
    assert!(c.contains(&("reset_enabled".into(), false)), "{:?}", c);
    assert!(c.contains(&("invariant".into(), false)), "{:?}", c);
    assert!(!ex.cfg.contains("_enabled"), "{}", ex.cfg);
    assert_eq!(
        ex.report["transitions"],
        serde_json::json!([
            {"operator": "flip", "unassigned": []},
            {"operator": "reset", "unassigned": []},
        ])
    );
    assert_eq!(ex.report["init_unassigned"], serde_json::json!([]));
    assert!(!ex.cfg.contains("never assigns"), "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &bounded(&ex, "n < 3"));
    assert_eq!(run.violated, Vec::<String>::new());
}

/// A crate function named `unwrap` (Option's is still `.v0`), Euclidean
/// division and remainder by a negative divisor, a state field named like
/// the generated `vars`, and a predicate `next` reads as a guard.
const NAMES: &str = r#"
verus! {
pub struct Pair { pub a: int, pub b: int }

impl Pair {
    pub open spec fn unwrap(self) -> int { self.a + self.b }
}

pub struct State { pub x: int, pub vars: int, pub p: Pair, pub o: Option<int> }

pub open spec fn init(s: State) -> bool {
    s == State { x: 0, vars: 0, p: Pair { a: 1, b: 2 }, o: Some(5int) }
}

pub open spec fn safe(s: State) -> bool { s.x <= 3 }

pub open spec fn next(pre: State, post: State) -> bool {
    &&& safe(pre)
    &&& pre.x < 3
    &&& pre.o is Some
    &&& post == State { x: pre.x + 1, vars: pre.vars + pre.p.unwrap() + pre.o.unwrap(), ..pre }
}

pub open spec fn vars_value(s: State) -> bool { s.vars == 8 * s.x }

pub open spec fn euclid(s: State) -> bool {
    &&& (s.x - 7) / -2int == (if s.x == 0 { 4int } else if s.x == 1 { 3 } else if s.x == 2 { 3 } else { 2 })
    &&& (s.x - 7) % -2int == (if s.x == 0 || s.x == 2 { 1int } else { 0 })
    &&& (s.x - 7) / 2 == (if s.x == 0 { -4int } else if s.x == 1 { -3 } else if s.x == 2 { -3 } else { -2 })
    &&& (s.x - 7) % 2 == (if s.x == 0 || s.x == 2 { 1int } else { 0 })
}

pub open spec fn x_small(s: State) -> bool { s.x <= 2 }
}
"#;

#[test]
fn tla_export_names_and_euclidean_arithmetic() {
    let ex = export_code(NAMES, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    // The generated `vars` keeps its name; the field's variable is renamed.
    assert_eq!(names(&ex.report["variables"]), ["x", "vars_v", "p", "o"]);
    assert!(
        ex.tla.contains("VARIABLES x, vars_v, p, o\nvars == <<x, vars_v, p, o>>"),
        "{}",
        ex.tla
    );
    // `Pair::unwrap` is the crate's function, not Option's `.v0`.
    assert!(ex.tla.contains("unwrap(p)"), "{}", ex.tla);
    assert!(ex.tla.contains("o.v0"), "{}", ex.tla);
    assert!(!ex.tla.contains("arrow_0"), "{}", ex.tla);
    // A positive literal divisor keeps `\div` and `%`; a negative one does not.
    assert!(ex.tla.contains("EuclidDiv("), "{}", ex.tla);
    assert!(ex.tla.contains("\\div 2)"), "{}", ex.tla);
    // `safe` is a guard of `next`: excluded, and said so, not dropped.
    assert_eq!(names(&ex.report["invariants"]), ["vars_value", "euclid", "x_small"]);
    let c = candidates(&ex.report);
    assert!(c.contains(&("safe".into(), false)), "{:?}", c);
    let safe = ex.report["candidates"]
        .as_array()
        .unwrap()
        .iter()
        .find(|c| c["function"] == "test_crate::safe")
        .unwrap();
    assert!(safe["reason"].as_str().unwrap().starts_with("reached from init/next"), "{}", safe);
    assert!(ex.cfg.contains("test_crate::safe is not checked"), "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    // x reaches 3; everything but x_small holds (with Verus's `/` and `%`).
    assert_eq!(run.violated, ["x_small"], "{}", ex.tla);
    assert_eq!(run.distinct, 4, "{run:?}");
}

#[test]
fn tla_export_checks_exactly_the_named_invariants() {
    let ex = export_code(NAMES, "test_crate:safe,euclid");
    assert_eq!(names(&ex.report["invariants"]), ["safe", "euclid"]);
    let c = candidates(&ex.report);
    assert!(c.contains(&("safe".into(), true)), "{:?}", c);
    assert!(c.contains(&("x_small".into(), false)), "{:?}", c);
    assert!(ex.cfg.contains("INVARIANTS\n  safe\n  euclid\n"), "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
}

#[test]
fn tla_export_rejects_an_unknown_invariant() {
    let src = TempDir::new().expect("temp dir");
    let entry = src.path().join("test.rs");
    std::fs::write(&entry, format!("{}\n{}\n{}\n", FEATURE_PRELUDE, USE_PRELUDE, NAMES)).unwrap();
    let log = src.path().join("log");
    let options =
        ["-V tla-export=test_crate:nope".to_string(), format!("--log-dir {}", log.display())];
    let options: Vec<&str> = options.iter().map(|s| s.as_str()).collect();
    let output = run_verus(&options, src.path(), &entry, true, true);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(!output.status.success(), "{}", stderr);
    assert!(stderr.contains("no invariant `nope` in `test_crate`"), "{}", stderr);
}

/// State fields named like the Euclidean operators' parameters would once
/// have been (`a`, `b`): TLA+ forbids a parameter that redefines a variable.
const EUCLID_FIELDS: &str = r#"
verus! {
pub struct State { pub a: int, pub b: int }

pub open spec fn init(s: State) -> bool { s.a == 7 && s.b == -2 }

pub open spec fn next(pre: State, post: State) -> bool {
    pre.b < 0 && post.a == pre.a / pre.b && post.b == -pre.b
}

pub open spec fn rem_nonneg(s: State) -> bool { s.a % s.b >= 0 }

pub open spec fn quotient(s: State) -> bool { s.b < 0 || s.a == -3 }
}
"#;

#[test]
fn tla_export_euclid_parameters_do_not_clash_with_fields() {
    let ex = export_code(EUCLID_FIELDS, "test_crate");
    assert_eq!(names(&ex.report["variables"]), ["a", "b"]);
    assert!(ex.tla.contains("EuclidDiv(a, b)"), "{}", ex.tla);
    assert!(!ex.tla.contains("EuclidMod(a, b) =="), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    // 7 / -2 is -3 in Verus (remainder 1), and -3 % 2 is 1.
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 2, "{run:?}");
}

/// A narrowing cast gives an out-of-range value some unspecified value of the
/// type. It is printed as a value check: TLC stops, naming the cast, in the
/// reached state where `(pre.x + 1) as u8` leaves `u8` (x = 255). A literal
/// is decided statically: kept in range, refused (tainting `wide`) out of it.
const CLIP: &str = r#"
verus! {
pub struct State { pub x: u8 }

pub open spec fn init(s: State) -> bool { s.x == 254int as u8 }

pub open spec fn next(pre: State, post: State) -> bool { post.x == (pre.x + 1) as u8 }

pub open spec fn in_range(s: State) -> bool { s.x <= 255 }

pub open spec fn wide(s: State) -> bool { s.x != 300int as u8 }
}
"#;

#[test]
fn tla_export_checks_a_narrowing_cast_where_it_is_evaluated() {
    let ex = export_code(CLIP, "test_crate");
    let refusals = ex.report["refusals"].as_array().unwrap();
    assert_eq!(refusals.len(), 1, "{refusals:?}");
    assert_eq!(refusals[0]["what"], "cast to u8 of a literal out of range");
    assert_eq!(refusals[0]["in_function"], "test_crate::wide");
    // The in-range literal is kept; the out-of-range one taints `wide`.
    assert!(ex.tla.contains("(x = 254)"), "{}", ex.tla);
    assert!(
        ex.tla.contains("IF (0 <= c__ /\\ c__ <= 255) THEN c__ ELSE Assert(FALSE, \"tla-export: value out of range of u8 in a cast at "),
        "{}",
        ex.tla
    );
    assert_eq!(names(&ex.report["invariants"]), ["in_range"]);
    assert_eq!(names(&ex.report["skipped_invariants"]), ["wide"]);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    // 254 and 255 are reached; the step from 255 stops TLC at the cast.
    let out = tlc_output(&jar, &ex.spec(), &ex.cfg);
    assert!(out.contains("tla-export: value out of range of u8 in a cast at"), "{}", out);
    assert!(out.contains("x = 255"), "{}", out);
}

/// A narrowing cast behind the guard that keeps it in range, the usual
/// shape of a decrement: the value check never fails, nothing is refused,
/// and the invariant is checked (the cast was a refusal that made the only
/// transition fail).
const GUARDED_CAST: &str = r#"
verus! {
pub struct State { pub x: nat, pub y: u8 }

pub open spec fn init(s: State) -> bool { s.x == 2 && s.y == 3 }

pub open spec fn dec(pre: State, post: State) -> bool {
    pre.x > 0 && post.x == (pre.x - 1) as nat && post.y == (pre.y - 1) as u8
}

pub open spec fn next(pre: State, post: State) -> bool { dec(pre, post) }

pub open spec fn small(s: State) -> bool { s.x <= 2 && s.y >= 1 && (s.y - 1) as nat <= 2 }
}
"#;

#[test]
fn tla_export_keeps_a_guarded_narrowing_cast() {
    let ex = export_code(GUARDED_CAST, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["small"]);
    assert_eq!(names(&ex.report["skipped_invariants"]), Vec::<String>::new());
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // x from 2 down to 0 (y from 3 down to 1).
    assert_eq!(run.distinct, 3, "{run:?}");
}

/// A quantifier over a generic datatype is bounded per instantiation:
/// `Option<bool>` from BOOLEAN, `Option<int>` by a constant of its own.
const OPTIONS: &str = r#"
verus! {
pub struct State { pub x: int }

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn next(pre: State, post: State) -> bool { pre.x < 2 && post.x == pre.x + 1 }

pub open spec fn id_bool(o: Option<bool>) -> Option<bool> { o }

pub open spec fn id_int(o: Option<int>) -> Option<int> { o }

pub open spec fn some_bool(s: State) -> bool {
    exists|o: Option<bool>| #[trigger] id_bool(o) == Some(s.x > 0)
}

pub open spec fn some_int(s: State) -> bool {
    exists|o: Option<int>| #[trigger] id_int(o) == Some(s.x)
}
}
"#;

#[test]
fn tla_export_bounds_a_generic_datatype_per_instantiation() {
    let ex = export_code(OPTIONS, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    let holes = ex.report["holes"].as_array().unwrap();
    assert_eq!(holes.len(), 1, "{holes:?}");
    assert_eq!(holes[0]["constant"], "Dom_Option_int_Some_v0");
    assert_eq!(holes[0]["typ"], "int");
    assert!(ex.tla.contains("v0__ \\in BOOLEAN"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let cfg = format!("{}CONSTANTS Dom_Option_int_Some_v0 = {{0, 1, 2}}\n", ex.cfg);
    let run = tlc(&jar, &ex.spec(), &cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 3, "{run:?}");
}

/// A transition that primes only some variables: TLC cannot complete the
/// successor, so the report and the .cfg name what it leaves unassigned. A
/// helper a transition conjoins (`keep_y`) is part of it, not a transition.
const UNASSIGNED: &str = r#"
verus! {
pub struct State { pub x: int, pub y: int }

pub open spec fn init(s: State) -> bool { s.x == 0 && s.y == 0 }

pub open spec fn keep_y(pre: State, post: State) -> bool { post.y == pre.y }

pub open spec fn step_x(pre: State, post: State) -> bool {
    post.x == pre.x + 1 && keep_y(pre, post)
}

pub open spec fn step_y(pre: State, post: State) -> bool { post.y == pre.y + 1 }

pub open spec fn next(pre: State, post: State) -> bool { step_x(pre, post) || step_y(pre, post) }
}
"#;

#[test]
fn tla_export_reports_unassigned_variables_per_transition() {
    let ex = export_code(UNASSIGNED, "test_crate");
    assert_eq!(
        ex.report["transitions"],
        serde_json::json!([
            {"operator": "step_x", "unassigned": []},
            {"operator": "step_y", "unassigned": ["x"]},
        ])
    );
    assert!(ex.cfg.contains("\\* Transition step_y never assigns x:"), "{}", ex.cfg);
    assert!(!ex.cfg.contains("step_x never"), "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
}

/// Fields of bounded integer types, directly and inside a record, an enum
/// payload, an Option and a Seq. In Verus the state is always within its
/// types, so `dec` is disabled at x = 0 and `inc` at b = 255; without TypeOK
/// TLC ran x below 0 and b up to 256, and reported `sum_in_range` (which
/// Verus proves) violated.
const TYPED: &str = r#"
use vstd::prelude::*;
verus! {
pub struct Inner { pub c: u8, pub n: int }

pub enum Tag { A, B(i8) }

pub struct State { pub x: nat, pub b: u8, pub i: Inner, pub o: Option<u16>, pub t: Tag, pub s: Seq<u8> }

pub open spec fn init(s: State) -> bool {
    &&& s.x == 2
    &&& s.b == 254
    &&& s.i == Inner { c: 1, n: 0 }
    &&& s.o == None::<u16>
    &&& s.t == Tag::A
    &&& s.s == Seq::<u8>::empty()
}

pub open spec fn dec(pre: State, post: State) -> bool {
    post.x == pre.x - 1 && post.b == pre.b && post.i == pre.i && post.o == pre.o && post.t == pre.t
        && post.s == pre.s
}

pub open spec fn inc(pre: State, post: State) -> bool {
    post.b == pre.b + 1 && post.x == pre.x && post.i == pre.i && post.o == pre.o && post.t == pre.t
        && post.s == pre.s
}

pub open spec fn next(pre: State, post: State) -> bool { dec(pre, post) || inc(pre, post) }

pub open spec fn sum_in_range(s: State) -> bool { s.x + s.b <= 257 }
}
"#;

#[test]
fn tla_export_keeps_bounded_integers_in_their_types() {
    let ex = export_code(TYPED, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(names(&ex.report["typed_variables"]), ["x", "b", "i", "o", "t", "s"]);
    for pred in [
        "/\\ (x >= 0)\n",
        "/\\ (0 <= b /\\ b <= 255)\n",
        "/\\ (0 <= i.c /\\ i.c <= 255)\n",
        "/\\ (o.tag = \"Some\" => (0 <= o.v0 /\\ o.v0 <= 65535))\n",
        "/\\ (t.tag = \"B\" => (-128 <= t.v0 /\\ t.v0 <= 127))\n",
        "/\\ (\\A i__ \\in 1..Len(s) : (0 <= s[i__] /\\ s[i__] <= 255))\n",
        "Init == init /\\ TypeOK\n",
        "Next == next /\\ TypeOK'\n",
    ] {
        assert!(ex.tla.contains(pred), "{pred}\n{}", ex.tla);
    }
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    // The bound only keeps a regression from running forever.
    let run = tlc(&jar, &ex.spec(), &bounded(&ex, "x > -3 /\\ b < 258"));
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // x in 0..2, b in 254..255.
    assert_eq!(run.distinct, 6, "{run:?}");
}

/// A trait method call resolved to an impl runs the impl's body, which the
/// trait's declaration lacks.
const TRAIT_IMPL: &str = r#"
verus! {
pub trait Measure { spec fn measure(&self) -> int; }

pub struct State { pub x: int }

impl Measure for State {
    open spec fn measure(&self) -> int { self.x * 2 }
}

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn next(pre: State, post: State) -> bool { pre.x < 3 && post.x == pre.x + 1 }

pub open spec fn measured(s: State) -> bool { s.measure() <= 6 }
}
"#;

#[test]
fn tla_export_calls_the_impl_of_a_trait_method() {
    let ex = export_code(TRAIT_IMPL, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["measured"]);
    assert!(ex.tla.contains("(x * 2)"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 4, "{run:?}");
}

/// Only a conjunct-level `v' = e` assigns `v`: not a guard reading `v'`, not
/// a predicate conjoined on the post state, not a negated equality, and an
/// `IF` only when both arms assign.
const GUARDS: &str = r#"
verus! {
pub struct State { pub x: int, pub y: int }

pub open spec fn init(s: State) -> bool { s.x == 0 && s.y == 0 }

pub open spec fn pos(s: State) -> bool { s.y >= 0 }

pub open spec fn guard_only(pre: State, post: State) -> bool { post.x == pre.x + 1 && post.y >= 0 }

pub open spec fn via_primed(pre: State, post: State) -> bool { post.x == pre.x + 1 && pos(post) }

pub open spec fn negated(pre: State, post: State) -> bool { post.x == pre.x + 1 && post.y != pre.y }

pub open spec fn both_arms(pre: State, post: State) -> bool {
    post.x == pre.x + 1 && (if pre.x < 3 { post.y == 1 } else { post.y == 2 })
}

pub open spec fn one_arm(pre: State, post: State) -> bool {
    post.x == pre.x + 1 && (if pre.x < 3 { post.y == 1 } else { true })
}

pub open spec fn next(pre: State, post: State) -> bool {
    guard_only(pre, post) || via_primed(pre, post) || negated(pre, post) || both_arms(pre, post)
        || one_arm(pre, post)
}
}
"#;

#[test]
fn tla_export_counts_only_conjunct_level_assignments() {
    let ex = export_code(GUARDS, "test_crate");
    assert_eq!(
        ex.report["transitions"],
        serde_json::json!([
            {"operator": "both_arms", "unassigned": []},
            {"operator": "guard_only", "unassigned": ["y"]},
            {"operator": "negated", "unassigned": ["y"]},
            {"operator": "one_arm", "unassigned": ["y"]},
            {"operator": "via_primed", "unassigned": ["y"]},
        ])
    );
    assert!(ex.cfg.contains("\\* Transition guard_only never assigns y:"), "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
}

/// Backslashes and quotes in character (and string) literals are escaped.
const ESCAPES: &str = r#"
verus! {
pub struct State { pub c: char }

pub open spec fn init(s: State) -> bool { s.c == '\\' }

pub open spec fn next(pre: State, post: State) -> bool {
    post.c == (if pre.c == '\\' { '"' } else { '\\' })
}

pub open spec fn alternates(s: State) -> bool { s.c == '\\' || s.c == '"' }
}
"#;

#[test]
fn tla_export_escapes_string_literals() {
    let ex = export_code(ESCAPES, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert!(ex.tla.contains("(c = \"\\\\\")"), "{}", ex.tla);
    assert!(ex.tla.contains("\"\\\"\""), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 2, "{run:?}");
}

/// A frame condition with the post state on the right: TLC assigns only a
/// primed variable on the left, so `pre.y == post.y` must print as
/// `y' = y` (as `(y = y')` TLC stopped: "the identifier y is either undefined
/// or not an operator"), and likewise for `=~=`.
const REVERSED: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: nat, pub y: nat, pub s: Seq<int> }

pub open spec fn init(s: State) -> bool { s.x == 0 && s.y == 5 && s.s == Seq::<int>::empty() }

pub open spec fn next(pre: State, post: State) -> bool {
    &&& pre.x < 3
    &&& post.x == pre.x + 1
    &&& pre.y == post.y
    &&& pre.s =~= post.s
}

pub open spec fn y_fixed(s: State) -> bool { s.y == 5 && s.s.len() == 0 }
}
"#;

#[test]
fn tla_export_puts_the_assigned_variable_on_the_left() {
    let ex = export_code(REVERSED, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert!(ex.tla.contains("(y' = y)"), "{}", ex.tla);
    assert!(ex.tla.contains("(s' = s)"), "{}", ex.tla);
    assert_eq!(
        ex.report["transitions"],
        serde_json::json!([{"operator": "next", "unassigned": []}])
    );
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 4, "{run:?}");
}

/// A primed field on both sides: the one assigned earlier (in the operator,
/// or before an enclosing branch) goes on the right and the other is
/// assigned.
const BOTH_PRIMED: &str = r#"
verus! {
pub struct State { pub x: int, pub y: int }

pub open spec fn init(s: State) -> bool { s.x == 0 && s.y == 0 }

pub open spec fn copy_after(pre: State, post: State) -> bool {
    pre.x < 2 && post.x == pre.x + 1 && post.x == post.y
}

pub open spec fn copy_in_branch(pre: State, post: State) -> bool {
    &&& pre.x < 2
    &&& post.x == pre.x + 2
    &&& if pre.x == 0 { post.y == post.x } else { post.x == post.y }
}

pub open spec fn next(pre: State, post: State) -> bool {
    copy_after(pre, post) || copy_in_branch(pre, post)
}

pub open spec fn same(s: State) -> bool { s.x == s.y }
}
"#;

#[test]
fn tla_export_orients_an_equality_of_two_primed_fields() {
    let ex = export_code(BOTH_PRIMED, "test_crate");
    assert_eq!(
        ex.report["transitions"],
        serde_json::json!([
            {"operator": "copy_after", "unassigned": []},
            {"operator": "copy_in_branch", "unassigned": []},
        ])
    );
    assert!(ex.tla.contains("(y' = x')"), "{}", ex.tla);
    assert!(!ex.tla.contains("(x' = y')"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // (0,0), (1,1), (2,2), (3,3).
    assert_eq!(run.distinct, 4, "{run:?}");
}

/// Neither primed field assigned yet: the equality assigns nothing, and the
/// transition is reported (TLC cannot evaluate `y' = x'` there).
const BOTH_PRIMED_FIRST: &str = r#"
verus! {
pub struct State { pub x: int, pub y: int }

pub open spec fn init(s: State) -> bool { s.x == 0 && s.y == 0 }

pub open spec fn next(pre: State, post: State) -> bool {
    pre.x < 2 && post.y == post.x && post.x == pre.x + 1
}
}
"#;

#[test]
fn tla_export_reports_an_equality_of_two_unassigned_primed_fields() {
    let ex = export_code(BOTH_PRIMED_FIRST, "test_crate");
    assert_eq!(
        ex.report["transitions"],
        serde_json::json!([{"operator": "next", "unassigned": ["y"]}])
    );
    assert!(ex.cfg.contains("\\* Transition next never assigns y:"), "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
}

/// A hand-rolled invariant named `invariant` is checked by default.
const NAMED_INVARIANT: &str = r#"
verus! {
pub struct State { pub x: int }

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn next(pre: State, post: State) -> bool { pre.x < 3 && post.x == pre.x + 1 }

// Violated: x reaches 3.
pub open spec fn invariant(s: State) -> bool { s.x < 3 }
}
"#;

#[test]
fn tla_export_checks_a_hand_rolled_invariant_named_invariant() {
    let ex = export_code(NAMED_INVARIANT, "test_crate");
    assert_eq!(names(&ex.report["invariants"]), ["invariant"]);
    assert!(ex.cfg.contains("INVARIANTS\n  invariant\n"), "{}", ex.cfg);
    assert!(!ex.cfg.contains("No invariant is checked"), "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, ["invariant"], "{}", ex.tla);
}

/// No invariant checked: the .cfg says so rather than let TLC report "No
/// error has been found" silently, with no candidate at all or with the
/// candidates and why none is included.
const NO_INVARIANT: &str = r#"
verus! {
pub struct State { pub x: int }

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn can_step(s: State) -> bool { s.x < 3 }

pub open spec fn next(pre: State, post: State) -> bool { can_step(pre) && post.x == pre.x + 1 }
}
"#;

#[test]
fn tla_export_says_when_no_invariant_is_checked() {
    let ex = export_code(NO_INVARIANT, "test_crate");
    assert_eq!(names(&ex.report["invariants"]), Vec::<String>::new());
    assert!(!ex.cfg.contains("INVARIANTS"), "{}", ex.cfg);
    assert!(
        ex.cfg.contains("\\* No invariant is checked. The candidates (see the .tla.json report):\n\\*   test_crate::can_step: reached from init/next, unprimed or primed"),
        "{}",
        ex.cfg
    );
    let none = export_code(
        &NO_INVARIANT.replace("can_step(pre)", "pre.x < 3").replace(
            "pub open spec fn can_step(s: State) -> bool { s.x < 3 }",
            "pub open spec fn bump(x: int) -> int { x + 1 }",
        ),
        "test_crate",
    );
    assert!(
        none.cfg.contains("\\* No invariant is checked: the module has no candidate invariant.\n"),
        "{}",
        none.cfg
    );
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    sany(&jar, &none.spec());
}

/// `=~=` on the whole state assigns field by field, as `==` does (printed as
/// a record equality, TLC stopped at once: "the identifier x is either
/// undefined or not an operator").
const WHOLE_EXT_EQ: &str = r#"
verus! {
pub struct State { pub x: int, pub y: int }

pub open spec fn init(s: State) -> bool { s =~= State { x: 0, y: 0 } }

pub open spec fn next(pre: State, post: State) -> bool {
    pre.x < 2 && post =~= State { x: pre.x + 1, ..pre }
}

pub open spec fn small(s: State) -> bool { s.x <= 2 && s.y == 0 }
}
"#;

#[test]
fn tla_export_assigns_a_whole_state_ext_equality() {
    let ex = export_code(WHOLE_EXT_EQ, "test_crate");
    assert!(ex.tla.contains("(x = 0 /\\ y = 0)"), "{}", ex.tla);
    assert!(ex.tla.contains("x' = (x + 1) /\\ y' = "), "{}", ex.tla);
    assert_eq!(
        ex.report["transitions"],
        serde_json::json!([{"operator": "next", "unassigned": []}])
    );
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 3, "{run:?}");
}

/// A frame condition factored out of a disjunction: every step assigns `z`
/// through the caller, and `next` assigns `x` and `y` through its branches,
/// so nothing is unassigned (all three used to be reported, though TLC
/// checks the model).
const FRAME: &str = r#"
verus! {
pub struct State { pub x: int, pub y: int, pub z: int }

pub open spec fn init(s: State) -> bool { s.x == 0 && s.y == 0 && s.z == 0 }

pub open spec fn step_x(pre: State, post: State) -> bool {
    pre.x < 2 && post.x == pre.x + 1 && post.y == pre.y
}

pub open spec fn step_y(pre: State, post: State) -> bool {
    pre.y < 2 && post.y == pre.y + 1 && post.x == pre.x
}

pub open spec fn next(pre: State, post: State) -> bool {
    (step_x(pre, post) || step_y(pre, post)) && post.z == pre.z
}

pub open spec fn small(s: State) -> bool { s.x + s.y <= 4 && s.z == 0 }
}
"#;

#[test]
fn tla_export_counts_a_frame_condition_around_a_disjunction() {
    let ex = export_code(FRAME, "test_crate");
    assert_eq!(
        ex.report["transitions"],
        serde_json::json!([
            {"operator": "step_x", "unassigned": []},
            {"operator": "step_y", "unassigned": []},
        ])
    );
    assert!(!ex.cfg.contains("never assigns"), "{}", ex.cfg);
    // A step that really leaves `x` out is still reported, and only it.
    let gap = export_code(&FRAME.replace(" && post.x == pre.x\n", "\n"), "test_crate");
    assert_eq!(
        gap.report["transitions"],
        serde_json::json!([
            {"operator": "step_x", "unassigned": []},
            {"operator": "step_y", "unassigned": ["x"]},
        ])
    );
    // So is an inline branch that leaves it out: `next` is.
    let inline = export_code(
        &FRAME.replace("step_y(pre, post))", "(pre.y < 2 && post.y == pre.y + 1))"),
        "test_crate",
    );
    assert_eq!(
        inline.report["transitions"],
        serde_json::json!([
            {"operator": "next", "unassigned": ["x"]},
            {"operator": "step_x", "unassigned": []},
        ])
    );
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // x, y in 0..2.
    assert_eq!(run.distinct, 9, "{run:?}");
}

/// A widening cast (`u8` to `u16`, `i16`, `nat`) is the identity; a
/// narrowing one is a value check, which holds in every reached state here.
const WIDENING: &str = r#"
verus! {
pub struct State { pub b: u8 }

pub open spec fn init(s: State) -> bool { s.b == 0 }

pub open spec fn next(pre: State, post: State) -> bool { pre.b < 3 && post.b == pre.b + 1 }

pub open spec fn wide(s: State) -> bool {
    (s.b as u16) <= 3 && (s.b as i16) >= 0 && (s.b as nat) < 4 && (s.b as u32) != 5
}

pub open spec fn narrow(s: State) -> bool { (s.b as i8) >= 0 }
}
"#;

#[test]
fn tla_export_keeps_a_widening_cast() {
    let ex = export_code(WIDENING, "test_crate");
    assert!(ex.tla.contains("(b <= 3)"), "{}", ex.tla);
    assert!(ex.tla.contains("value out of range of i8"), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["wide", "narrow"]);
    assert_eq!(names(&ex.report["skipped_invariants"]), Vec::<String>::new());
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 4, "{run:?}");
}

/// A branch that is `false` never holds, so it needs to assign nothing:
/// `cond` assigns both variables on the branch that can hold (it was
/// reported as assigning neither, though TLC checks the model).
const FALSE_BRANCH: &str = r#"
verus! {
pub struct State { pub x: int, pub y: int }

pub open spec fn init(s: State) -> bool { s.x == 0 && s.y == 0 }

pub open spec fn step(pre: State, post: State) -> bool {
    pre.x < 3 && post == State { x: pre.x + 1, ..pre }
}

pub open spec fn cond(pre: State, post: State) -> bool {
    if pre.x > 10 { false } else { post.x == pre.x && post.y == pre.y + 1 && pre.y < 2 }
}

pub open spec fn next(pre: State, post: State) -> bool { step(pre, post) || cond(pre, post) }

pub open spec fn small(s: State) -> bool { s.x <= 3 && s.y <= 2 }
}
"#;

#[test]
fn tla_export_counts_a_false_branch_as_assigning_everything() {
    let ex = export_code(FALSE_BRANCH, "test_crate");
    assert_eq!(
        ex.report["transitions"],
        serde_json::json!([
            {"operator": "cond", "unassigned": []},
            {"operator": "step", "unassigned": []},
        ])
    );
    assert!(!ex.cfg.contains("never assigns"), "{}", ex.cfg);
    // A branch that is not `false` and assigns nothing is still counted.
    let gap = export_code(&FALSE_BRANCH.replace("{ false }", "{ pre.y > 0 }"), "test_crate");
    assert_eq!(
        gap.report["transitions"],
        serde_json::json!([
            {"operator": "cond", "unassigned": ["x", "y"]},
            {"operator": "step", "unassigned": []},
        ])
    );
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // x in 0..3, y in 0..2.
    assert_eq!(run.distinct, 12, "{run:?}");
}

/// An `init` that says nothing of `y`: TLC cannot compute the initial states
/// ("current state is not a legal state"), so the report and the .cfg name
/// it. `0 == s.x` counts, and is printed `x = 0` (TLC assigns only from the
/// left). A helper `init` calls with the state is followed, and one `next`
/// also calls as a guard (`is_zero`) assigns in Init only.
const INIT_GAP: &str = r#"
verus! {
pub struct State { pub x: nat, pub y: int }

pub open spec fn is_zero(s: State) -> bool { 0 == s.x }

pub open spec fn init(s: State) -> bool { is_zero(s) }

pub open spec fn next(pre: State, post: State) -> bool {
    &&& is_zero(pre) || pre.x < 2
    &&& post.x == pre.x + 1
    &&& post.y == pre.y
}

pub open spec fn small(s: State) -> bool { s.x <= 2 }
}
"#;

#[test]
fn tla_export_reports_what_init_leaves_unassigned() {
    let ex = export_code(INIT_GAP, "test_crate");
    assert_eq!(ex.report["init_unassigned"], serde_json::json!(["y"]));
    assert!(ex.cfg.contains("\\* Init never assigns y: TLC cannot compute"), "{}", ex.cfg);
    assert!(ex.tla.contains("(x = 0)"), "{}", ex.tla);
    // `is_zero(pre)` in next is a guard: Next assigns both variables.
    assert!(!ex.cfg.contains("Transition next never assigns"), "{}", ex.cfg);
    let fixed = export_code(
        &INIT_GAP
            .replace("{ is_zero(s) }", "{ is_zero(s) && if s.x == 0 { s.y == 5 } else { false } }"),
        "test_crate",
    );
    assert_eq!(fixed.report["init_unassigned"], serde_json::json!([]));
    assert!(!fixed.cfg.contains("Init never assigns"), "{}", fixed.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    sany(&jar, &fixed.spec());
    let run = tlc(&jar, &fixed.spec(), &fixed.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", fixed.tla);
    // x in 0..2, y = 5.
    assert_eq!(run.distinct, 3, "{run:?}");
}

/// An enum value carries its variant in the record label `tag`, so a field
/// named `tag` (in a variant, or in the state) is labelled `tag_`: the
/// record `[tag |-> "A", tag |-> 1]` was rejected by SANY.
const TAG_FIELD: &str = r#"
verus! {
pub enum Mode { A { tag: int }, B }

pub struct State { pub m: Mode, pub tag: int }

pub open spec fn init(s: State) -> bool { s.m == Mode::A { tag: 1 } && s.tag == 0 }

pub open spec fn next(pre: State, post: State) -> bool {
    match pre.m {
        Mode::A { tag } => tag < 3 && post.m == Mode::A { tag: tag + 1 } && post.tag == pre.tag,
        Mode::B => false,
    }
}

pub open spec fn small(s: State) -> bool {
    match s.m { Mode::A { tag } => tag <= 3 && s.tag == 0, Mode::B => false }
}
}
"#;

#[test]
fn tla_export_keeps_a_field_named_tag_apart_from_the_variant() {
    let ex = export_code(TAG_FIELD, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert!(ex.tla.contains("[tag |-> \"A\", tag_ |-> 1]"), "{}", ex.tla);
    assert_eq!(names(&ex.report["variables"]), ["m", "tag_"]);
    assert_eq!(
        ex.report["transitions"],
        serde_json::json!([{"operator": "next", "unassigned": []}])
    );
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // tag 1..3.
    assert_eq!(run.distinct, 3, "{run:?}");
}

/// Quantifiers over bounded integer types: a domain read off the guard is
/// intersected with the type's range (`x < 300` over `u8` was `0..299`, so
/// TLC found `all_small` FALSE and `no_witness`'s 256), a guard's open side
/// is closed by the type (`i8`), an unguarded binder of at most 16 bits takes
/// its whole range, and a wider one is a hole named after its type
/// (`Dom_u32`, once `Dom_int` like every integer binder).
const INT_BINDERS: &str = r#"
verus! {
pub struct State { pub n: nat }

pub open spec fn init(s: State) -> bool { s.n == 0 }

pub open spec fn next(pre: State, post: State) -> bool { pre.n < 1 && post.n == pre.n + 1 }

pub open spec fn f(x: u8) -> int { x as int }

pub open spec fn g(x: i8) -> int { x as int }

pub open spec fn h(x: u32) -> int { x as int }

pub open spec fn all_small(s: State) -> bool { forall|x: u8| x < 300 ==> #[trigger] f(x) <= 255 }

pub open spec fn no_witness(s: State) -> bool {
    !(exists|x: u8| x < 300 && #[trigger] f(x) == 256)
}

pub open spec fn i8_low(s: State) -> bool { forall|x: i8| x < 5 ==> #[trigger] g(x) >= -128 }

pub open spec fn u8_top(s: State) -> bool { exists|x: u8| #[trigger] f(x) == 255 }

pub open spec fn u32_nonneg(s: State) -> bool { forall|x: u32| #[trigger] h(x) >= 0 }

proof fn truths(s: State)
    ensures all_small(s), no_witness(s), i8_low(s), u8_top(s), u32_nonneg(s)
{
    assert(f(255u8) == 255);
}
}
"#;

#[test]
fn tla_export_bounds_integer_binders_by_their_type() {
    let ex = export_code(INT_BINDERS, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert!(
        ex.tla.contains("\\A x \\in 0..(IF ((300) - 1) < 255 THEN ((300) - 1) ELSE 255) :"),
        "{}",
        ex.tla
    );
    assert!(
        ex.tla.contains("\\A x \\in -128..(IF ((5) - 1) < 127 THEN ((5) - 1) ELSE 127) :"),
        "{}",
        ex.tla
    );
    assert!(ex.tla.contains("\\E x \\in 0..255 :"), "{}", ex.tla);
    let holes = ex.report["holes"].as_array().unwrap();
    assert_eq!(holes.len(), 1, "{holes:?}");
    assert_eq!(holes[0]["constant"], "Dom_u32");
    assert_eq!(holes[0]["typ"], "u32");
    assert_eq!(
        names(&ex.report["invariants"]),
        ["all_small", "no_witness", "i8_low", "u8_top", "u32_nonneg"]
    );
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let cfg = format!("{}CONSTANTS Dom_u32 = {{0, 1}}\n", ex.cfg);
    let run = tlc(&jar, &ex.spec(), &cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 2, "{run:?}");
}

/// A chained guard bounds a binder through a later one: `0 <= a < b < len`
/// gives `a` the domain `0..len - 2` (it was a `Dom_int` hole).
const CHAINED: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub s: Seq<u8> }

pub open spec fn init(s: State) -> bool { s.s == Seq::<u8>::empty() }

pub open spec fn next(pre: State, post: State) -> bool {
    pre.s.len() < 3 && post.s == pre.s.push(pre.s.len() as u8)
}

pub open spec fn sorted(s: State) -> bool {
    forall|a: int, b: int| 0 <= a < b < s.s.len() ==> s.s[a] <= s.s[b]
}

pub open spec fn descending(s: State) -> bool {
    forall|a: int, b: int| s.s.len() > b > a >= 0 ==> s.s[a] < s.s[b]
}
}
"#;

#[test]
fn tla_export_bounds_a_binder_through_a_chained_guard() {
    let ex = export_code(CHAINED, "test_crate");
    assert_eq!(ex.report["holes"], serde_json::json!([]), "{}", ex.tla);
    assert!(ex.tla.contains("\\A a \\in 0..(Len(s)) - 2 :"), "{}", ex.tla);
    assert!(ex.tla.contains("\\A b \\in (a) + 1..(Len(s)) - 1 :"), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["sorted", "descending"]);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // The sequence grows from << >> to <<0, 1, 2>>.
    assert_eq!(run.distinct, 4, "{run:?}");
}

/// A predicate next reads only on the post state (`lit(post)`) is a guard,
/// not an invariant, as one read on the pre state is: it was checked, and
/// failed at Init.
const PRIMED_GUARD: &str = r#"
verus! {
pub struct State { pub on: bool, pub n: nat }

pub open spec fn init(s: State) -> bool { s.on == false && s.n == 0 }

pub open spec fn lit(s: State) -> bool { s.on }

pub open spec fn next(pre: State, post: State) -> bool {
    &&& pre.n < 2
    &&& post.n == pre.n + 1
    &&& post.on == false
    &&& !lit(post)
}

pub open spec fn small(s: State) -> bool { s.n <= 2 }
}
"#;

#[test]
fn tla_export_leaves_out_a_guard_read_on_the_post_state() {
    let ex = export_code(PRIMED_GUARD, "test_crate");
    assert_eq!(names(&ex.report["invariants"]), ["small"]);
    let c = candidates(&ex.report);
    assert!(c.contains(&("lit".into(), false)), "{:?}", c);
    let lit = ex.report["candidates"]
        .as_array()
        .unwrap()
        .iter()
        .find(|c| c["function"] == "test_crate::lit")
        .unwrap();
    assert!(lit["reason"].as_str().unwrap().starts_with("reached from init/next"), "{}", lit);
    assert!(ex.cfg.contains("\\* test_crate::lit is not checked"), "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 3, "{run:?}");
}

/// VerusSync lowers `assert` to `tmp_assert => (update ...)`: the updates
/// count as assigning (the transition was reported leaving `n` and `s`
/// unassigned, though TLC checks it).
#[test]
fn tla_export_counts_updates_under_a_verussync_assert() {
    let ex = export(&fixture("assert_sync.rs"), "test_crate::Guarded");
    assert_eq!(ex.report["shape"], "verussync");
    assert!(ex.tla.contains("tmp_assert_2 => (n' = update_tmp_n)"), "{}", ex.tla);
    assert_eq!(
        ex.report["transitions"],
        serde_json::json!([{"operator": "bump", "unassigned": []}])
    );
    assert!(!ex.cfg.contains("never assigns"), "{}", ex.cfg);
    assert_eq!(names(&ex.report["invariants"]), ["n_small"]);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // n from 0 to 3.
    assert_eq!(run.distinct, 4, "{run:?}");
}

/// `moved(post, pre)` swaps the callee's pre and post states: the call as a
/// whole is the refusal. Printed as an extra argument, the Assert gave
/// `moved` more arguments than its definition, and SANY rejected the module.
const SWAPPED_STATES: &str = r#"
verus! {
pub struct State { pub x: int }

pub open spec fn moved(a: State, b: State) -> bool { b.x == a.x + 1 }

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn next(pre: State, post: State) -> bool {
    pre.x < 2 && post.x == pre.x + 1 && moved(post, pre)
}

pub open spec fn small(s: State) -> bool { s.x <= 2 }
}
"#;

#[test]
fn tla_export_refuses_a_swapped_state_as_the_whole_call() {
    let ex = export_code(SWAPPED_STATES, "test_crate");
    let refusals: Vec<String> = ex.report["refusals"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r["what"].as_str().unwrap().to_string())
        .collect();
    assert_eq!(refusals.len(), 1, "{refusals:?}");
    assert!(refusals[0].contains("post state passed where the callee expects its pre"));
    assert!(!ex.tla.contains("moved("), "{}", ex.tla);
    // Only Next reaches the refusal; the invariant is still checked.
    assert_eq!(names(&ex.report["invariants"]), ["small"]);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    // TLC stops where the refused call is evaluated, with its reason.
    let out = tlc_output(&jar, &ex.spec(), &ex.cfg);
    assert!(out.contains("tla-export refused: post state passed"), "TLC output:\n{}", out);
}

/// A recursive walk holds the state as a record, so the per-index predicate
/// it calls, and a helper given a constructed state, take theirs as a
/// record too (the `_rec` variant) rather than being refused.
const RECORD_STATE: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub a: Seq<u8>, pub k: nat }

pub open spec fn ok_at(s: State, i: int) -> bool { s.a[i] <= 3 }

pub open spec fn all_le(s: State, i: nat) -> bool decreases i {
    if i == 0 { true } else { s.a.len() >= i ==> ok_at(s, i - 1) && all_le(s, (i - 1) as nat) }
}

pub open spec fn k_le(s: State, n: nat) -> bool { s.k <= n }

pub open spec fn init(s: State) -> bool { s.a == Seq::<u8>::empty() && s.k == 0 }

pub open spec fn next(pre: State, post: State) -> bool {
    &&& pre.k < 3
    &&& post.k == pre.k + 1
    &&& post.a == pre.a.push(pre.k as u8)
}

pub open spec fn good(s: State) -> bool { all_le(s, s.a.len()) }

pub open spec fn reset_ok(s: State) -> bool { k_le(State { k: 0, ..s }, 0) }
}
"#;

#[test]
fn tla_export_passes_a_record_state_to_a_state_helper() {
    let ex = export_code(RECORD_STATE, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["good", "reset_ok"]);
    assert!(ex.tla.contains("ok_at_rec(s, (i - 1))"), "{}", ex.tla);
    assert!(ex.tla.contains("k_le_rec("), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // k in 0..3, `a` the pushes so far.
    assert_eq!(run.distinct, 4, "{run:?}\n{}", ex.tla);
}

/// `s.o.is_none()` and `s.p is None` in Init, and `post.p is None` in Next,
/// say the field is the `None` record: printed as that equality, they
/// assign it, so TLC can compute the states.
const NONE_INIT: &str = r#"
verus! {
pub struct State { pub o: Option<int>, pub p: Option<int>, pub x: int }

pub open spec fn init(s: State) -> bool { s.o.is_none() && s.p is None && s.x == 0 }

pub open spec fn next(pre: State, post: State) -> bool {
    &&& pre.x < 2
    &&& post.x == pre.x + 1
    &&& post.o == Some(pre.x)
    &&& post.p is None
}

pub open spec fn inv(s: State) -> bool { s.p is None && (s.o is None || s.o.unwrap() < 2) }
}
"#;

#[test]
fn tla_export_assigns_a_none_check() {
    let ex = export_code(NONE_INIT, "test_crate");
    assert_eq!(ex.report["init_unassigned"], serde_json::json!([]), "{}", ex.tla);
    assert!(!ex.cfg.contains("never assigns"), "{}", ex.cfg);
    assert!(ex.tla.contains("(o = [tag |-> \"None\"])"), "{}", ex.tla);
    assert!(ex.tla.contains("(p = [tag |-> \"None\"])"), "{}", ex.tla);
    assert!(ex.tla.contains("(p' = [tag |-> \"None\"])"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 3, "{run:?}\n{}", ex.tla);
}
