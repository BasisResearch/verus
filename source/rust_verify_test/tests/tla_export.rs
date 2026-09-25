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

/// Run TLC to completion on `spec` with `cfg` (deadlock is not an error,
/// and every violation is counted).
fn tlc(jar: &str, spec: &Path, cfg: &str) -> Tlc {
    let dir = spec.parent().unwrap();
    let cfg_path = spec.with_extension("cfg");
    std::fs::write(&cfg_path, cfg).unwrap();
    let meta = dir.join("states");
    let out = java(
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
    );
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

/// A cast to a bounded type is only known, by proof, to land in range: an
/// out-of-range value becomes some unspecified value of the type. Printed as
/// the identity it would leave the type (or, under TypeOK, disable the step),
/// so it is refused. A literal already in range is kept.
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
fn tla_export_refuses_a_cast_to_a_bounded_type() {
    let ex = export_code(CLIP, "test_crate");
    let refusals = ex.report["refusals"].as_array().unwrap();
    assert_eq!(refusals.len(), 2, "{refusals:?}");
    assert!(refusals.iter().all(|r| r["what"].as_str().unwrap().starts_with("cast to u8")));
    assert_eq!(refusals[0]["in_function"], "test_crate::next");
    // The in-range literal is kept; the out-of-range one taints `wide`.
    assert!(ex.tla.contains("(x = 254)"), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["in_range"]);
    assert_eq!(names(&ex.report["skipped_invariants"]), ["wide"]);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
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
