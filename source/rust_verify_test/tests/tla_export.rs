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
    export_with(entry, module, &[])
}

/// [`export`], with further options for Verus (`--no-verify`).
fn export_with(entry: &Path, module: &str, extra: &[&str]) -> Exported {
    let dir = TempDir::new().expect("temp dir");
    let log = dir.path().join("log");
    let options = [format!("-V tla-export={module}"), format!("--log-dir {}", log.display())];
    let mut options: Vec<&str> = options.iter().map(|s| s.as_str()).collect();
    options.extend_from_slice(extra);
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

/// Run a class from the TLA+ tools: whether java exited successfully, and
/// its stdout and stderr.
fn java(jar: &str, dir: &Path, args: &[&str]) -> (bool, String) {
    let out = std::process::Command::new("java")
        .arg(format!("-Djava.io.tmpdir={}", dir.display()))
        .args(["-cp", jar])
        .args(args)
        .current_dir(dir)
        .output()
        .expect("could not run java");
    let text =
        format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    (out.status.success(), text)
}

/// SANY's verdict on a spec: panics with its output unless java ran SANY to
/// the end of semantic processing of the module with no error. The positive
/// marker catches a SANY that never ran (a jar without it prints "Error:
/// Could not find or load main class", which no error pattern matched).
fn sany(jar: &str, spec: &Path) {
    let (ok, out) = java(jar, spec.parent().unwrap(), &["tla2sany.SANY", spec.to_str().unwrap()]);
    let module = spec.file_stem().unwrap().to_str().unwrap();
    assert!(
        ok && out.contains(&format!("Semantic processing of module {module}"))
            && !out.contains("*** Errors")
            && !out.contains("Fatal errors")
            && !out.contains("error"),
        "SANY rejected {} (or did not run):\n{out}",
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
    tlc_output_with(jar, spec, cfg, &["-deadlock", "-continue"])
}

/// TLC's output on `spec` with `cfg`, with `flags` before the spec.
fn tlc_output_with(jar: &str, spec: &Path, cfg: &str, flags: &[&str]) -> String {
    let dir = spec.parent().unwrap();
    let cfg_path = spec.with_extension("cfg");
    std::fs::write(&cfg_path, cfg).unwrap();
    let meta = dir.join("states");
    let mut args = vec!["tlc2.TLC", "-workers", "1"];
    args.extend_from_slice(flags);
    args.extend([
        "-metadir",
        meta.to_str().unwrap(),
        "-config",
        cfg_path.to_str().unwrap(),
        spec.to_str().unwrap(),
    ]);
    // TLC exits non-zero on a violation too; callers read the output.
    java(jar, dir, &args).1
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
    // As written, with no flag: count stops at 3, which Verus does not
    // count as an error, and the .cfg tells TLC so.
    assert!(ex.cfg.contains("SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\n"), "{}", ex.cfg);
    let out = tlc_output_with(&jar, &ex.spec(), &ex.cfg, &[]);
    assert!(out.contains("No error has been found"), "{}", out);
    assert!(!out.contains("Deadlock"), "{}", out);
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
    assert!(ex.tla.contains("RECURSIVE sumto_rec(_, _)"), "{}", ex.tla);
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
    // not be a state predicate: the state is passed as a record to the one
    // operator a recursive function has, its record variant.
    let ex = export_code(RECURSIVE_STATE, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["sum_is_n"]);
    assert!(ex.tla.contains("RECURSIVE sum_rec(_, _)"), "{}", ex.tla);
    assert!(!ex.tla.contains("sum_post"), "{}", ex.tla);
    assert!(ex.tla.contains("sum_rec([v |-> v', n |-> n'], Len(v'))"), "{}", ex.tla);
    assert!(ex.tla.contains("sum_rec([v |-> v, n |-> n], Len(v))"), "{}", ex.tla);
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

/// A `char` is a TLA+ string, so a cast from one and an ordering comparison
/// of two have no TLA+ meaning: each is refused where it occurs rather than
/// left for TLC to stop at with a type error, and a `char` binder's guard
/// gives no range (its domain is a hole).
const CHARS: &str = r#"
verus! {
pub struct State { pub x: u32, pub c: char }

pub open spec fn init(s: State) -> bool { s.x == 0 && s.c == 'a' }

pub open spec fn next(pre: State, post: State) -> bool {
    pre.x < 2 && post.x == pre.x + 1 && post.c == pre.c
}

pub open spec fn small(s: State) -> bool { s.x <= 2 && s.c == 'a' }

pub open spec fn code(s: State) -> bool { (s.c as u32) < 128 }

pub open spec fn wide(s: State) -> bool { s.c as int >= 0 }

pub open spec fn ordered(s: State) -> bool { 'a' <= s.c }

pub open spec fn chained(s: State) -> bool { 'a' <= s.c <= 'z' }

pub open spec fn is_c(d: char, s: State) -> bool { d == s.c }

pub open spec fn spread(s: State) -> bool {
    forall|d: char| #![trigger is_c(d, s)] 'b' <= d ==> !is_c(d, s)
}
}
"#;

#[test]
fn tla_export_refuses_char_casts_and_orderings() {
    let ex = export_code(CHARS, "test_crate");
    let whats: Vec<String> = ex.report["refusals"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r["what"].as_str().unwrap().to_string())
        .collect();
    // `s.c as u32` is a cast; `s.c as int` reaches VIR with the char type,
    // so its comparison with `0` is the one refused.
    assert_eq!(whats.iter().filter(|w| *w == "cast from char").count(), 1, "{whats:?}");
    assert_eq!(
        whats.iter().filter(|w| *w == "ordering comparison of chars").count(),
        4,
        "{whats:?}"
    );
    assert_eq!(names(&ex.report["invariants"]), ["small"]);
    assert_eq!(
        names(&ex.report["skipped_invariants"]),
        ["code", "wide", "ordered", "chained", "spread"]
    );
    // No range of strings: the char binder is a hole.
    let holes = ex.report["holes"].as_array().unwrap();
    assert_eq!(holes.len(), 1, "{holes:?}");
    assert_eq!(holes[0]["constant"], "Dom_char");
    assert!(!ex.tla.contains("\"..") && !ex.tla.contains("..\""), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let cfg = format!("{}CONSTANTS Dom_char = {{\"a\", \"b\"}}\n", ex.cfg);
    let run = tlc(&jar, &ex.spec(), &cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 3, "{run:?}");
}

/// Two datatypes of one name in different modules never share a hole
/// constant: the first takes the name, the second a suffix.
const SAME_NAMED: &str = r#"
verus! {
pub mod a { pub struct Id { pub v: u16 } }

pub mod b {
    use vstd::prelude::*;
    pub struct Id { pub v: int }
}

pub struct State { pub x: int }

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn next(pre: State, post: State) -> bool { pre.x < 2 && post.x == pre.x + 1 }

pub open spec fn ia(s: State) -> bool { forall|i: a::Id| i.v < 3 ==> s.x != 7 }

pub open spec fn ib(s: State) -> bool { forall|i: b::Id| i.v == s.x ==> s.x >= 0 }
}
"#;

#[test]
fn tla_export_names_same_named_datatypes_apart() {
    let ex = export_code(SAME_NAMED, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    let holes: Vec<(String, String)> = ex.report["holes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|h| {
            (h["constant"].as_str().unwrap().to_string(), h["typ"].as_str().unwrap().to_string())
        })
        .collect();
    assert_eq!(
        holes,
        [("Dom_Id_Id_v".to_string(), "u16".to_string()), ("Dom_Id_2_Id_v".into(), "int".into())]
    );
    assert_eq!(names(&ex.report["invariants"]), ["ia", "ib"]);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let cfg = format!(
        "{}CONSTANTS Dom_Id_Id_v = {{0, 1}}\nCONSTANTS Dom_Id_2_Id_v = {{0, 1, 2}}\n",
        ex.cfg
    );
    let run = tlc(&jar, &ex.spec(), &cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 3, "{run:?}");
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
/// is closed by the type (`i8`), an unguarded binder of at most 2^10 values
/// (`u8`) takes its whole range, and a wider one is a hole named after its type
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

/// VerusSync lowers `assert` to `tmp_assert => (update ...)`, printed as
/// `IF tmp_assert THEN (update ...) ELSE Assert(FALSE, ...)`: the updates
/// count as assigning (the transition was reported leaving `n` and `s`
/// unassigned, though TLC checks it).
#[test]
fn tla_export_counts_updates_under_a_verussync_assert() {
    let ex = export(&fixture("assert_sync.rs"), "test_crate::Guarded");
    assert_eq!(ex.report["shape"], "verussync");
    assert!(
        ex.tla.contains("(IF tmp_assert_2 THEN (n' = update_tmp_n) ELSE Assert(FALSE, "),
        "{}",
        ex.tla
    );
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

/// Under --no-verify a VerusSync `assert` is not proved. When one fails in
/// a reached state, TLC stops with the assertion's location and
/// transition, not "successor state not completely specified" or an
/// evaluation error. Of two asserts, the message names the one that fails
/// first: `n <= 1` fails at n = 2 while `n <= 3` still holds.
#[test]
fn tla_export_reports_a_failing_verussync_assert() {
    let fixture_code = std::fs::read_to_string(fixture("assert_sync.rs")).unwrap();
    let broken = fixture_code
        .replace("assert(pre.n <= 3);", "assert(pre.n <= 3);\n            assert(pre.n <= 1);");
    assert_ne!(broken, fixture_code, "the fixture's assert moved");
    let line = broken.lines().position(|l| l.contains("assert(pre.n <= 1);")).unwrap() + 1;
    let src = TempDir::new().expect("temp dir");
    let entry = src.path().join("assert_sync.rs");
    std::fs::write(&entry, broken).unwrap();
    let ex = export_with(&entry, "test_crate::Guarded", &["--no-verify"]);
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(
        ex.report["transitions"],
        serde_json::json!([{"operator": "bump", "unassigned": []}])
    );
    let second = "VerusSync assert in test_crate::Guarded::State::bump fails at ";
    assert!(ex.tla.contains(&format!("{second}{}:{line}:", entry.display())), "{}", ex.tla);
    assert!(ex.tla.contains(&format!("{}:{}:", entry.display(), line - 1)), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let out = tlc_output_with(&jar, &ex.spec(), &ex.cfg, &[]);
    assert!(out.contains("The first argument of Assert evaluated to FALSE"), "{}", out);
    assert!(out.contains(&format!("{second}{}:{line}:", entry.display())), "{}", out);
    assert!(!out.contains("not completely specified"), "{}", out);
}

/// `moved(post, pre)` swaps the callee's pre and post states: it is called
/// in its record variant, each state passed as its record, rather than
/// refused. `moved(post, pre)` says `pre.x == post.x + 1`, against `post.x ==
/// pre.x + 1`, so Next never holds, as in Verus: TLC finds the initial state
/// alone.
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
fn tla_export_passes_swapped_states_as_records() {
    let ex = export_code(SWAPPED_STATES, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert!(ex.tla.contains("moved_rec([x |-> x'], [x |-> x])"), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["small"]);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 1, "{run:?}\n{}", ex.tla);
}

/// A two-state helper given one state twice (`frame(post, post)`,
/// `same(pre, pre)`) fits neither its plain nor its primed variant: it is
/// called in its record variant, rather than refused (which stopped TLC on
/// every step).
const SAME_STATE_TWICE: &str = r#"
verus! {
pub struct State { pub a: u8, pub b: u8 }

pub open spec fn frame(x: State, y: State) -> bool { x.b == y.b }

pub open spec fn init(s: State) -> bool { s.a == 0 && s.b == 0 }

pub open spec fn next(pre: State, post: State) -> bool {
    &&& pre.a < 2
    &&& frame(pre, pre)
    &&& post.a == pre.a + 1
    &&& post.b == pre.b
    &&& frame(post, post)
}

pub open spec fn ok(s: State) -> bool { s.a <= 2 }
}
"#;

#[test]
fn tla_export_passes_one_state_given_twice_as_records() {
    let ex = export_code(SAME_STATE_TWICE, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert!(ex.tla.contains("frame_rec([a |-> a, b |-> b], [a |-> a, b |-> b])"), "{}", ex.tla);
    assert!(ex.tla.contains("frame_rec([a |-> a', b |-> b'], [a |-> a', b |-> b'])"), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["ok"]);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // a runs 0..2 with b fixed at 0.
    assert_eq!(run.distinct, 3, "{run:?}\n{}", ex.tla);
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

/// A recursive `(State) -> bool` spec fn `next` reads on the post state
/// (`cnt`), another the invariant (`other`), and a mutual recursion
/// (`is_even`/`is_odd`). A recursive function has only its record variant:
/// a primed copy declared RECURSIVE made SANY reject the module ("\land has
/// both temporal formula and action"). A recursive root is a wrapper
/// applying the record variant, and only the operators in a call cycle are
/// declared RECURSIVE.
const RECURSIVE_ROOT: &str = r#"
verus! {
pub struct State { pub n: nat, pub m: nat }

pub open spec fn init(s: State) -> bool { s.n == 0 && s.m == 0 }

pub open spec fn cnt(s: State) -> bool decreases s.n {
    if s.n == 0 { s.m <= 10 } else { cnt(State { n: (s.n - 1) as nat, ..s }) }
}

pub open spec fn other(s: State) -> bool decreases s.m {
    if s.m == 0 { s.n <= 3 } else { other(State { m: (s.m - 1) as nat, ..s }) }
}

pub open spec fn is_even(k: nat) -> bool decreases k {
    if k == 0 { true } else { is_odd((k - 1) as nat) }
}

pub open spec fn is_odd(k: nat) -> bool decreases k {
    if k == 0 { false } else { is_even((k - 1) as nat) }
}

pub open spec fn next(pre: State, post: State) -> bool {
    pre.n < 3 && post.n == pre.n + 1 && post.m == pre.m && cnt(post)
}

pub open spec fn parity(s: State) -> bool { is_even(s.n) != is_odd(s.n) }
}
"#;

#[test]
fn tla_export_gives_a_recursive_function_only_its_record_variant() {
    let ex = export_code(RECURSIVE_ROOT, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["other", "parity"]);
    assert!(!ex.tla.contains("cnt_post"), "{}", ex.tla);
    assert!(ex.tla.contains("cnt_rec([n |-> n', m |-> m'])"), "{}", ex.tla);
    assert!(ex.tla.contains("other ==\n    other_rec([n |-> n, m |-> m])"), "{}", ex.tla);
    let recursive: Vec<&str> = ex.tla.lines().filter(|l| l.starts_with("RECURSIVE")).collect();
    assert_eq!(
        recursive,
        [
            "RECURSIVE cnt_rec(_)",
            "RECURSIVE is_even_rec(_)",
            "RECURSIVE is_odd_rec(_)",
            "RECURSIVE other_rec(_)"
        ],
        "{}",
        ex.tla
    );
    // Named, `cnt` is checked too, through its wrapper.
    let named = export_code(RECURSIVE_ROOT, "test_crate:cnt,other");
    assert_eq!(names(&named.report["invariants"]), ["cnt", "other"]);
    assert!(named.tla.contains("cnt ==\n    cnt_rec([n |-> n, m |-> m])"), "{}", named.tla);
    assert!(!named.tla.contains("RECURSIVE cnt\n"), "{}", named.tla);
    let Some(jar) = tla_tools() else { return };
    for ex in [&ex, &named] {
        sany(&jar, &ex.spec());
        let run = tlc(&jar, &ex.spec(), &ex.cfg);
        assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
        // n in 0..3, m = 0.
        assert_eq!(run.distinct, 4, "{run:?}\n{}", ex.tla);
    }
}

/// Implications at conjunct level: TLC assigns in the consequent when the
/// guard holds, so one alone leaves the variable unassigned when it fails,
/// but two with complementary guards (`g`/`!g`, `y < 1`/`y >= 1`) assign
/// what both consequents do, in Next as in Init.
const IMPLICATIONS: &str = r#"
verus! {
pub struct State { pub f: bool, pub x: int, pub y: int }

pub open spec fn init(s: State) -> bool {
    s.f == false && (s.f ==> s.x == 1) && (!s.f ==> s.x == 0) && s.y == 0
}

pub open spec fn next(pre: State, post: State) -> bool {
    &&& post.f == !pre.f
    &&& pre.f ==> post.x == 1
    &&& !pre.f ==> post.x == 2
    &&& pre.y < 1 ==> post.y == pre.y + 1
    &&& pre.y >= 1 ==> post.y == pre.y
}

pub open spec fn small(s: State) -> bool { s.x <= 2 && s.y <= 1 }
}
"#;

#[test]
fn tla_export_pairs_implications_of_complementary_guards() {
    let ex = export_code(IMPLICATIONS, "test_crate");
    assert_eq!(ex.report["init_unassigned"], serde_json::json!([]), "{}", ex.tla);
    assert!(!ex.cfg.contains("never assigns"), "{}", ex.cfg);
    // A guard that is not the complement leaves `x` unassigned when neither
    // holds.
    let gap = export_code(
        &IMPLICATIONS.replace("!pre.f ==> post.x == 2", "pre.y < 5 ==> post.x == 2"),
        "test_crate",
    );
    assert_eq!(
        gap.report["transitions"],
        serde_json::json!([{ "operator": "next", "unassigned": ["x"] }]),
        "{}",
        gap.tla
    );
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // (f, x, y): (F, 0, 0), (T, 2, 1), (F, 1, 1).
    assert_eq!(run.distinct, 3, "{run:?}\n{}", ex.tla);
}

/// `seq![a, b, c]` is `<_ as View>::view(&[a, b, c])`: the array literal is
/// a sequence and the array's view the identity (it was refused, and an
/// invariant using it left out).
const SEQ_LITERAL: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: int, pub y: int }

pub open spec fn init(s: State) -> bool { s.x == 0 && s.y == 1 }

pub open spec fn next(pre: State, post: State) -> bool {
    pre.x < 2 && post.x == pre.x + 1 && post.y == seq![pre.y, 5int, 7int][1]
}

pub open spec fn first_is_x(s: State) -> bool {
    seq![s.x, s.y][0] == s.x && seq![s.x, s.y].len() == 2
}

pub open spec fn y_in(s: State) -> bool { seq![1int, 5int].contains(s.y) }
}
"#;

#[test]
fn tla_export_translates_a_seq_literal() {
    let ex = export_code(SEQ_LITERAL, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["first_is_x", "y_in"]);
    assert!(ex.tla.contains("(y' = <<y, 5, 7>>[(1) + 1])"), "{}", ex.tla);
    assert!(ex.tla.contains("Len(<<x, y>>)"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // x in 0..2, y 1 then 5.
    assert_eq!(run.distinct, 3, "{run:?}\n{}", ex.tla);
}

/// Guards the export once left unbounded: a membership guard annotated
/// `#[trigger]` (on a map's domain and on a set), and the body of an
/// `exists` that is a single guard (membership, and a chained range). Each
/// binder was a `Dom_int` hole. A spec const named like a TLA+ keyword
/// (`STATE`) is renamed.
const GUARD_SHAPES: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub m: Map<int, int>, pub s: Set<int>, pub v: Seq<int>, pub x: int }

pub spec const STATE: int = 3;

pub open spec fn init(s: State) -> bool {
    &&& s.m == Map::<int, int>::empty().insert(1, 1)
    &&& s.s == Set::<int>::empty().insert(2)
    &&& s.v == seq![4int, 5int]
    &&& s.x == 0
}

pub open spec fn next(pre: State, post: State) -> bool {
    &&& pre.x < STATE
    &&& post.x == pre.x + 1
    &&& post.m == pre.m
    &&& post.s == pre.s
    &&& post.v == pre.v
}

pub open spec fn m_pos(s: State) -> bool {
    forall|k: int| #[trigger] s.m.dom().contains(k) ==> s.m[k] > 0
}

pub open spec fn s_small(s: State) -> bool { forall|e: int| #[trigger] s.s.contains(e) ==> e < 10 }

pub open spec fn m_nonempty(s: State) -> bool { exists|k: int| s.m.dom().contains(k) }

pub open spec fn v_nonempty(s: State) -> bool {
    exists|i: int| #![trigger s.v[i]] 0 <= i < s.v.len()
}

pub open spec fn x_bounded(s: State) -> bool { s.x <= STATE }
}
"#;

#[test]
fn tla_export_bounds_trigger_and_single_exists_guards() {
    let ex = export_code(GUARD_SHAPES, "test_crate");
    assert_eq!(ex.report["holes"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(
        names(&ex.report["invariants"]),
        ["m_pos", "s_small", "m_nonempty", "v_nonempty", "x_bounded"]
    );
    assert!(!ex.tla.contains("CONSTANTS"), "{}", ex.tla);
    assert!(ex.tla.contains("\\A k \\in DOMAIN m :"), "{}", ex.tla);
    assert!(ex.tla.contains("\\A e \\in s :"), "{}", ex.tla);
    assert!(ex.tla.contains("\\E k \\in DOMAIN m :"), "{}", ex.tla);
    assert!(ex.tla.contains("\\E i \\in 0..(Len(v)) - 1 :"), "{}", ex.tla);
    assert!(ex.tla.contains("STATE_ ==\n"), "{}", ex.tla);
    assert!(!ex.tla.contains("STATE ==\n"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // x in 0..3, the rest fixed.
    assert_eq!(run.distinct, 4, "{run:?}\n{}", ex.tla);
}

/// The export reads the VIR crate before verification, so `--no-verify`
/// still writes it (it once wrote nothing and exited 0). The crate holds a
/// proof that does not verify, so the run succeeds only if nothing is
/// verified.
#[test]
fn tla_export_runs_under_no_verify() {
    let counter = std::fs::read_to_string(fixture("counter.rs")).unwrap();
    let broken = counter
        .replace("fn main() {\n}", "proof fn unprovable() ensures false {}\n\nfn main() {\n}");
    assert_ne!(broken, counter, "the fixture's main moved");
    let src = TempDir::new().expect("temp dir");
    let entry = src.path().join("counter.rs");
    std::fs::write(&entry, broken).unwrap();
    let ex = export_with(&entry, "test_crate", &["--no-verify"]);
    assert_eq!(ex.report["shape"], "hand-rolled");
    assert_eq!(names(&ex.report["invariants"]), ["bounded", "sum_small"]);
    assert!(ex.tla.contains("Next == next /\\ TypeOK'"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!((run.generated, run.distinct), (28, 18), "{run:?}");
}

/// A domain read off a type alone takes at most 2^10 values. A `u16`
/// binder is a `Dom_u16` hole rather than 65536 values, and a step variant
/// whose fields together take more (`Put(u16, u16)`, `Pair(u8, u8)`,
/// `Mixed(Option<int>, u8, u8)`) has a hole for each field of more than one
/// value; a hole bounding a field that became one (`Option<int>`'s payload)
/// is dropped. A small variant (`Nudge(u8)`, 256 values) is still whole.
const WIDE_STEPS: &str = r#"
verus! {
pub struct State { pub n: u16 }

pub enum Step { Put(u16, u16), Pair(u8, u8), Nudge(u8), Mixed(Option<int>, u8, u8) }

pub open spec fn init(s: State) -> bool { s.n == 0 }

pub open spec fn step(pre: State, post: State, st: Step) -> bool {
    match st {
        Step::Put(a, b) => a + b < 10 && post.n == a + b,
        Step::Pair(a, b) => a < b && post.n == b as u16,
        Step::Nudge(a) => a == 1 && pre.n < 20 && post.n == pre.n + a,
        Step::Mixed(o, a, b) => o is Some && b == 0 && post.n == a as u16,
    }
}

pub open spec fn next(pre: State, post: State) -> bool { exists|st: Step| step(pre, post, st) }

pub open spec fn f(x: u16) -> int { x as int }

pub open spec fn n_small(s: State) -> bool { forall|x: u16| #[trigger] f(x) == s.n ==> x < 30 }
}
"#;

#[test]
fn tla_export_caps_a_domain_read_off_a_type() {
    let ex = export_code(WIDE_STEPS, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    let mut constants: Vec<String> = ex.report["holes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|h| h["constant"].as_str().unwrap().to_string())
        .collect();
    constants.sort();
    assert_eq!(
        constants,
        [
            "Dom_Step_Mixed_v0",
            "Dom_Step_Mixed_v1",
            "Dom_Step_Mixed_v2",
            "Dom_Step_Pair_v0",
            "Dom_Step_Pair_v1",
            "Dom_Step_Put_v0",
            "Dom_Step_Put_v1",
            "Dom_u16",
        ],
        "{}",
        ex.tla
    );
    assert!(!ex.tla.contains("0..65535 :"), "{}", ex.tla);
    assert!(!ex.tla.contains("Dom_Option"), "{}", ex.tla);
    assert!(
        ex.tla.contains(
            "(\\E v0__3 \\in 0..255 : (LET st == [tag |-> \"Nudge\", v0 |-> v0__3] IN step(st)))"
        ),
        "{}",
        ex.tla
    );
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    // A record set or a range is not a .cfg value: an MC module extending
    // the export defines the domains and the .cfg substitutes them.
    let mc = ex.spec().with_file_name("MC.tla");
    std::fs::write(
        &mc,
        format!(
            "---- MODULE MC ----\nEXTENDS {}\n\
             MC_mixed == {{[tag |-> \"None\"], [tag |-> \"Some\", v0 |-> 1]}}\n\
             MC_u16 == 0..40\n====\n",
            ex.module
        ),
    )
    .unwrap();
    let cfg = format!(
        "{}CONSTANTS\n  Dom_Step_Put_v0 = {{0, 1, 2}}\n  Dom_Step_Put_v1 = {{0, 3}}\n  \
         Dom_Step_Pair_v0 = {{0, 1}}\n  Dom_Step_Pair_v1 = {{1, 25}}\n  \
         Dom_Step_Mixed_v0 <- MC_mixed\n  Dom_Step_Mixed_v1 = {{2}}\n  \
         Dom_Step_Mixed_v2 = {{0}}\n  Dom_u16 <- MC_u16\n",
        ex.cfg
    );
    let run = tlc(&jar, &mc, &cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // n reaches 0..20 (Put, Mixed, then Nudge) and 25 (Pair).
    assert_eq!(run.distinct, 22, "{run:?}\n{}", ex.tla);
}

/// verus-tla's invariants are closures over the state: a `() ->
/// spec_fn(int) -> bool` helper beside them is not one (it was printed with
/// the state record as its argument, `[count |-> count] > 0`).
const VERUS_TLA_HELPER: &str = r#"
verus! {
pub struct State { pub count: nat }

pub open spec fn init() -> spec_fn(State) -> bool { |s: State| s.count == 0 }

pub open spec fn next() -> spec_fn(State, State) -> bool {
    |pre: State, post: State| pre.count < 3 && post.count == pre.count + 1
}

pub open spec fn positive() -> spec_fn(int) -> bool { |i: int| i > 0 }

pub open spec fn small() -> spec_fn(State) -> bool { |s: State| s.count <= 3 }
}
"#;

#[test]
fn tla_export_verus_tla_takes_only_closures_over_the_state() {
    let ex = export_code(VERUS_TLA_HELPER, "test_crate");
    assert_eq!(ex.report["shape"], "verus-tla");
    assert_eq!(names(&ex.report["invariants"]), ["small"]);
    assert_eq!(candidates(&ex.report), [("small".to_string(), true)]);
    assert!(!ex.tla.contains("positive"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 4, "{run:?}");
}

/// The 2^10 cap holds for a datatype's variants together too: five
/// variants of 512 values each (2560 in all) have a hole per field, while
/// `Small` (3 values) is still enumerated whole.
const WIDE_UNION: &str = r#"
verus! {
pub enum Cmd { A(u8, bool), B(u8, bool), C(u8, bool), D(u8, bool), E(u8, bool) }

pub enum Small { On(bool), Off }

pub struct State { pub x: u8 }

pub open spec fn off(k: Small) -> bool { k is Off }

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn next(pre: State, post: State) -> bool {
    ||| exists|c: Cmd| c is A && c->A_1 && pre.x < 5 && post.x == c->A_0
    ||| exists|k: Small| #[trigger] off(k) && post.x == 0
}

pub open spec fn x_small(s: State) -> bool { s.x < 5 }
}
"#;

#[test]
fn tla_export_caps_the_union_of_a_datatypes_variants() {
    let ex = export_code(WIDE_UNION, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    let mut constants: Vec<String> = ex.report["holes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|h| h["constant"].as_str().unwrap().to_string())
        .collect();
    constants.sort();
    let expected: Vec<String> = ["A", "B", "C", "D", "E"]
        .iter()
        .flat_map(|v| [format!("Dom_Cmd_{v}_v0"), format!("Dom_Cmd_{v}_v1")])
        .collect();
    assert_eq!(constants, expected, "{}", ex.tla);
    assert!(!ex.tla.contains("0..255"), "{}", ex.tla);
    assert!(
        ex.tla.contains(
            "({[tag |-> \"On\", v0 |-> v0__6] : v0__6 \\in BOOLEAN} \\cup {[tag |-> \"Off\"]})"
        ),
        "{}",
        ex.tla
    );
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let mut cfg = format!("{}CONSTANTS\n", ex.cfg);
    for v in ["A", "B", "C", "D", "E"] {
        cfg.push_str(&format!("  Dom_Cmd_{v}_v0 = {{1, 4, 9}}\n  Dom_Cmd_{v}_v1 = {{TRUE}}\n"));
    }
    let run = tlc(&jar, &ex.spec(), &cfg);
    // x takes 0, 1 and 4; 9 is reached and violates x_small.
    assert_eq!(run.violated, ["x_small"], "{}", ex.tla);
}

/// A tuple binder is bounded as a datatype of one variant, its values TLA+
/// tuples: `(bool, u8)` whole (512 values), `(u8, u8)` (65536) a hole per
/// element; and a hole is named after the tuple's element types, so
/// `(u8, u8)` and `(int, bool)` never share one.
const TUPLE_BINDERS: &str = r#"
verus! {
pub struct State { pub x: u8 }

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn next(pre: State, post: State) -> bool {
    ||| exists|p: (u8, u8)| p.0 == p.1 && pre.x < 3 && post.x == p.0
    ||| exists|q: (bool, u8)| q.0 && q.1 == 2 && pre.x == 1 && post.x == q.1
}

pub open spec fn x_small(s: State) -> bool { forall|t: (int, bool)| t.1 ==> s.x < 3 + t.0 }
}
"#;

#[test]
fn tla_export_bounds_tuple_binders_by_their_element_types() {
    let ex = export_code(TUPLE_BINDERS, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    let mut constants: Vec<String> = ex.report["holes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|h| h["constant"].as_str().unwrap().to_string())
        .collect();
    constants.sort();
    assert_eq!(
        constants,
        ["Dom_tuple2_int_bool_v0", "Dom_tuple2_u8_u8_v0", "Dom_tuple2_u8_u8_v1"],
        "{}",
        ex.tla
    );
    assert!(
        ex.tla
            .contains("\\E q \\in ({<<v0__2, v1__2>> : v0__2 \\in BOOLEAN, v1__2 \\in 0..255}) :"),
        "{}",
        ex.tla
    );
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let cfg = format!(
        "{}CONSTANTS\n  Dom_tuple2_u8_u8_v0 = {{0, 1}}\n  Dom_tuple2_u8_u8_v1 = {{1, 2}}\n  \
         Dom_tuple2_int_bool_v0 = {{0, 1}}\n",
        ex.cfg
    );
    let run = tlc(&jar, &ex.spec(), &cfg);
    // x takes 0, 1 (the pair (1, 1)) and 2 (the pair (true, 2)).
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 3, "{run:?}");
}

/// Helpers an invariant calls (`big`, `marked`, under an implication) are
/// checked inside it, not on their own: alone, `big` fails in the initial
/// state. Named on the command line, they are checked as asked.
const INVARIANT_HELPERS: &str = r#"
verus! {
pub struct State { pub x: nat, pub y: nat }

pub open spec fn init(s: State) -> bool { s.x == 0 && s.y == 0 }

pub open spec fn next(pre: State, post: State) -> bool {
    pre.x < 3 && post.x == pre.x + 1 && post.y == pre.y
}

pub open spec fn big(s: State) -> bool { s.x >= 2 }

pub open spec fn marked(s: State) -> bool { s.y == 7 }

pub open spec fn inv(s: State) -> bool { big(s) ==> !marked(s) }

pub open spec fn small(s: State) -> bool { s.x <= 3 }
}
"#;

#[test]
fn tla_export_leaves_out_a_helper_another_invariant_calls() {
    let ex = export_code(INVARIANT_HELPERS, "test_crate");
    assert_eq!(names(&ex.report["invariants"]), ["inv", "small"]);
    assert_eq!(
        candidates(&ex.report),
        [
            ("big".to_string(), false),
            ("marked".to_string(), false),
            ("inv".to_string(), true),
            ("small".to_string(), true)
        ]
    );
    let reason = ex.report["candidates"][0]["reason"].as_str().unwrap();
    assert!(reason.starts_with("called by the invariant test_crate::inv"), "{}", reason);
    assert!(ex.cfg.contains("test_crate::big is not checked on its own"), "{}", ex.cfg);
    let named = export_code(INVARIANT_HELPERS, "test_crate:inv,big");
    assert_eq!(names(&named.report["invariants"]), ["big", "inv"]);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 4, "{run:?}");
    // Alone, `big` fails where x < 2: at x = 0 and x = 1.
    let run = tlc(&jar, &named.spec(), &named.cfg);
    assert_eq!(run.violated, ["big", "big"], "{run:?}");
}

/// `s.x == s.y` in Init assigns whichever field an earlier conjunct left
/// unassigned, and is printed with that one on the left (TLC assigns only
/// from the left): `y = x` once `x` is assigned, `x = y` once `y` is.
const INIT_FIELD_EQUALITY: &str = r#"
verus! {
pub struct State { pub x: nat, pub y: nat, pub z: nat }

pub open spec fn init(s: State) -> bool {
    &&& s.x == 1
    &&& s.x == s.y
    &&& s.z == s.y
}

pub open spec fn next(pre: State, post: State) -> bool {
    pre.x < 3 && post.x == pre.x + 1 && post.y == pre.y && post.z == pre.z
}

pub open spec fn same(s: State) -> bool { s.y == s.z && s.y == 1 }
}
"#;

#[test]
fn tla_export_assigns_an_init_equality_of_two_fields() {
    let ex = export_code(INIT_FIELD_EQUALITY, "test_crate");
    assert_eq!(ex.report["init_unassigned"], serde_json::json!([]), "{}", ex.tla);
    assert!(!ex.cfg.contains("Init never assigns"), "{}", ex.cfg);
    assert!(ex.tla.contains("(y = x)"), "{}", ex.tla);
    assert!(ex.tla.contains("(z = y)"), "{}", ex.tla);
    // With nothing assigned before it, the equality assigns neither.
    let gap = export_code(&INIT_FIELD_EQUALITY.replace("s.x == 1", "true"), "test_crate");
    assert_eq!(gap.report["init_unassigned"], serde_json::json!(["x", "y", "z"]), "{}", gap.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 3, "{run:?}");
}

/// Literal and range patterns are comparisons of the scrutinee.
const LITERAL_PATTERNS: &str = r#"
verus! {
pub struct State { pub k: u8, pub phase: int }

pub open spec fn init(s: State) -> bool { s.k == 0 && s.phase == 0 }

pub open spec fn next(pre: State, post: State) -> bool {
    &&& match pre.k {
        0 => post.k == 1,
        1..=3 => post.k == pre.k + 2,
        _ => post.k == 0,
    }
    &&& post.phase == match post.k {
        0 => 0int,
        1..5 => 1,
        _ => 2,
    }
}

pub open spec fn k_small(s: State) -> bool { s.k <= 5 }

pub open spec fn phase_ok(s: State) -> bool {
    (s.k == 0 ==> s.phase == 0) && (1 <= s.k < 5 ==> s.phase == 1) && (s.k >= 5 ==> s.phase == 2)
}
}
"#;

#[test]
fn tla_export_compares_literal_and_range_patterns() {
    let ex = export_code(LITERAL_PATTERNS, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert!(ex.tla.contains("IF (m__ = 0) THEN"), "{}", ex.tla);
    assert!(ex.tla.contains("((1 <= m__) /\\ (m__ <= 3))"), "{}", ex.tla);
    assert!(ex.tla.contains("((1 <= m__2) /\\ (m__2 < 5))"), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["k_small", "phase_ok"]);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // k: 0 -> 1 -> 3 -> 5 -> 0.
    assert_eq!(run.distinct, 4, "{run:?}");
}

/// A bare or negated bool field at conjunct level is an assignment: `!s.done`
/// in Init is `done = FALSE`, `post.done` and `!post.done` in Next are
/// `done' = TRUE` and `done' = FALSE`. Printed as a bare read, TLC stopped
/// on the unassigned variable.
const BOOL_FIELDS: &str = r#"
verus! {
pub struct State { pub n: nat, pub done: bool, pub busy: bool }

pub open spec fn init(s: State) -> bool { s.n == 0 && !s.done && s.busy }

pub open spec fn finished(s: State) -> bool { s.done }

pub open spec fn next(pre: State, post: State) -> bool {
    &&& pre.n < 3
    &&& post.n == pre.n + 1
    &&& if post.n == 3 { post.done } else { !post.done }
    &&& !post.busy || pre.busy
    &&& post.busy == pre.busy
}

pub open spec fn done_at_three(s: State) -> bool { s.done <==> s.n == 3 }
}
"#;

#[test]
fn tla_export_assigns_a_bare_bool_field() {
    let ex = export_code(BOOL_FIELDS, "test_crate");
    assert_eq!(ex.report["init_unassigned"], serde_json::json!([]), "{}", ex.tla);
    assert!(!ex.cfg.contains("never assigns"), "{}", ex.cfg);
    assert!(ex.tla.contains("(done = FALSE)"), "{}", ex.tla);
    assert!(ex.tla.contains("(busy = TRUE)"), "{}", ex.tla);
    assert!(ex.tla.contains("(done' = TRUE)"), "{}", ex.tla);
    assert!(ex.tla.contains("(done' = FALSE)"), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["finished", "done_at_three"]);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    // `finished` fails wherever n < 3.
    assert_eq!(run.violated, ["finished", "finished", "finished"], "{run:?}\n{}", ex.tla);
    assert_eq!(run.distinct, 4, "{run:?}");
}

/// A helper Init calls is printed once, orienting `s.x == s.y` by its own
/// conjuncts alone (`x = y`), so it does not assign `y` after the caller
/// assigned `x`. `y` is a `u8`, so Init draws it from `0..255` and `init`
/// keeps the one value `x = y` allows; the report says so.
const INIT_HELPER_EQUALITY: &str = r#"
verus! {
pub struct State { pub x: u8, pub y: u8 }

pub open spec fn same(s: State) -> bool { s.x == s.y }

pub open spec fn init(s: State) -> bool { s.x == 0 && same(s) }

pub open spec fn next(pre: State, post: State) -> bool {
    pre.x < 3 && post.x == pre.x + 1 && post.y == pre.y
}

pub open spec fn small(s: State) -> bool { s.x < 9 }
}
"#;

#[test]
fn tla_export_reads_an_init_helper_as_it_is_printed() {
    let ex = export_code(INIT_HELPER_EQUALITY, "test_crate");
    assert!(ex.tla.contains("same ==\n    (x = y)"), "{}", ex.tla);
    assert_eq!(ex.report["init_unassigned"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(
        ex.report["init_enumerated"],
        serde_json::json!([{"variable": "y", "domain": "0..255"}])
    );
    assert!(ex.tla.contains("Init == (y \\in 0..255) /\\ init /\\ TypeOK\n"), "{}", ex.tla);
    assert!(!ex.cfg.contains("Init never assigns"), "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    // One initial state, x = y = 0, and x counts to 3.
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.distinct, 4, "{run:?}\n{}", ex.tla);
}

/// A helper is checked inside its caller only when that caller is in the
/// .cfg: `inv` reaches a refusal (`choose`) and is left out, so `small`,
/// which it calls, is checked on its own (and fails at x = 3, 4, 5).
const HELPER_OF_A_REFUSED_INVARIANT: &str = r#"
verus! {
pub struct State { pub x: u8 }

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn next(pre: State, post: State) -> bool { pre.x < 5 && post.x == pre.x + 1 }

pub open spec fn small(s: State) -> bool { s.x < 3 }

pub open spec fn id(y: u8) -> u8 { y }

pub open spec fn weird(s: State) -> bool { s.x == choose|y: u8| #[trigger] id(y) == s.x }

pub open spec fn inv(s: State) -> bool { small(s) && weird(s) }
}
"#;

#[test]
fn tla_export_checks_a_helper_whose_caller_is_left_out() {
    let ex = export_code(HELPER_OF_A_REFUSED_INVARIANT, "test_crate");
    // `weird` reaches the refusal too; `small` is checked.
    assert_eq!(names(&ex.report["skipped_invariants"]), ["weird", "inv"]);
    assert_eq!(names(&ex.report["invariants"]), ["small"]);
    assert_eq!(
        candidates(&ex.report),
        [("small".to_string(), true), ("weird".to_string(), false), ("inv".to_string(), false)]
    );
    assert!(!ex.cfg.contains("not checked on its own"), "{}", ex.cfg);
    assert!(ex.cfg.contains("INVARIANTS\n  small\n"), "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, ["small", "small", "small"], "{run:?}");
}

/// A datatype of one variant without fields has one value, the record the
/// export prints for it (`[tag |-> "unit"]`), so a binder over it is
/// enumerated rather than a hole.
const ONE_VALUE_STEP: &str = r#"
verus! {
pub struct State { pub x: u8 }

pub enum Step { Tick }

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn step(pre: State, post: State, st: Step) -> bool {
    match st { Step::Tick => pre.x < 5 && post.x == pre.x + 1 }
}

pub open spec fn next(pre: State, post: State) -> bool {
    exists|st: Step| step(pre, post, st) && st == Step::Tick
}

pub open spec fn small(s: State) -> bool { s.x < 9 }
}
"#;

#[test]
fn tla_export_enumerates_a_datatype_of_one_value() {
    let ex = export_code(ONE_VALUE_STEP, "test_crate");
    assert_eq!(ex.report["holes"], serde_json::json!([]), "{}", ex.tla);
    assert!(!ex.tla.contains("CONSTANTS"), "{}", ex.tla);
    assert!(ex.tla.contains("\\E st \\in {[tag |-> \"unit\"]}"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // x in 0..5.
    assert_eq!(run.distinct, 6, "{run:?}");
}

/// A collection's values are TLA+ sequences, sets and functions, so a
/// domain read off its type is never built from its Rust representation (a
/// `Seq` was nested `SeqInner` records, a `Set` or `Map`, opaque in VIR,
/// the one value `[tag |-> "unit"]`): a `Seq` or `Map` is a hole named after
/// its type (per field in a step variant), a `Set` of a small element domain
/// its subsets (`SUBSET BOOLEAN`), and a larger `Set` a hole.
const COLLECTION_DOMAINS: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub log: Seq<u8>, pub u: Set<u8>, pub m: Map<int, bool>, pub b: Set<bool> }

pub enum Step { Put(Seq<u8>), Add(Set<u8>), Store(Map<int, bool>), Flags(Set<bool>) }

pub open spec fn init(s: State) -> bool {
    &&& s.log == Seq::<u8>::empty()
    &&& s.u == Set::<u8>::empty()
    &&& s.m == Map::<int, bool>::empty()
    &&& s.b == Set::<bool>::empty()
}

pub open spec fn step(pre: State, post: State, st: Step) -> bool {
    match st {
        Step::Put(x) => x.len() == 1 && pre.log.len() < 2 && post.log == pre.log + x
            && post.u == pre.u && post.m == pre.m && post.b == pre.b,
        Step::Add(x) => post.u == pre.u.union(x)
            && post.log == pre.log && post.m == pre.m && post.b == pre.b,
        Step::Store(x) => post.m == x && post.log == pre.log && post.u == pre.u && post.b == pre.b,
        Step::Flags(x) => post.b == x && post.log == pre.log && post.u == pre.u && post.m == pre.m,
    }
}

pub open spec fn next(pre: State, post: State) -> bool { exists|st: Step| step(pre, post, st) }

// Violated: Add can insert 3.
pub open spec fn no3(s: State) -> bool { !s.u.contains(3u8) }

pub open spec fn m_ok(s: State) -> bool { s.m.dom().contains(1) ==> s.m[1] }

pub open spec fn log_short(s: State) -> bool { s.log.len() <= 2 }

pub open spec fn b_small(s: State) -> bool {
    forall|t: Set<bool>| #[trigger] t.subset_of(s.b) ==> t.len() <= 2
}

pub open spec fn log_other(s: State) -> bool {
    forall|q: Seq<u8>| #[trigger] q.len() > 5 ==> q != s.log
}
}
"#;

#[test]
fn tla_export_bounds_collections_by_holes_or_subsets() {
    let ex = export_code(COLLECTION_DOMAINS, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    let mut holes: Vec<(String, String)> = ex.report["holes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|h| (h["constant"].as_str().unwrap().into(), h["typ"].as_str().unwrap().into()))
        .collect();
    holes.sort();
    let expected = [
        ("Dom_Seq_u8", "Seq_u8"),
        ("Dom_Step_Add_v0", "Set_u8"),
        ("Dom_Step_Put_v0", "Seq_u8"),
        ("Dom_Step_Store_v0", "Map_int_bool"),
    ];
    let expected: Vec<(String, String)> =
        expected.iter().map(|(c, t)| (c.to_string(), t.to_string())).collect();
    assert_eq!(holes, expected, "{}", ex.tla);
    assert!(!ex.tla.contains("tag |-> \"unit\""), "{}", ex.tla);
    assert!(!ex.tla.contains("SeqInner"), "{}", ex.tla);
    assert!(ex.tla.contains("(SUBSET BOOLEAN)"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let mc = ex.spec().with_file_name("MC.tla");
    std::fs::write(
        &mc,
        format!(
            "---- MODULE MC ----\nEXTENDS {}\n\
             MC_put == {{<<1>>, <<2>>}}\n\
             MC_add == {{{{}}, {{3}}}}\n\
             MC_store == {{[k \\in {{}} |-> k], 1 :> TRUE}}\n\
             MC_seq == {{<< >>, <<7>>}}\n====\n",
            ex.module
        ),
    )
    .unwrap();
    let cfg = format!(
        "{}CONSTANTS\n  Dom_Step_Put_v0 <- MC_put\n  Dom_Step_Add_v0 <- MC_add\n  \
         Dom_Step_Store_v0 <- MC_store\n  Dom_Seq_u8 <- MC_seq\n",
        ex.cfg
    );
    let run = tlc(&jar, &mc, &cfg);
    assert!(!run.violated.is_empty(), "{run:?}\n{}", ex.tla);
    assert!(run.violated.iter().all(|v| v == "no3"), "{run:?}\n{}", ex.tla);
    // 7 logs (length at most 2 over {1, 2}) x 2 sets u x 2 maps x 4 sets b.
    assert_eq!(run.distinct, 112, "{run:?}\n{}", ex.tla);
}

/// A `Map` whose keys and values have small domains is bounded as the
/// functions from a subset of its keys to its values, in a binder's domain;
/// a larger one is a hole. TypeOK bounds a map's keys and values, never
/// with this domain.
const MAP_DOMAINS: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub m: Map<bool, bool>, pub big: Map<u8, bool> }

pub open spec fn init(s: State) -> bool {
    &&& s.m == Map::<bool, bool>::empty()
    &&& s.big == Map::<u8, bool>::empty()
}

pub open spec fn next(pre: State, post: State) -> bool {
    ||| post.m == pre.m.insert(true, false) && post.big == pre.big
    ||| post.big == pre.big.insert(1u8, true) && post.m == pre.m
}

pub open spec fn m_small(s: State) -> bool {
    forall|t: Map<bool, bool>| #[trigger] t.dom().contains(false) ==> t != s.m
}

pub open spec fn big_no3(s: State) -> bool {
    forall|t: Map<u8, bool>| #[trigger] t.dom().contains(3u8) ==> t != s.big
}
}
"#;

#[test]
fn tla_export_bounds_a_small_map_and_leaves_a_large_one_a_hole() {
    let ex = export_code(MAP_DOMAINS, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert!(
        ex.tla.contains(
            "(\\A t \\in UNION {[d__ -> BOOLEAN] : d__ \\in SUBSET BOOLEAN} : ((FALSE \\in DOMAIN t) => ~((m = t))))"
        ),
        "{}",
        ex.tla
    );
    assert!(ex.tla.contains("(\\A t \\in Dom_Map_u8_bool : "), "{}", ex.tla);
    let holes: Vec<(&str, &str)> = ex.report["holes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|h| (h["constant"].as_str().unwrap(), h["typ"].as_str().unwrap()))
        .collect();
    assert_eq!(holes, [("Dom_Map_u8_bool", "Map_u8_bool")], "{}", ex.tla);
    // TypeOK bounds `big`'s u8 keys and says nothing of either map's domain.
    assert!(
        ex.tla.contains(
            "TypeOK ==\n    /\\ (\\A k__2 \\in DOMAIN big : (0 <= k__2 /\\ k__2 <= 255))\nInit =="
        ),
        "{}",
        ex.tla
    );
    assert!(!ex.tla.contains("m \\in UNION"), "{}", ex.tla);
    assert!(!ex.tla.contains("big \\in"), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["m_small", "big_no3"]);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let mc = ex.spec().with_file_name("MC.tla");
    std::fs::write(
        &mc,
        format!(
            "---- MODULE MC ----\nEXTENDS {}\n\
             MC_big == {{[k \\in {{}} |-> TRUE], 1 :> TRUE, 3 :> TRUE}}\n====\n",
            ex.module
        ),
    )
    .unwrap();
    let cfg = format!("{}CONSTANTS\n  Dom_Map_u8_bool <- MC_big\n", ex.cfg);
    let run = tlc(&jar, &mc, &cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{run:?}\n{}", ex.tla);
    // m is empty or {TRUE: FALSE}, big empty or {1: TRUE}.
    assert_eq!(run.distinct, 4, "{run:?}\n{}", ex.tla);
}

/// An or-pattern that binds nothing is the disjunction of its
/// alternatives' conditions (it was refused, which stopped TLC at the
/// first step of a `match` on the step).
const OR_PATTERNS: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub n: nat, pub k: nat }

pub enum Step { A, B, C(u8), D }

pub open spec fn init(s: State) -> bool { s.n == 0 && s.k == 0 }

pub open spec fn next(pre: State, post: State) -> bool {
    exists|st: Step| match st {
        Step::A | Step::B => pre.n < 3 && post.n == pre.n + 1 && post.k == pre.k,
        Step::C(1) | Step::C(2) => pre.k < 2 && post.k == pre.k + 1 && post.n == pre.n,
        _ => post == pre,
    }
}

pub open spec fn bounded(s: State) -> bool { s.n <= 3 && s.k <= 2 }
}
"#;

#[test]
fn tla_export_prints_an_or_pattern_as_a_disjunction() {
    let ex = export_code(OR_PATTERNS, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(ex.report["holes"], serde_json::json!([]), "{}", ex.tla);
    assert!(ex.tla.contains("((m__.tag = \"A\") \\/ (m__.tag = \"B\"))"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // n in 0..3 and k in 0..2.
    assert_eq!(run.distinct, 12, "{run:?}\n{}", ex.tla);
}

/// An Init equality of two fields after a helper that assigns one of them:
/// the helper's assignment counts, so the other field goes on the left and
/// the print agrees with the report (it was printed `x = y`, which TLC
/// cannot evaluate, while the report said everything was assigned).
const INIT_HELPER_THEN_EQUALITY: &str = r#"
verus! {
pub struct State { pub x: int, pub y: int, pub done: bool }

pub open spec fn x_zero(s: State) -> bool { s.x == 0 && !s.done }

pub open spec fn init(s: State) -> bool { x_zero(s) && s.x == s.y }

pub open spec fn next(pre: State, post: State) -> bool {
    &&& pre.x < 2
    &&& post.x == pre.x + 1
    &&& post.y == pre.y
    &&& post.done == pre.done
}

pub open spec fn y_zero(s: State) -> bool { s.y == 0 }
}
"#;

#[test]
fn tla_export_counts_what_an_init_helper_assigns() {
    let ex = export_code(INIT_HELPER_THEN_EQUALITY, "test_crate");
    assert_eq!(ex.report["init_unassigned"], serde_json::json!([]), "{}", ex.tla);
    assert!(ex.tla.contains("(x_zero /\\ (y = x))"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // x in 0..2, y and done fixed.
    assert_eq!(run.distinct, 3, "{run:?}\n{}", ex.tla);
}

/// TLC has no reals and rejects a module holding one outright, so a real
/// literal and a conversion between int and real are refused where they
/// occur (they were printed as a decimal and the identity).
const REALS: &str = r#"
verus! {
pub struct State { pub x: int }

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn next(pre: State, post: State) -> bool { pre.x < 2 && post.x == pre.x + 1 }

pub open spec fn small(s: State) -> bool { s.x <= 2 }

pub open spec fn real_small(s: State) -> bool { (s.x as real) < 2.5real }
}
"#;

#[test]
fn tla_export_refuses_reals() {
    let ex = export_code(REALS, "test_crate");
    let whats: Vec<String> = ex.report["refusals"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r["what"].as_str().unwrap().to_string())
        .collect();
    assert!(whats.iter().any(|w| w == "real literal"), "{:?}", whats);
    assert!(whats.iter().any(|w| w == "conversion between int and real"), "{:?}", whats);
    assert_eq!(names(&ex.report["skipped_invariants"]), ["real_small"]);
    assert_eq!(names(&ex.report["invariants"]), ["small"]);
    assert!(!ex.tla.contains("2.5"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 3, "{run:?}\n{}", ex.tla);
}

/// The shapes toyDB's Raft model (`src/raft/safety.rs`) writes, which the
/// export of it against the hand-written `tla/Raft.tla` turned up: a node set
/// `Set::range(0, n)` (refused as an uninterpreted trait method); a
/// quantifier guarded by `net.contains(Msg::Ping { from, round })` (a hole
/// per binder); `b == 0 || log[b - 1] < 1` in a transition (TLC branches on
/// the `\/` and indexes `log[-1]`); and `exists|step: Step|` whose arms call
/// one transition each (a hole per field, and the union of every variant's
/// values built in every state). 144 states, as a breadth-first search of
/// the same system finds.
const MESSAGES: &str = r#"
use vstd::prelude::*;
verus! {
pub enum Msg { Ping { from: int, round: nat }, Note { log: Seq<int> } }

pub struct State { pub n: nat, pub net: Set<Msg>, pub log: Seq<int> }

pub open spec fn nodes(n: nat) -> Set<int> { Set::<int>::range(0, n as int) }

pub open spec fn init(s: State) -> bool {
    &&& s.n == 2
    &&& s.net == Set::<Msg>::empty()
    &&& s.log == Seq::<int>::empty()
}

pub open spec fn ping(pre: State, post: State, from: int, round: nat) -> bool {
    &&& nodes(pre.n).contains(from)
    &&& round < 2
    &&& post == State { net: pre.net.insert(Msg::Ping { from, round }), ..pre }
}

pub open spec fn extend(pre: State, post: State, b: nat) -> bool {
    &&& b <= pre.log.len() < 2
    &&& (b == 0 || pre.log[b - 1] < 1)
    &&& post == State { log: pre.log.push(b as int), ..pre }
}

pub open spec fn echo(pre: State, post: State, from: int, round: nat) -> bool {
    &&& pre.net.contains(Msg::Ping { from, round })
    &&& pre.log.len() < 2
    &&& post == State { log: pre.log.push(from + round), ..pre }
}

pub enum Step { Ping { from: int, round: nat }, Extend { b: nat }, Echo { from: int, round: nat } }

pub open spec fn next_step(pre: State, post: State, step: Step) -> bool {
    match step {
        Step::Ping { from, round } => ping(pre, post, from, round),
        Step::Extend { b } => extend(pre, post, b),
        Step::Echo { from, round } => echo(pre, post, from, round),
    }
}

pub open spec fn next(pre: State, post: State) -> bool {
    exists|step: Step| next_step(pre, post, step)
}

pub open spec fn pings_ok(s: State) -> bool {
    forall|from: int, round: nat| #[trigger] s.net.contains(Msg::Ping { from, round })
        ==> nodes(s.n).contains(from) && round < 2
}

pub open spec fn log_small(s: State) -> bool {
    forall|i: int| 0 <= i < s.log.len() ==> 0 <= #[trigger] s.log[i] <= 2
}
}
"#;

#[test]
fn tla_export_bounds_message_fields_and_step_fields_from_their_guards() {
    let ex = export_code(MESSAGES, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(ex.report["holes"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["pings_ok", "log_small"]);
    // The node set is a range.
    assert!(ex.tla.contains("(0)..((n_2) - 1)"), "{}", ex.tla);
    // A message field ranges over the fields of the messages in `net`.
    assert!(ex.tla.contains(".from : m__"), "{}", ex.tla);
    assert!(ex.tla.contains(".tag = \"Ping\"}}"), "{}", ex.tla);
    // The guarding disjunction is evaluated, not branched on.
    assert!(ex.tla.contains("(IF (b = 0) THEN TRUE ELSE"), "{}", ex.tla);
    // One \E per variant, over fields bounded by the transition's guard.
    assert!(ex.tla.contains("(LET step == [tag |-> \"Extend\", b |-> b__] IN next_step(step))"));
    assert!(!ex.tla.contains("\\cup {[tag |-> \"Extend\""), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 144, "{run:?}\n{}", ex.tla);
}

/// Step fields are bounded from the guard of the arm a variant's values
/// take, and only when that arm takes all of them: the first arm that could
/// match the variant, unguarded, and binding each field plainly. Here an arm
/// refuting a field (`R { a: true, b }`), a guarded arm (`G { b } if b > 0`)
/// and a guarded wildcard each leave some values to a later arm, whose
/// guard (`b < 1`, `b < 0`) would drop `x = 21, 22, 31, 32, 50`. The nine
/// states are 0 and the eight values the arms reach (`t60` is unreachable).
const ARMS: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: int }

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn t10(pre: State, post: State, b: u8) -> bool {
    &&& b < 1 &&& pre.x == 0 &&& post == State { x: 10 + b }
}
pub open spec fn t20(pre: State, post: State, b: u8) -> bool {
    &&& b < 3 &&& pre.x == 0 &&& post == State { x: 20 + b }
}
pub open spec fn t30(pre: State, post: State, b: u8) -> bool {
    &&& b < 3 &&& pre.x == 0 &&& post == State { x: 30 + b }
}
pub open spec fn t40(pre: State, post: State, b: u8) -> bool {
    &&& b < 1 &&& pre.x == 0 &&& post == State { x: 40 + b }
}
pub open spec fn t60(pre: State, post: State, b: u8) -> bool {
    &&& b < 0 &&& pre.x == 0 &&& post == State { x: 60 + b }
}

pub enum Step { R { a: bool, b: u8 }, G { b: u8 }, W { b: u8 } }

pub open spec fn next_step(pre: State, post: State, step: Step) -> bool {
    match step {
        Step::R { a: true, b } => t10(pre, post, b),
        Step::R { a, b } => t20(pre, post, b),
        Step::G { b } if b > 0 => t30(pre, post, b),
        Step::G { b } => t40(pre, post, b),
        _ if step is W => pre.x == 0 && post == State { x: 50 },
        Step::W { b } => t60(pre, post, b),
    }
}

pub open spec fn next(pre: State, post: State) -> bool {
    exists|step: Step| next_step(pre, post, step)
}

pub open spec fn small(s: State) -> bool { s.x <= 60 }
}
"#;

#[test]
fn tla_export_bounds_a_step_field_only_from_an_arm_taking_every_value() {
    let ex = export_code(ARMS, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(ex.report["holes"], serde_json::json!([]), "{}", ex.tla);
    // Each variant's `b` is read off its type: no arm bounds it alone.
    assert!(!ex.tla.contains("\\in 0..(1) - 1"), "{}", ex.tla);
    assert!(!ex.tla.contains("\\in 0..(0) - 1"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 9, "{run:?}\n{}", ex.tla);
}

/// A disjunction Init reaches keeps its `\/`, which TLC branches on to
/// assign the state (two initial states), while the same disjunction in an
/// action is evaluated. `Set::range_inclusive(lo, hi)` holds `hi` even below
/// `lo`, as vstd's `range_set(lo, hi).insert(hi)` does.
const INIT_OR: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: int, pub y: int }

pub open spec fn init(s: State) -> bool {
    &&& s.x == 0 || s.x == 1
    &&& s.y == 0
}

pub open spec fn next(pre: State, post: State) -> bool {
    &&& pre.x == 0 || pre.x == 5
    &&& pre.y < 1
    &&& post == State { y: pre.y + 1, ..pre }
}

pub open spec fn inclusive(s: State) -> bool {
    &&& Set::<int>::range_inclusive(3, 1).contains(1)
    &&& !Set::<int>::range_inclusive(3, 1).contains(3)
    &&& Set::<int>::range_inclusive(0, s.y).contains(s.y)
}
}
"#;

#[test]
fn tla_export_keeps_a_disjunction_init_reaches() {
    let ex = export_code(INIT_OR, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(ex.report["holes"], serde_json::json!([]), "{}", ex.tla);
    assert!(ex.tla.contains("(x = 0) \\/ (x = 1)"), "{}", ex.tla);
    assert!(ex.tla.contains("(IF (x = 0) THEN TRUE ELSE (x = 5))"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let out = tlc_output(&jar, &ex.spec(), &ex.cfg);
    assert!(out.contains("2 distinct states generated"), "{}", out);
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // (0, 0), (1, 0) and (0, 1): the `x = 1` state takes no step.
    assert_eq!(run.distinct, 3, "{run:?}\n{}", ex.tla);
}

/// A binder that is a field of a constructor in a membership guard ranges
/// over that field of the members, through a nested constructor (with a
/// tag test at each level of several variants), a tuple, and a map's keys.
/// `wrong` holds of no member, so TLC must find it violated: the bound is
/// not empty.
const CTOR_FIELDS: &str = r#"
use vstd::prelude::*;
verus! {
pub enum Inner { A { v: int }, B }
pub enum Msg { Wrap { inner: Inner, t: (int, int) }, Other }

pub struct State { pub net: Set<Msg>, pub m: Map<Msg, bool>, pub k: int }

pub open spec fn init(s: State) -> bool {
    &&& s.net == Set::<Msg>::empty().insert(Msg::Wrap { inner: Inner::A { v: 1 }, t: (2, 3) })
        .insert(Msg::Wrap { inner: Inner::B, t: (7, 7) }).insert(Msg::Other)
    &&& s.m == Map::<Msg, bool>::empty().insert(Msg::Wrap { inner: Inner::A { v: 4 }, t: (5, 6) }, true)
    &&& s.k == 0
}

pub open spec fn next(pre: State, post: State) -> bool {
    &&& pre.k < 2
    &&& post == State { k: pre.k + 1, ..pre }
}

pub open spec fn nested(s: State) -> bool {
    forall|v: int, a: int, b: int| #[trigger] s.net.contains(Msg::Wrap { inner: Inner::A { v }, t: (a, b) })
        ==> v == 1 && a == 2 && b == 3
}

pub open spec fn keyed(s: State) -> bool {
    forall|v: int, a: int, b: int| #[trigger] s.m.contains_key(Msg::Wrap { inner: Inner::A { v }, t: (a, b) })
        ==> v == 4 && a + b == 11
}

pub open spec fn wrong(s: State) -> bool {
    forall|v: int, a: int, b: int| #[trigger] s.net.contains(Msg::Wrap { inner: Inner::A { v }, t: (a, b) })
        ==> v != 1
}
}
"#;

#[test]
fn tla_export_bounds_a_nested_tuple_and_map_key_constructor_field() {
    let ex = export_code(CTOR_FIELDS, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(ex.report["holes"], serde_json::json!([]), "{}", ex.tla);
    assert!(ex.tla.contains(".inner.tag = \"A\""), "{}", ex.tla);
    assert!(ex.tla.contains(".inner.v : m__"), "{}", ex.tla);
    assert!(ex.tla.contains(".t[2] : m__"), "{}", ex.tla);
    assert!(ex.tla.contains("\\in DOMAIN m : "), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    // In each of the three states (`-continue`).
    assert_eq!(run.violated, ["wrong", "wrong", "wrong"], "{}", ex.tla);
    assert_eq!(run.distinct, 3, "{run:?}\n{}", ex.tla);
}

/// A disjunction over a value read in the post state keeps its `\/`, whose
/// branches TLC assigns the primed variable from: through a helper given
/// `post.x` (its own operator, whose parameter reads the post state), a
/// `let` bound to `post.z`, and a match on `post.o`. The same helper given a
/// pre-state value is evaluated. Nine states: the initial one, then two
/// values of `x` and two of `z` after each of the two steps.
const PRIMED_OR: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: int, pub y: int, pub z: int, pub o: Option<int> }

pub open spec fn init(s: State) -> bool {
    &&& s.x == 0 &&& s.y == 0 &&& s.z == 0 &&& s.o == Option::<int>::None
}

pub open spec fn pick(v: int) -> bool { v == 0 || v == 1 }

pub open spec fn next(pre: State, post: State) -> bool {
    &&& pre.y < 2
    &&& pick(pre.x)
    &&& post.y == pre.y + 1
    &&& post.o == Option::<int>::Some(pre.y)
    &&& pick(post.x)
    &&& { let h = post.z; h == 0 || h == 2 }
    &&& match post.o { Option::Some(v) => v == 0 || v >= 1, Option::None => false }
}

pub open spec fn small(s: State) -> bool { s.x <= 1 && s.z <= 2 }
}
"#;

#[test]
fn tla_export_keeps_a_disjunction_over_the_post_state() {
    let ex = export_code(PRIMED_OR, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(ex.report["holes"], serde_json::json!([]), "{}", ex.tla);
    assert!(ex.tla.contains("pick(v) ==\n    (IF (v = 0) THEN TRUE ELSE (v = 1))"), "{}", ex.tla);
    assert!(ex.tla.contains("pick_postarg(v) ==\n    ((v = 0) \\/ (v = 1))"), "{}", ex.tla);
    assert!(ex.tla.contains("pick(x)"), "{}", ex.tla);
    assert!(ex.tla.contains("pick_postarg(x')"), "{}", ex.tla);
    assert!(ex.tla.contains("((h = 0) \\/ (h = 2))"), "{}", ex.tla);
    assert!(ex.tla.contains("((v = 0) \\/ (v >= 1))"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 9, "{run:?}\n{}", ex.tla);
}

/// A closure, or a record of closures, that captures the post state reads
/// it: a disjunction of its applications keeps its `\/`, whose branches
/// assign `x'`. From `y = 0` the steps take `x` to `y` or `y + 10`.
const CLOSURE_OR: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: int, pub y: int }

pub struct Pair { pub f: spec_fn(int) -> bool }

pub open spec fn init(s: State) -> bool { s.x == 0 && s.y == 0 }

pub open spec fn next(pre: State, post: State) -> bool {
    let f = |v: int| post.x == v;
    let p = Pair { f: |v: int| post.x == v };
    &&& pre.y < 3
    &&& post.y == pre.y + 1
    &&& (f(pre.y) || f(pre.y + 10))
    &&& ((p.f)(pre.y) || (p.f)(pre.y + 10))
}

pub open spec fn small(s: State) -> bool { s.y <= 3 }
}
"#;

#[test]
fn tla_export_keeps_a_disjunction_over_a_closure_reading_the_post_state() {
    let ex = export_code(CLOSURE_OR, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(ex.report["holes"], serde_json::json!([]), "{}", ex.tla);
    assert!(!ex.tla.contains("IF (LET"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    // (0,0); then x in {y, y+10} for y = 1..3 after each step: 1 + 2 + 2 + 2.
    assert_eq!(run.distinct, 7, "{run:?}\n{}", ex.tla);
}

/// A step field whose guard reads the step value itself (`b < size(step)`)
/// is not bounded from it: the domain sits outside the `LET` binding the
/// step. It is bounded by its type (`u8`) instead, in the callee's match and
/// in a match written inline in the `exists`. `x` runs 0..6.
const STEP_GUARD: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: int }

pub enum Step { A { b: u8 }, B { c: int } }

pub open spec fn size(s: Step) -> int { match s { Step::A { .. } => 3, Step::B { .. } => 2 } }

pub open spec fn init(s: State) -> bool { s.x == 0 }

pub open spec fn next_step(pre: State, post: State, step: Step) -> bool {
    match step {
        Step::A { b } => b < size(step) && pre.x < 5 && post.x == pre.x + b,
        Step::B { c } => 0 <= c < 2 && pre.x < 5 && post.x == pre.x + c,
    }
}

pub open spec fn next(pre: State, post: State) -> bool {
    ||| exists|step: Step| next_step(pre, post, step)
    ||| exists|st: Step| #![trigger size(st)] match st {
        Step::A { b } => b < size(st) && pre.x < 4 && post.x == pre.x + b,
        Step::B { c } => 0 <= c < 2 && pre.x < 4 && post.x == pre.x + c,
    }
}

pub open spec fn small(s: State) -> bool { s.x <= 6 }
}
"#;

#[test]
fn tla_export_bounds_a_step_field_whose_guard_reads_the_step() {
    let ex = export_code(STEP_GUARD, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(ex.report["holes"], serde_json::json!([]), "{}", ex.tla);
    assert!(!ex.tla.contains("(size(step)) - 1"), "{}", ex.tla);
    assert!(!ex.tla.contains("(size(st)) - 1"), "{}", ex.tla);
    assert!(ex.tla.contains("\\E b__ \\in 0..255 : (LET step =="), "{}", ex.tla);
    assert!(ex.tla.contains("\\in 0..255 : (LET st =="), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 7, "{run:?}\n{}", ex.tla);
}

/// The trace spec written beside an export, read back.
fn trace_spec(ex: &Exported) -> (PathBuf, String, String) {
    let module = format!("{}_trace", ex.module);
    let spec = ex.dir.path().join("log").join(format!("{module}.tla"));
    let tla = std::fs::read_to_string(&spec).expect("the trace spec");
    let cfg = std::fs::read_to_string(spec.with_extension("cfg")).expect("the trace .cfg");
    (spec, tla, cfg)
}

/// TLC on the trace spec over `log`, which it is to stop at with an error
/// (an `Assert` of the trace spec's, or one of TLC's own): its output.
fn stops(jar: &str, spec: &Path, cfg: &str, log: &Path, extra: &str) -> String {
    let cfg = cfg.replace("\"trace.ndjson\"", &format!("\"{}\"", log.display()));
    let out = tlc_output_with(jar, spec, &format!("{cfg}{extra}"), &[]);
    assert!(out.contains("Error:"), "TLC followed {}:\n{out}", log.display());
    out
}

/// TLC on the trace spec over `log`: the depth it reached (the logged steps
/// followed, plus one) and its output, with `extra` appended to the .cfg.
fn follow(jar: &str, spec: &Path, cfg: &str, log: &Path, extra: &str) -> (u64, String) {
    let cfg = cfg.replace("\"trace.ndjson\"", &format!("\"{}\"", log.display()));
    let out = tlc_output_with(jar, spec, &format!("{cfg}{extra}"), &[]);
    assert!(!out.contains("Error:"), "TLC failed on {}:\n{out}", log.display());
    let re = regex::Regex::new(r"The depth of the complete state graph search is (\d+)").unwrap();
    let depth = re.captures(&out).unwrap_or_else(|| panic!("TLC did not finish:\n{}", out))[1]
        .parse()
        .unwrap();
    (depth, out)
}

#[test]
fn tla_export_trace_spec_follows_a_counter_log() {
    let ex = export(&fixture("counter.rs"), "test_crate");
    let trace = &ex.report["trace"];
    assert_eq!(trace["module"], "State_tla_trace");
    assert_eq!(trace["index_variable"], "trace_i");
    assert_eq!(names(&trace["observables"]), ["x", "y"]);
    // `next_step`, which dispatches on the `Step` enum, is a step too (every
    // operator Next reaches through branches is).
    assert_eq!(
        trace["steps"],
        serde_json::json!([
            {"step": "next_step", "function": "test_crate::next_step", "operator": "next_step",
             "short_name_shared": false,
             "params": [{"name": "step", "typ": "Step",
                         "domain": "({[tag |-> \"Inc\"]} \\cup {[tag |-> \"Dbl\"]})"}],
             "enumerated": true},
            {"step": "t_dbl", "function": "test_crate::t_dbl", "operator": "t_dbl",
             "short_name_shared": false, "params": [], "enumerated": true},
            {"step": "t_inc", "function": "test_crate::t_inc", "operator": "t_inc",
             "short_name_shared": false, "params": [], "enumerated": true},
        ])
    );
    let (spec, tla, cfg) = trace_spec(&ex);
    assert!(tla.starts_with("---- MODULE State_tla_trace ----\n"), "{}", tla);
    assert!(tla.contains("EXTENDS State_tla, Json, TLC, Integers, Sequences\n"), "{}", tla);
    // Only ever narrows Next: the logged step is conjoined with it, after
    // it, so the step reads the successor Next assigns.
    assert!(tla.contains("           /\\ Next\n           /\\ TraceStep(e)\n"), "{}", tla);
    assert!(cfg.contains("INIT TraceInit\nNEXT TraceNext\n"), "{}", cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    let logs = std::fs::canonicalize(fixture("counter_trace_ok.ndjson")).unwrap();
    // Five steps: the conforming log is followed to its end.
    let (depth, _) = follow(&jar, &spec, &cfg, &logs, "");
    assert_eq!(depth, 6);
    // The fourth step is t_dbl where the counter took t_inc (x goes 2 to 3):
    // TLC stops there, with t_dbl enabled but its x not the logged one.
    let bad = std::fs::canonicalize(fixture("counter_trace_bad.ndjson")).unwrap();
    let probe = "\nINVARIANT Probe\n";
    let spec_probe = spec.with_file_name("Probe_trace.tla");
    std::fs::write(
        &spec_probe,
        tla.replace("MODULE State_tla_trace", "MODULE Probe_trace").replace(
            "\n=====",
            "\nProbe == trace_i = 4 => PrintT(<<\"probe\", TraceStepAt.step, TraceEnabled, TraceDiagnosis>>)\n=====",
        ),
    )
    .unwrap();
    let (depth, out) = follow(&jar, &spec_probe, &cfg, &bad, probe);
    assert_eq!(depth, 4, "{out}");
    assert!(
        out.contains(
            "<<\"probe\", \"t_dbl\", {[step |-> \"t_dbl\"], [step |-> \"t_inc\"], [params |-> [step |-> [tag |-> \"Inc\"]], step |-> \"next_step\"], [params |-> [step |-> [tag |-> \"Dbl\"]], step |-> \"next_step\"]}, [step_enabled |-> TRUE, unmatched |-> {\"x\"}]>>"
        ), "{}", out);
}

#[test]
fn tla_export_trace_spec_decodes_collections_and_parameters() {
    let ex = export_code(
        r#"
use vstd::prelude::*;
verus! {
pub enum Mode { Off, On(u8) }
pub enum Ev { Lo(u8), Hi(u8, bool) }
pub struct Rec { pub a: nat, pub ghost_b: int }
pub struct State {
    pub s: Seq<Rec>, pub set: Set<u8>, pub m: Map<u8, bool>, pub o: Option<int>, pub mode: Mode,
    pub mr: Map<u8, Rec>, pub ev: Ev,
}
pub open spec fn init(s: State) -> bool {
    &&& s.s == Seq::<Rec>::empty() &&& s.set == Set::<u8>::empty() &&& s.m == Map::<u8, bool>::empty()
    &&& s.o is None &&& s.mode == Mode::Off
    &&& s.mr == Map::<u8, Rec>::empty() &&& s.ev == Ev::Lo(0)
}
pub open spec fn t_add(pre: State, post: State, k: u8, g: bool) -> bool {
    &&& k < 3
    &&& post.s == pre.s.push(Rec { a: k as nat, ghost_b: if g { 1 } else { 0 } })
    &&& post.set == pre.set.insert(k)
    &&& post.m == pre.m.insert(k, g)
    &&& post.o == Some(k as int)
    &&& post.mode == Mode::On(k)
    &&& post.mr == pre.mr.insert(k, Rec { a: k as nat, ghost_b: if g { 1 } else { 0 } })
    &&& post.ev == if g { Ev::Hi(k, g) } else { Ev::Lo(k) }
}
pub open spec fn next(pre: State, post: State) -> bool {
    exists|k: u8, g: bool| t_add(pre, post, k, g)
}
}
"#,
        "test_crate",
    );
    let steps = &ex.report["trace"]["steps"];
    assert_eq!(steps[0]["step"], "t_add");
    assert_eq!(
        steps[0]["params"],
        serde_json::json!([
            {"name": "k", "typ": "u8", "domain": "0..255"},
            {"name": "g", "typ": "bool", "domain": "BOOLEAN"},
        ])
    );
    let (spec, _, cfg) = trace_spec(&ex);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    // `g` is left out of the log (it only reaches the ghost field), so it
    // ranges over BOOLEAN; the Seq is observed whole and then by index, its
    // records partially, and so are a Map's values (its keys whole). Both
    // variants of `Ev` have a field `v0`: each is compared under its tag.
    let log = ex.dir.path().join("t.ndjson");
    let lines = [
        r#"{"module": "State_tla", "export": "test_crate", "state": {"s": [], "set": [], "m": [], "o": {"tag": "None"}, "mr": [], "ev": {"tag": "Lo", "v0": 0}}}"#,
        r#"{"step": "t_add", "params": {"k": 2}, "state": {"s": [{"a": 2}], "set": [2], "m": [[2, true]], "o": {"tag": "Some", "v0": 2}, "mode": {"tag": "On", "v0": 2}, "mr": [[2, {"a": 2}]], "ev": {"tag": "Hi", "v0": 2}}}"#,
        r#"{"step": "t_add", "params": {"k": 0, "g": false}, "state": {"s": {"1": {"a": 0, "ghost_b": 0}}, "set": [0, 2], "o": {"tag": "Some"}, "mr": [[0, {"a": 0}], [2, {"ghost_b": 1}]], "ev": {"tag": "Lo", "v0": 0}}}"#,
    ];
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 3, "{out}");
    // A Map value's field, a Map key, or a shared label under the other tag
    // the model cannot produce stops the log at the step observing it.
    for (from, to) in [
        (r#"[[0, {"a": 0}], [2, {"ghost_b": 1}]]"#, r#"[[0, {"a": 0}], [2, {"ghost_b": 0}]]"#),
        (r#"[[0, {"a": 0}], [2, {"ghost_b": 1}]]"#, r#"[[1, {"a": 0}], [2, {"ghost_b": 1}]]"#),
        (r#""ev": {"tag": "Lo", "v0": 0}}}"#, r#""ev": {"tag": "Hi", "v0": 0}}}"#),
        (r#""ev": {"tag": "Lo", "v0": 0}}}"#, r#""ev": {"tag": "Lo", "v0": 2}}}"#),
    ] {
        let bad = lines[2].replace(from, to);
        assert_ne!(bad, lines[2]);
        std::fs::write(&log, format!("{}\n{}\n{bad}\n", lines[0], lines[1])).unwrap();
        let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
        assert_eq!(depth, 2, "{to}\n{out}");
    }
    // An empty object observes nothing of a Seq; an empty array is the
    // empty Seq, which `s` is not after two steps.
    let s_by_index = r#""s": {"1": {"a": 0, "ghost_b": 0}}"#;
    for (to, want) in [(r#""s": {}"#, 3), (r#""s": []"#, 2)] {
        let line = lines[2].replace(s_by_index, to);
        assert_ne!(line, lines[2]);
        std::fs::write(&log, format!("{}\n{}\n{line}\n", lines[0], lines[1])).unwrap();
        let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
        assert_eq!(depth, want, "{to}\n{out}");
    }
    // A key that is no index stops TLC; an index past the end only diverges.
    let line = lines[2].replace(s_by_index, r#""s": {"x1": {"a": 0}}"#);
    std::fs::write(&log, format!("{}\n{}\n{line}\n", lines[0], lines[1])).unwrap();
    let out = stops(&jar, &spec, &cfg, &log, "");
    assert!(out.contains("observed as an object has a key that is no index: x1"), "{}", out);
    let line = lines[2].replace(s_by_index, r#""s": {"7": {"a": 0}}"#);
    std::fs::write(&log, format!("{}\n{}\n{line}\n", lines[0], lines[1])).unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 2, "{out}");
    // A value the model cannot produce (k = 5 fails the guard) stops it.
    std::fs::write(&log, lines[..2].join("\n").replace("\"k\": 2", "\"k\": 5") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 1, "{out}");
}

#[test]
fn tla_export_trace_spec_stops_at_a_malformed_log() {
    let ex = export(&fixture("counter.rs"), "test_crate");
    let (spec, _, cfg) = trace_spec(&ex);
    let Some(jar) = tla_tools() else { return };
    let log = ex.dir.path().join("t.ndjson");
    let header = r#"{"module": "State_tla", "export": "test_crate", "state": {"x": 0, "y": 0}}"#;
    // A log for another module is not read as this one's.
    std::fs::write(&log, "{\"module\": \"Other_tla\", \"export\": \"other\"}\n").unwrap();
    let out = stops(&jar, &spec, &cfg, &log, "");
    assert!(out.contains("trace: the log's header does not name the module State_tla"), "{}", out);
    // Nor is one for another export whose state has the same name, or a
    // header naming no export.
    for other in
        [r#"{"module": "State_tla", "export": "other_crate::Other"}"#, r#"{"module": "State_tla"}"#]
    {
        std::fs::write(&log, format!("{other}\n")).unwrap();
        let out = stops(&jar, &spec, &cfg, &log, "");
        assert!(
            out.contains("trace: the log's header does not name the export test_crate"),
            "{}",
            out
        );
    }
    // A parameter the step does not declare (a misspelling) is not ignored.
    let line = r#"{"step": "t_inc", "params": {"n": 1}, "state": {"x": 1}}"#;
    std::fs::write(&log, format!("{header}\n{line}\n")).unwrap();
    let out = stops(&jar, &spec, &cfg, &log, "");
    assert!(out.contains("trace: t_inc has no parameter n"), "{}", out);
    // Nor is a step the model does not have, or a field the state lacks.
    let line = r#"{"step": "t_dec", "params": {}, "state": {}}"#;
    std::fs::write(&log, format!("{header}\n{line}\n")).unwrap();
    let out = stops(&jar, &spec, &cfg, &log, "");
    assert!(out.contains("trace: the model has no step t_dec"), "{}", out);
    let line = r#"{"step": "t_inc", "params": {}, "state": {"z": 1}}"#;
    std::fs::write(&log, format!("{header}\n{line}\n")).unwrap();
    let out = stops(&jar, &spec, &cfg, &log, "");
    assert!(out.contains("trace: the state has no field z"), "{}", out);
    // A misspelled "state" or "params" is not read as observing nothing,
    // in a step line or in the header; nor is a step line without "step".
    for (line, want) in [
        (r#"{"step": "t_inc", "stat": {"x": 7}}"#, "trace: a step line has no key stat"),
        (
            r#"{"step": "t_inc", "param": {}, "state": {"x": 1}}"#,
            "trace: a step line has no key param",
        ),
        (r#"{"state": {"x": 1}}"#, "trace: a step line names no step"),
    ] {
        std::fs::write(&log, format!("{header}\n{line}\n")).unwrap();
        let out = stops(&jar, &spec, &cfg, &log, "");
        assert!(out.contains(want), "{}\n{}", line, out);
    }
    let bad = r#"{"module": "State_tla", "export": "test_crate", "State": {"x": 7, "y": 0}}"#;
    std::fs::write(&log, format!("{bad}\n")).unwrap();
    let out = stops(&jar, &spec, &cfg, &log, "");
    assert!(out.contains("trace: the log's header has no key State"), "{}", out);
}

#[test]
fn tla_export_trace_spec_names_a_shared_step_by_its_path() {
    let ex = export_code(
        r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: u8, pub s: Seq<u8> }
pub open spec fn init(s: State) -> bool { s.x == 0 && s.s == Seq::<u8>::empty() }
pub mod a {
    use super::*;
    pub open spec fn step(pre: State, post: State, k: u8) -> bool {
        &&& k < 3 &&& post.x == k &&& post.s == pre.s.push(k)
    }
}
pub mod b {
    use super::*;
    pub open spec fn step(pre: State, post: State) -> bool { &&& post.x == 200 &&& post.s == pre.s }
}
pub open spec fn next(pre: State, post: State) -> bool {
    (exists|k: u8| a::step(pre, post, k)) || b::step(pre, post)
}
}
"#,
        "test_crate",
    );
    let steps = ex.report["trace"]["steps"].as_array().unwrap();
    let mut named: Vec<(String, bool)> = steps
        .iter()
        .map(|s| (s["step"].as_str().unwrap().to_string(), s["short_name_shared"] == true))
        .collect();
    named.sort();
    assert_eq!(
        named,
        [("test_crate::a::step".to_string(), true), ("test_crate::b::step".to_string(), true)]
    );
    let (spec, _, cfg) = trace_spec(&ex);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    let log = ex.dir.path().join("t.ndjson");
    let header = r#"{"module": "State_tla", "export": "test_crate", "state": {"x": 0}}"#;
    // By their full paths, each step is the one named.
    let lines = [
        header,
        r#"{"step": "test_crate::a::step", "params": {"k": 1}, "state": {"x": 1, "s": [1]}}"#,
        r#"{"step": "test_crate::b::step", "state": {"x": 200, "s": [1]}}"#,
    ];
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 3, "{out}");
    // The shared short name names neither: TLC stops rather than pick one.
    std::fs::write(
        &log,
        format!("{header}\n{}\n", lines[1].replace("test_crate::a::step", "step")),
    )
    .unwrap();
    let out = stops(&jar, &spec, &cfg, &log, "");
    assert!(
        out.contains("trace: step names more than one step (test_crate::")
            && out.contains("): log its full path"),
        "{}",
        out
    );
}

#[test]
fn tla_export_trace_spec_follows_a_verussync_log() {
    let ex = export(&fixture("adder_sync.rs"), "test_crate::Adder");
    // `add(v: int)`: `v` is the field of the `Step::add` Next matches, which
    // its `exists` bounds by the hole `Dom_Step_add_v0`, so a log may leave
    // it out. `next_by`, the dispatch on `Step`, is loggable too, its `Step`
    // ranging over the bound of that `exists`.
    assert_eq!(
        ex.report["trace"]["steps"],
        serde_json::json!([{
            "step": "add", "function": "test_crate::Adder::State::add", "operator": "add",
            "short_name_shared": false,
            "params": [{"name": "v", "typ": "int", "domain": "Dom_Step_add_v0"}],
            "enumerated": true,
        }, {
            "step": "next_by", "function": "test_crate::Adder::State::next_by",
            "operator": "next_by", "short_name_shared": false,
            "params": [{"name": "step", "typ": "Step",
                        "domain": "({[tag |-> \"add\", v0 |-> v0__] : v0__ \\in Dom_Step_add_v0})"}],
            "enumerated": true,
        }])
    );
    let (spec, tla, cfg) = trace_spec(&ex);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    let constants = "CONSTANTS Dom_Step_add_v0 = {0, 1, 2}\n";
    let log = ex.dir.path().join("t.ndjson");
    let lines = [
        r#"{"module": "State_tla", "export": "test_crate::Adder", "state": {"x": 0, "y": 0}}"#,
        r#"{"step": "add", "params": {"v": 2}, "state": {"x": 2, "y": 2}}"#,
        r#"{"step": "test_crate::Adder::State::add", "params": {}, "state": {"x": 3}}"#,
    ];
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, constants);
    assert_eq!(depth, 3, "{out}");
    // With `v` left out, the model's enabled steps enumerate it over the
    // hole (and `next_by`'s `Step` over the records holding it); x going 2
    // to 7 is no `v` in it, so TLC stops at that step.
    std::fs::write(&log, lines[..2].join("\n") + "\n" + &lines[2].replace("\"x\": 3", "\"x\": 7"))
        .unwrap();
    let spec_probe = spec.with_file_name("Probe_trace.tla");
    std::fs::write(
        &spec_probe,
        tla.replace("MODULE State_tla_trace", "MODULE Probe_trace").replace(
            "\n=====",
            "\nProbe == trace_i = 2 => PrintT(<<\"probe\", TraceEnabled, TraceDiagnosis>>)\n=====",
        ),
    )
    .unwrap();
    let (depth, out) =
        follow(&jar, &spec_probe, &cfg, &log, &format!("{constants}INVARIANT Probe\n"));
    assert_eq!(depth, 2, "{out}");
    assert!(
        out.contains(
            "<<\"probe\", {[params |-> [step |-> [tag |-> \"add\", v0 |-> 0]], step |-> \"next_by\"], [params |-> [step |-> [tag |-> \"add\", v0 |-> 1]], step |-> \"next_by\"], [params |-> [step |-> [tag |-> \"add\", v0 |-> 2]], step |-> \"next_by\"], [params |-> [v |-> 0], step |-> \"add\"], [params |-> [v |-> 1], step |-> \"add\"], [params |-> [v |-> 2], step |-> \"add\"]}, [step_enabled |-> TRUE, unmatched |-> {\"x\"}]>>"
        ), "{}", out);
}

#[test]
fn tla_export_trace_spec_decodes_a_record_in_a_set_whole() {
    let ex = export_code(
        r#"
use vstd::prelude::*;
verus! {
pub struct Rec { pub a: u8, pub b: nat }
pub struct State { pub set: Set<Rec>, pub last: Rec }
pub open spec fn init(s: State) -> bool {
    &&& s.set == Set::<Rec>::empty() &&& s.last == Rec { a: 0, b: 0 }
}
pub open spec fn t_put(pre: State, post: State, a: u8) -> bool {
    &&& a < 3
    &&& post.set == pre.set.insert(Rec { a, b: 7 })
    &&& post.last == Rec { a, b: 7 }
}
pub open spec fn next(pre: State, post: State) -> bool { exists|a: u8| t_put(pre, post, a) }
}
"#,
        "test_crate",
    );
    let (spec, _, cfg) = trace_spec(&ex);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    let log = ex.dir.path().join("t.ndjson");
    let header = r#"{"module": "State_tla", "export": "test_crate"}"#;
    // In the state a record is partial (`last`), in a Set element whole.
    let line = r#"{"step": "t_put", "params": {"a": 1}, "state": {"set": [{"a": 1, "b": 7}], "last": {"a": 1}}}"#;
    std::fs::write(&log, format!("{header}\n{line}\n")).unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 2, "{out}");
    // A Set element's record leaving out a field stops TLC.
    std::fs::write(&log, format!("{header}\n{}\n", line.replace(r#", "b": 7}]"#, "}]"))).unwrap();
    let out = stops(&jar, &spec, &cfg, &log, "");
    assert!(out.contains("\"b\""), "{}", out);
    // A partial record in the state naming a field its type lacks (a
    // misspelling) stops TLC, as a misspelled state field does, rather than
    // diverging.
    std::fs::write(
        &log,
        format!("{header}\n{}\n", line.replace(r#""last": {"a""#, r#""last": {"aa""#)),
    )
    .unwrap();
    let out = stops(&jar, &spec, &cfg, &log, "");
    assert!(out.contains("trace: Rec has no field aa"), "{}", out);
}

#[test]
fn tla_export_trace_spec_logs_a_step_that_branches_into_helpers() {
    let ex = export_code(
        r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: u8, pub y: u8 }
pub open spec fn init(s: State) -> bool { s.x == 0 && s.y == 0 }
pub open spec fn bump(pre: State, post: State) -> bool { post.x == 1 && post.y == pre.y }
pub open spec fn reset(pre: State, post: State) -> bool { post.x == 0 && post.y == pre.y }
pub open spec fn t_recv(pre: State, post: State, b: bool) -> bool {
    if b { bump(pre, post) } else { reset(pre, post) }
}
pub open spec fn t_other(pre: State, post: State) -> bool {
    ||| post.x == pre.x && post.y == 1
    ||| bump(pre, post)
}
pub open spec fn next(pre: State, post: State) -> bool {
    (exists|b: bool| t_recv(pre, post, b)) || t_other(pre, post)
}
}
"#,
        "test_crate",
    );
    // `t_recv` branches into `bump` and `reset`: it is a step, and so are
    // they; `next`, which only dispatches, is not.
    let steps = ex.report["trace"]["steps"].as_array().unwrap();
    let named: Vec<&str> = steps.iter().map(|s| s["step"].as_str().unwrap()).collect();
    assert_eq!(named, ["bump", "reset", "t_other", "t_recv"]);
    assert_eq!(
        steps[3]["params"],
        serde_json::json!([{"name": "b", "typ": "bool", "domain": "BOOLEAN"}])
    );
    let (spec, _, cfg) = trace_spec(&ex);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    let log = ex.dir.path().join("t.ndjson");
    let lines = [
        r#"{"module": "State_tla", "export": "test_crate", "state": {"x": 0, "y": 0}}"#,
        r#"{"step": "t_recv", "params": {"b": true}, "state": {"x": 1, "y": 0}}"#,
        r#"{"step": "t_other", "params": {}, "state": {"x": 1, "y": 1}}"#,
        r#"{"step": "t_recv", "state": {"x": 0, "y": 1}}"#,
        r#"{"step": "bump", "params": {}, "state": {"x": 1, "y": 1}}"#,
    ];
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 5, "{out}");
    // The step's own parameter still narrows it: `b` false is `reset`.
    std::fs::write(&log, format!("{}\n{}\n", lines[0], lines[1].replace("true", "false"))).unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 1, "{out}");
}

/// A helper step reads the primed variables its caller assigned
/// (`chk: y' = x'`): Next comes first in TraceNext, so the helper only
/// filters the successors Next assigned. `next = t_step` conjoins the one
/// transition, so it is loggable although it is not a branch; `frame`,
/// which `t_step` conjoins and which branches into nothing, is not.
#[test]
fn tla_export_trace_spec_takes_next_before_the_logged_step() {
    let ex = export_code(
        r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: u8, pub y: u8 }
pub open spec fn init(s: State) -> bool { s.x == 0 && s.y == 0 }
pub open spec fn frame(pre: State, post: State) -> bool { post.x == pre.x + 1 }
pub open spec fn chk(pre: State, post: State) -> bool { post.y == post.x }
pub open spec fn other(pre: State, post: State) -> bool { post.y == pre.y }
pub open spec fn t_step(pre: State, post: State) -> bool {
    pre.x < 3 && frame(pre, post) && (if pre.x == 0 { chk(pre, post) } else { other(pre, post) })
}
pub open spec fn next(pre: State, post: State) -> bool { t_step(pre, post) }
}
"#,
        "test_crate",
    );
    let steps = ex.report["trace"]["steps"].as_array().unwrap();
    let named: Vec<&str> = steps.iter().map(|s| s["step"].as_str().unwrap()).collect();
    assert_eq!(named, ["chk", "other", "t_step"]);
    let (spec, tla, cfg) = trace_spec(&ex);
    assert!(tla.contains("ENABLED (Next /\\ chk)"), "{}", tla);
    assert!(tla.contains("step_enabled |-> ENABLED (Next /\\ TraceStep(e))"), "{}", tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    let log = ex.dir.path().join("t.ndjson");
    let lines = [
        r#"{"module": "State_tla", "export": "test_crate", "state": {"x": 0, "y": 0}}"#,
        r#"{"step": "chk", "state": {"x": 1, "y": 1}}"#,
        r#"{"step": "other", "state": {"x": 2, "y": 1}}"#,
        r#"{"step": "t_step", "state": {"x": 3, "y": 1}}"#,
    ];
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 4, "{out}");
    // `chk` where the model took `other` (x is 1, not 0) stops the log.
    std::fs::write(
        &log,
        format!("{}\n{}\n{}\n", lines[0], lines[1], lines[2].replace("other", "chk")),
    )
    .unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 2, "{out}");
}

/// A guard is never a step, even reached inside a branch: `ready` reads
/// only the pre state and `small` no state at all. The one transition Next
/// conjoins beside a guard (`t_only`) is.
#[test]
fn tla_export_trace_spec_logs_no_guard() {
    let ex = export_code(
        r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: u8, pub y: u8 }
pub open spec fn init(s: State) -> bool { s.x == 0 && s.y == 0 }
pub open spec fn ready(s: State) -> bool { s.x < 3 }
pub open spec fn small(v: u8) -> bool { v < 2 }
pub open spec fn t_a(pre: State, post: State) -> bool { ready(pre) && post.x == pre.x + 1 && post.y == pre.y }
pub open spec fn t_c(pre: State, post: State, b: bool) -> bool {
    if b { ready(pre) && small(pre.y) && post.x == pre.x && post.y == pre.y + 1 } else { post == pre }
}
pub open spec fn next(pre: State, post: State) -> bool {
    t_a(pre, post) || (exists|b: bool| t_c(pre, post, b))
}
}
"#,
        "test_crate",
    );
    let steps = ex.report["trace"]["steps"].as_array().unwrap();
    let named: Vec<&str> = steps.iter().map(|s| s["step"].as_str().unwrap()).collect();
    assert_eq!(named, ["t_a", "t_c"]);
    let ex = export_code(
        r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: u8 }
pub open spec fn init(s: State) -> bool { s.x == 0 }
pub open spec fn ready(s: State) -> bool { s.x < 3 }
pub open spec fn t_only(pre: State, post: State) -> bool { post.x == pre.x + 1 }
pub open spec fn next(pre: State, post: State) -> bool { ready(pre) && t_only(pre, post) }
}
"#,
        "test_crate",
    );
    let steps = ex.report["trace"]["steps"].as_array().unwrap();
    let named: Vec<&str> = steps.iter().map(|s| s["step"].as_str().unwrap()).collect();
    assert_eq!(named, ["t_only"]);
    let (spec, _, cfg) = trace_spec(&ex);
    let Some(jar) = tla_tools() else { return };
    let log = ex.dir.path().join("t.ndjson");
    let lines = [
        r#"{"module": "State_tla", "export": "test_crate", "state": {"x": 0}}"#,
        r#"{"step": "t_only", "state": {"x": 1}}"#,
        r#"{"step": "t_only", "state": {"x": 2}}"#,
        r#"{"step": "t_only", "state": {"x": 3}}"#,
        r#"{"step": "t_only", "state": {"x": 4}}"#,
    ];
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    // x = 3 is no longer ready: the fourth step stops the log.
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 4, "{out}");
}

/// The verus-tla shape: `next()` is one action of closures, so the only
/// step is `next`; an `Option` is observed by its tag, its payload too.
#[test]
fn tla_export_trace_spec_follows_a_verus_tla_log() {
    let ex = export(&fixture("mutex_tla.rs"), "test_crate");
    assert_eq!(ex.report["shape"], "verus-tla");
    let steps = ex.report["trace"]["steps"].as_array().unwrap();
    let named: Vec<&str> = steps.iter().map(|s| s["step"].as_str().unwrap()).collect();
    assert_eq!(named, ["next"]);
    let (spec, _, cfg) = trace_spec(&ex);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    let log = ex.dir.path().join("t.ndjson");
    let lines = [
        r#"{"module": "State_tla", "export": "test_crate", "state": {"holder": {"tag": "None"}, "count": 0}}"#,
        r#"{"step": "next", "state": {"holder": {"tag": "Some", "v0": 1}, "count": 1}}"#,
        r#"{"step": "next", "params": {}, "state": {"holder": {"tag": "None"}}}"#,
    ];
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 3, "{out}");
    // A holder no acquire gives (thread 7), or a count that jumps, stops it.
    for (from, to) in [(r#""v0": 1"#, r#""v0": 7"#), (r#""count": 1"#, r#""count": 2"#)] {
        let bad = lines[1].replace(from, to);
        assert_ne!(bad, lines[1]);
        std::fs::write(&log, format!("{}\n{bad}\n", lines[0])).unwrap();
        let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
        assert_eq!(depth, 1, "{to}\n{out}");
    }
}

/// A step parameter ranges over the field of the `Step` value Next matches,
/// whatever position the parameter takes: `Step::t_set(f, n)` passes its
/// fields to `t_set(n, f)` swapped. `n` (an int) ranges over the hole
/// `Dom_Step_t_set_v1` of its own type, and `f` over the booleans, never
/// the other's field.
#[test]
fn tla_export_trace_spec_takes_a_parameter_domain_from_the_match() {
    let ex = export_code(
        r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: int, pub b: bool }
pub enum Step { t_set(bool, int), t_nop }
pub open spec fn init(s: State) -> bool { s.x == 0 && !s.b }
pub open spec fn t_set(pre: State, post: State, n: int, f: bool) -> bool {
    post.x == n && post.b == f
}
pub open spec fn t_nop(pre: State, post: State) -> bool { post == pre }
pub open spec fn next_step(pre: State, post: State, step: Step) -> bool {
    match step {
        Step::t_set(f, n) => t_set(pre, post, n, f),
        Step::t_nop => t_nop(pre, post),
    }
}
pub open spec fn next(pre: State, post: State) -> bool { exists|s: Step| next_step(pre, post, s) }
}
"#,
        "test_crate",
    );
    let steps = ex.report["trace"]["steps"].as_array().unwrap();
    let t_set = steps.iter().find(|s| s["step"] == "t_set").unwrap();
    assert_eq!(t_set["params"][0]["name"], "n");
    assert_eq!(t_set["params"][0]["domain"], "Dom_Step_t_set_v1", "{}", t_set);
    assert_eq!(t_set["params"][1]["name"], "f");
    let f_domain = t_set["params"][1]["domain"].as_str().unwrap();
    // The booleans, as the `v0` fields of the `Step::t_set` values Next
    // ranges over (never the int hole of `v1`).
    assert!(f_domain.starts_with("{s__.v0 : s__ \\in "), "{}", t_set);
    assert_eq!(t_set["enumerated"], true);
    let (spec, _, cfg) = trace_spec(&ex);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    let constants = "CONSTANTS Dom_Step_t_set_v1 = {2, 7}\n";
    let log = ex.dir.path().join("t.ndjson");
    let lines = [
        r#"{"module": "State_tla", "export": "test_crate", "state": {"x": 0, "b": false}}"#,
        r#"{"step": "t_set", "params": {"n": 7}, "state": {"x": 7, "b": true}}"#,
        r#"{"step": "t_set", "state": {"x": 2, "b": false}}"#,
    ];
    // `f` left out ranges over the booleans, then both over their fields.
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, constants);
    assert_eq!(depth, 3, "{}", out);
    // x = 5 is no `n` in the hole: the second step stops the log.
    std::fs::write(&log, lines[..2].join("\n") + "\n" + &lines[2].replace("\"x\": 2", "\"x\": 5"))
        .unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, constants);
    assert_eq!(depth, 2, "{}", out);
}

/// A parameter Next binds with a quantifier ranges over the bound Next
/// gives it (`exists|n: u64| n < 3 && ...`, `0..2`), which its type alone
/// (`u64`) would not give; a parameter passed a value of no known domain
/// must be logged, and the report says `TraceEnabled` leaves its step out.
#[test]
fn tla_export_trace_spec_takes_a_parameter_domain_from_a_quantifier() {
    let ex = export_code(
        r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: u64 }
pub open spec fn init(s: State) -> bool { s.x == 0 }
pub open spec fn t_go(pre: State, post: State, n: u64) -> bool { post.x == pre.x + n }
pub open spec fn t_jump(pre: State, post: State, to: int) -> bool { post.x == to }
pub open spec fn next(pre: State, post: State) -> bool {
    ||| exists|n: u64| n < 3 && t_go(pre, post, n)
    ||| pre.x < 10 && t_jump(pre, post, pre.x + 5)
}
}
"#,
        "test_crate",
    );
    let steps = ex.report["trace"]["steps"].as_array().unwrap();
    let step = |name: &str| steps.iter().find(|s| s["step"] == name).unwrap().clone();
    let (t_go, t_jump) = (step("t_go"), step("t_jump"));
    assert_eq!(t_go["params"][0]["domain"], "0..(3) - 1", "{t_go}");
    assert_eq!(t_go["enumerated"], true);
    assert_eq!(t_jump["params"][0]["domain"], serde_json::Value::Null, "{t_jump}");
    assert_eq!(t_jump["enumerated"], false);
    let (spec, tla, cfg) = trace_spec(&ex);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    let log = ex.dir.path().join("t.ndjson");
    let lines = [
        r#"{"module": "State_tla", "export": "test_crate", "state": {"x": 0}}"#,
        r#"{"step": "t_go", "state": {"x": 2}}"#,
        r#"{"step": "t_jump", "params": {"to": 7}, "state": {"x": 7}}"#,
    ];
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 3, "{}", out);
    // An n of 5 is outside the bound: the first step stops the log, where
    // the enabled steps list t_go's three and not t_jump.
    std::fs::write(&log, format!("{}\n{}\n", lines[0], lines[1].replace("\"x\": 2", "\"x\": 5")))
        .unwrap();
    let spec_probe = spec.with_file_name("Probe_trace.tla");
    std::fs::write(
        &spec_probe,
        tla.replace("MODULE State_tla_trace", "MODULE Probe_trace").replace(
            "\n=====",
            "\nProbe == trace_i = 1 => PrintT(<<\"probe\", TraceEnabled>>)\n=====",
        ),
    )
    .unwrap();
    let (depth, out) = follow(&jar, &spec_probe, &cfg, &log, "INVARIANT Probe\n");
    assert_eq!(depth, 1, "{}", out);
    // TLC breaks a long value over lines: compared without whitespace.
    let flat: String = out.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(
        flat.contains(
            "<<\"probe\",{[params|->[n|->0],step|->\"t_go\"],[params|->[n|->1],step|->\"t_go\"],[params|->[n|->2],step|->\"t_go\"]}>>"
        ),
        "{}",
        out
    );
    // t_jump with `to` left out stops TLC, saying why.
    std::fs::write(&log, format!("{}\n{}\n", lines[0], r#"{"step": "t_jump", "state": {"x": 5}}"#))
        .unwrap();
    let out = stops(&jar, &spec, &cfg, &log, "");
    assert!(
        out.contains("trace: t_jump leaves out its parameter to, which has no domain"),
        "{}",
        out
    );
}

/// A call passing a computed value (`pre.x + 5`) gives its parameter no
/// domain, even when the export has a `Dom_int` hole from a quantifier: the
/// hole holds only what the quantifier binds. A logged parameter is narrowed
/// to its domain; the step's label counts only through the state it reaches.
#[test]
fn tla_export_trace_spec_takes_no_hole_for_a_computed_argument() {
    let ex = export_code(
        r#"
use vstd::prelude::*;
verus! {
pub struct State { pub x: int, pub y: int }
pub open spec fn init(s: State) -> bool { s.x == 0 && s.y == 0 }
pub open spec fn t_set(pre: State, post: State, n: int) -> bool { post.y == n && post.x == pre.x }
pub open spec fn t_jump(pre: State, post: State, to: int) -> bool { post.x == to && post.y == pre.y }
pub open spec fn next(pre: State, post: State) -> bool {
    ||| exists|n: int| t_set(pre, post, n)
    ||| pre.x < 10 && t_jump(pre, post, pre.x + 5)
}
}
"#,
        "test_crate",
    );
    let steps = ex.report["trace"]["steps"].as_array().unwrap();
    let step = |name: &str| steps.iter().find(|s| s["step"] == name).unwrap().clone();
    let (t_set, t_jump) = (step("t_set"), step("t_jump"));
    assert_eq!(t_set["params"][0]["domain"], "Dom_int", "{t_set}");
    assert_eq!(t_set["enumerated"], true);
    assert_eq!(t_jump["params"][0]["domain"], serde_json::Value::Null, "{t_jump}");
    assert_eq!(t_jump["enumerated"], false);
    let (spec, tla, cfg) = trace_spec(&ex);
    assert!(tla.contains("A pass means the observed state sequence is a behaviour"), "{}", tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    let holes = "CONSTANT Dom_int = {0, 1}\n";
    let log = ex.dir.path().join("t.ndjson");
    let header = r#"{"module": "State_tla", "export": "test_crate", "state": {"x": 0, "y": 0}}"#;
    let write = |lines: &[&str]| {
        std::fs::write(&log, format!("{header}\n{}\n", lines.join("\n"))).unwrap();
    };
    // t_jump to 5, outside Dom_int, is a step of the model when logged.
    write(&[
        r#"{"step": "t_jump", "params": {"to": 5}, "state": {"x": 5}}"#,
        r#"{"step": "t_set", "state": {"y": 1}}"#,
    ]);
    let (depth, out) = follow(&jar, &spec, &cfg, &log, holes);
    assert_eq!(depth, 3, "{}", out);
    // Left out, it has no domain to range over: TLC stops saying why.
    write(&[r#"{"step": "t_jump", "state": {"x": 5}}"#]);
    let out = stops(&jar, &spec, &cfg, &log, holes);
    assert!(
        out.contains("trace: t_jump leaves out its parameter to, which has no domain"),
        "{}",
        out
    );
    // A logged n outside its domain (Dom_int) is a step the model cannot take.
    write(&[r#"{"step": "t_set", "params": {"n": 7}, "state": {"x": 0}}"#]);
    let (depth, out) = follow(&jar, &spec, &cfg, &log, holes);
    assert_eq!(depth, 1, "{}", out);
    // The label counts only through its effect: t_jump to 0 is never a step
    // of the model from x 0, but t_set(0) reaches the same state.
    write(&[r#"{"step": "t_jump", "params": {"to": 0}, "state": {"x": 0, "y": 0}}"#]);
    let (depth, out) = follow(&jar, &spec, &cfg, &log, holes);
    assert_eq!(depth, 2, "{}", out);
}

/// A header whose observed state is none of Init's: TLC finds no initial
/// state and ends without error at depth 0, the divergence before the
/// first step.
#[test]
fn tla_export_trace_spec_diverges_at_a_bad_header_state() {
    let ex = export(&fixture("counter.rs"), "test_crate");
    let (spec, tla, cfg) = trace_spec(&ex);
    assert!(
        tla.contains("when TLC finds no initial state (0 states generated, depth 0)"),
        "{}",
        tla
    );
    assert!(cfg.contains("depth 0 (no initial state)"), "{}", cfg);
    let Some(jar) = tla_tools() else { return };
    let log = ex.dir.path().join("t.ndjson");
    let lines = [
        r#"{"module": "State_tla", "export": "test_crate", "state": {"x": 3, "y": 0}}"#,
        r#"{"step": "t_inc", "params": {}, "state": {"x": 4, "y": 0}}"#,
    ];
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 0, "{}", out);
    assert!(out.contains("0 states generated"), "{}", out);
    // The same log from x = 0 is followed past its header.
    std::fs::write(&log, lines.join("\n").replace("\"x\": 3", "\"x\": 0") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 1, "{}", out);
}

/// An enum observed without its tag: the tag is free, and the fields named
/// are compared under whichever variant the model has. Decoded whole (a
/// parameter), an enum value must name its tag.
#[test]
fn tla_export_trace_spec_leaves_an_unobserved_tag_free() {
    let ex = export_code(
        r#"
use vstd::prelude::*;
verus! {
pub enum Mode { Idle, Busy(u8), Done(u8, bool) }
pub struct State { pub mode: Mode }
pub open spec fn init(s: State) -> bool { s.mode == Mode::Idle }
pub open spec fn t_busy(pre: State, post: State, n: u8) -> bool { n < 3 && post.mode == Mode::Busy(n) }
pub open spec fn t_set(pre: State, post: State, m: Mode) -> bool { post.mode == m }
pub open spec fn next(pre: State, post: State) -> bool {
    ||| exists|n: u8| n < 3 && t_busy(pre, post, n)
    ||| exists|m: Mode| t_set(pre, post, m)
}
}
"#,
        "test_crate",
    );
    let (spec, _, cfg) = trace_spec(&ex);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    let log = ex.dir.path().join("t.ndjson");
    let header = r#"{"module": "State_tla", "export": "test_crate", "state": {"mode": {}}}"#;
    let lines = [
        header,
        r#"{"step": "t_busy", "state": {"mode": {"v0": 2}}}"#,
        r#"{"step": "t_set", "params": {"m": {"tag": "Done", "v0": 1, "v1": true}}, "state": {"mode": {"v1": true}}}"#,
    ];
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 3, "{}", out);
    // A field the model's variant does not have, or another value, stops it.
    for (from, to) in
        [(r#"{"v0": 2}"#, r#"{"v1": true}"#), (r#"{"v0": 2}"#, r#"{"v0": 1, "tag": "Done"}"#)]
    {
        std::fs::write(&log, format!("{header}\n{}\n", lines[1].replace(from, to))).unwrap();
        let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
        assert_eq!(depth, 1, "{to}\n{out}");
    }
    // A label no variant declares is a malformed log, not a divergence.
    std::fs::write(
        &log,
        format!("{header}\n{}\n", lines[1].replace(r#"{"v0": 2}"#, r#"{"v2": 2}"#)),
    )
    .unwrap();
    let out = stops(&jar, &spec, &cfg, &log, "");
    assert!(out.contains("trace: Mode has no field v2"), "{}", out);
    // A parameter decoded whole without its tag stops TLC with the reason.
    let bad = r#"{"step": "t_set", "params": {"m": {"v0": 1}}, "state": {}}"#;
    std::fs::write(&log, format!("{header}\n{bad}\n")).unwrap();
    let out = stops(&jar, &spec, &cfg, &log, "");
    assert!(
        out.contains("trace: a Mode value decoded whole (a parameter, a Set element or a Map key) must name its tag"),
        "{}",
        out
    );
}

#[test]
fn tla_export_trace_spec_binds_no_name_of_the_export() {
    // Every state field is a VARIABLE the trace spec sees through EXTENDS,
    // so the names it binds (a JSON value, a key, an index, a log line, ...)
    // must be fresh against them: SANY rejects a rebound name.
    let ex = export_code(
        r#"
use vstd::prelude::*;
verus! {
pub struct State { pub v: nat, pub k: nat, pub e: bool, pub j: Seq<u8>, pub p: Map<u8, bool>, pub r: Option<u8> }
pub open spec fn init(s: State) -> bool {
    &&& s.v == 0 &&& s.k == 0 &&& s.e == false
    &&& s.j == Seq::<u8>::empty() &&& s.p == Map::<u8, bool>::empty() &&& s.r == None::<u8>
}
pub open spec fn t_go(pre: State, post: State, a: bool) -> bool {
    &&& pre.v < 3
    &&& post.v == pre.v + 1
    &&& post.k == pre.k
    &&& post.e == a
    &&& post.j == pre.j.push(1)
    &&& post.p == pre.p.insert(1, a)
    &&& post.r == Some(1u8)
}
pub open spec fn next(pre: State, post: State) -> bool { exists|a: bool| t_go(pre, post, a) }
}
"#,
        "test_crate",
    );
    let (spec, tla, cfg) = trace_spec(&ex);
    assert!(tla.contains("TraceParam(e_2, k_2, Dec(_), D) ==\n"), "{}", tla);
    assert!(tla.contains("TraceIsArray(j_2) =="), "{}", tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    let log = ex.dir.path().join("t.ndjson");
    let header = r#"{"module": "State_tla", "export": "test_crate", "state": {"v": 0, "j": []}}"#;
    let lines = [
        header,
        r#"{"step": "t_go", "params": {"a": true}, "state": {"v": 1, "k": 0, "e": true, "j": [1], "p": [[1, true]], "r": {"tag": "Some", "v0": 1}}}"#,
        r#"{"step": "t_go", "state": {"v": 2, "e": false, "j": {"1": 1}, "p": [[1, false]]}}"#,
    ];
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 3, "{}", out);
    // A wrong value still diverges there.
    std::fs::write(&log, format!("{header}\n{}\n", lines[1].replace(r#""v": 1"#, r#""v": 2"#)))
        .unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 1, "{}", out);
}

#[test]
fn tla_export_trace_spec_decodes_a_unit_struct() {
    // A struct without fields is `[tag |-> "unit"]` in the export: the trace
    // spec observes it from `{}` and decodes a parameter of it whole.
    let ex = export_code(
        r#"
use vstd::prelude::*;
verus! {
pub struct Tick {}
pub struct State { pub n: nat, pub t: Tick }
pub open spec fn init(s: State) -> bool { s.n == 0 && s.t == Tick {} }
pub open spec fn t_tick(pre: State, post: State, t: Tick) -> bool {
    &&& pre.n < 2
    &&& post.n == pre.n + 1
    &&& post.t == t
}
pub open spec fn next(pre: State, post: State) -> bool { exists|t: Tick| t_tick(pre, post, t) }
}
"#,
        "test_crate",
    );
    let (spec, _, cfg) = trace_spec(&ex);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    let log = ex.dir.path().join("t.ndjson");
    let header = r#"{"module": "State_tla", "export": "test_crate", "state": {"t": {}}}"#;
    let lines = [
        header,
        r#"{"step": "t_tick", "params": {"t": {}}, "state": {"n": 1, "t": {}}}"#,
        r#"{"step": "t_tick", "params": {"t": {"tag": "unit"}}, "state": {"t": {"tag": "unit"}}}"#,
    ];
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 3, "{}", out);
    // It has no field to observe.
    std::fs::write(
        &log,
        format!("{header}\n{}\n", lines[1].replace(r#""t": {}}}"#, r#""t": {"x": 1}}}"#)),
    )
    .unwrap();
    let out = stops(&jar, &spec, &cfg, &log, "");
    assert!(out.contains("trace: Tick has no field x"), "{}", out);
}

/// verus-tla's `defs` and `Action`, as `mutex_liveness.rs` carries them.
fn verus_tla_defs() -> String {
    let src = std::fs::read_to_string(fixture("mutex_liveness.rs")).unwrap();
    let start = src.find("pub mod defs {").unwrap();
    let end = src.find("use action::*;").unwrap();
    src[start..end].to_string()
}

#[test]
fn tla_export_verus_tla_liveness_under_weak_fairness() {
    let ex = export(&fixture("mutex_liveness.rs"), "test_crate");
    assert_eq!(ex.report["shape"], "verus-tla");
    assert_eq!(ex.report["refusals"], serde_json::json!([]));
    assert_eq!(ex.report["holes"], serde_json::json!([]));
    // `init` constrains the map key by key: Init draws it from the maps of
    // a subset of {A, B} to the three thread states.
    assert_eq!(ex.report["init_unassigned"], serde_json::json!([]));
    assert_eq!(ex.report["init_enumerated"][0]["variable"], "threads");
    assert!(ex.tla.contains("Init == (threads \\in UNION {[d__ -> "), "{}", ex.tla);
    // Each `f().forward(input)` is an operator named after `f`, so TLC's
    // steps and WF_vars read as the Verus actions.
    assert!(ex.tla.contains("thread_acquires_lock(input) ==\n"), "{}", ex.tla);
    assert!(ex.tla.contains("stutter ==\n"), "{}", ex.tla);
    assert!(
        ex.tla.contains(
            "thread_acquires_lock([tag |-> \"A\"]) \\/ thread_releases_lock([tag |-> \"A\"])"
        ),
        "{}",
        ex.tla
    );
    let props = ex.report["properties"].as_array().unwrap();
    assert_eq!(props.len(), 1, "{:?}", props);
    let p = &props[0];
    assert_eq!(p["operator"], "both_threads_eventually_terminate");
    assert_eq!(p["formula"], "<>(both_threads_are_terminated)");
    assert_eq!(
        p["fairness"],
        serde_json::json!([
            "(\\A tid \\in ({[tag |-> \"A\"]} \\cup {[tag |-> \"B\"]}) : WF_vars(thread_acquires_lock(tid)))",
            "(\\A tid \\in ({[tag |-> \"A\"]} \\cup {[tag |-> \"B\"]}) : WF_vars(thread_releases_lock(tid)))",
        ])
    );
    assert_eq!(p["assumptions"], serde_json::json!([]));
    assert_eq!(p["without_fairness"], false);
    assert_eq!(p["included"], true);
    assert_eq!(p["notes"], serde_json::json!([]));
    assert_eq!(ex.report["fairness_in_spec"], true);
    assert!(ex.tla.contains("Spec == Init /\\ [][Next]_vars /\\ Fairness\n"), "{}", ex.tla);
    assert!(ex.cfg.contains("PROPERTIES\n  both_threads_eventually_terminate\n"), "{}", ex.cfg);
    // The state the property waits for is not an invariant.
    assert_eq!(ex.report["invariants"], serde_json::json!([]));
    assert_eq!(candidates(&ex.report), [("both_threads_are_terminated".to_string(), false)]);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let out = tlc_output_with(&jar, &ex.spec(), &ex.cfg, &[]);
    assert!(out.contains("No error has been found"), "{}", out);
    assert!(out.contains("8 distinct states found"), "{}", out);

    // Without fairness for release, a thread may hold the lock forever.
    let src = std::fs::read_to_string(fixture("mutex_liveness.rs")).unwrap();
    let unfair: String = src
        .lines()
        .filter(|l| !l.contains("thread_releases_lock().weak_fairness"))
        .map(|l| format!("{l}\n"))
        .collect();
    let dir = TempDir::new().unwrap();
    let entry = dir.path().join("mutex_liveness.rs");
    std::fs::write(&entry, unfair).unwrap();
    let ex = export(&entry, "test_crate");
    assert_eq!(ex.report["properties"][0]["fairness"].as_array().unwrap().len(), 1);
    let out = tlc_output_with(&jar, &ex.spec(), &ex.cfg, &[]);
    assert!(
        out.contains("Error: Temporal property both_threads_eventually_terminate was violated"),
        "{}",
        out
    );
    assert!(out.contains("<thread_acquires_lock("), "{}", out);
    assert!(out.contains("Stuttering"), "{}", out);
}

/// A counter in verus-tla style with its spec in `spec()`: a property under
/// it, and one a proof fn states without fairness.
fn liveness_counter() -> String {
    format!(
        r#"
verus! {{
{defs}
use action::*;
use defs::*;

pub struct S {{ pub x: u8 }}

pub open spec fn init() -> StatePred<S> {{ |s: S| s.x == 0 }}

pub open spec fn inc() -> Action<S, (), ()> {{
    Action {{
        precondition: |input: (), s: S| s.x < 3,
        transition: |input: (), s: S| (S {{ x: (s.x + 1) as u8 }}, ()),
    }}
}}

pub open spec fn next() -> ActionPred<S> {{
    |s: S, s_prime: S| inc().forward(())(s, s_prime) || s_prime == s
}}

pub open spec fn spec() -> TempPred<S> {{
    lift_state(init()).and(always(lift_action(next()))).and(inc().weak_fairness(()))
}}

pub open spec fn reaches_three() -> TempPred<S> {{
    lift_state(init()).leads_to(lift_state(|s: S| s.x == 3))
}}

pub proof fn stops_short(m: TempPred<S>)
    requires
        m.entails(lift_state(init())),
        m.entails(always(lift_action(next()))),
    ensures
        m.entails(eventually(lift_state(|s: S| s.x == 3))),
{{
    admit();
}}
}}
"#,
        defs = verus_tla_defs()
    )
}

#[test]
fn tla_export_verus_tla_liveness_per_property_spec() {
    let ex = export_code(&liveness_counter(), "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]));
    let props = ex.report["properties"].as_array().unwrap();
    let ops: Vec<&str> = props.iter().map(|p| p["operator"].as_str().unwrap()).collect();
    assert_eq!(ops, ["stops_short", "reaches_three"]);
    assert_eq!(props[0]["without_fairness"], true);
    assert_eq!(props[1]["fairness"], serde_json::json!(["WF_vars(inc)"]));
    assert_eq!(props[1]["spec"], "test_crate::spec");
    assert_eq!(props[1]["formula"], "(init ~> (x = 3))");
    // The two specs differ, so Spec has no fairness and each property
    // carries its own as a premise.
    assert_eq!(ex.report["fairness_in_spec"], false);
    assert!(ex.tla.contains("Spec == Init /\\ [][Next]_vars\n"), "{}", ex.tla);
    assert!(ex.tla.contains("reaches_three ==\n    ((WF_vars(inc))) => ("), "{}", ex.tla);
    assert!(ex.cfg.contains("PROPERTY stops_short is checked without fairness"), "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let only = |p: &str| ex.cfg.replace("  stops_short\n  reaches_three\n", &format!("  {p}\n"));
    let out = tlc_output_with(&jar, &ex.spec(), &only("reaches_three"), &[]);
    assert!(out.contains("No error has been found"), "{}", out);
    let out = tlc_output_with(&jar, &ex.spec(), &only("stops_short"), &[]);
    assert!(out.contains("Error: Temporal property stops_short was violated"), "{}", out);
    assert!(out.contains("Stuttering"), "{}", out);
}

/// A verus-tla counter that `inc()` and `bump(b)` (enabled only for `true`)
/// count to 3, with `spec` as the body of `spec()` and `rest` after it.
fn liveness_counter_with(spec: &str, rest: &str) -> String {
    format!(
        r#"
verus! {{
{defs}
use action::*;
use defs::*;

pub struct S {{ pub x: u8 }}

pub open spec fn init() -> StatePred<S> {{ |s: S| s.x == 0 }}

pub open spec fn inc() -> Action<S, (), ()> {{
    Action {{
        precondition: |input: (), s: S| s.x < 3,
        transition: |input: (), s: S| (S {{ x: (s.x + 1) as u8 }}, ()),
    }}
}}

pub open spec fn bump() -> Action<S, bool, ()> {{
    Action {{
        precondition: |b: bool, s: S| s.x < 3 && b,
        transition: |b: bool, s: S| (S {{ x: (s.x + 1) as u8 }}, ()),
    }}
}}

pub open spec fn next() -> ActionPred<S> {{
    |s: S, s_prime: S| inc().forward(())(s, s_prime) || bump().forward(true)(s, s_prime) || s_prime == s
}}

pub open spec fn spec() -> TempPred<S> {{ {spec} }}

{rest}
}}
"#,
        defs = verus_tla_defs()
    )
}

/// Only WF_vars goes into Spec: a spec's `always(lift_state(p))` is the
/// property's premise (TLC cannot take `[]P` in a Spec).
#[test]
fn tla_export_verus_tla_spec_assumption_is_a_premise() {
    let ex = export_code(
        &liveness_counter_with(
            "lift_state(init()).and(always(lift_action(next()))).and(inc().weak_fairness(())).and(always(lift_state(|s: S| s.x <= 3)))",
            "pub open spec fn reaches_three() -> TempPred<S> { eventually(lift_state(|s: S| s.x == 3)) }",
        ),
        "test_crate",
    );
    assert_eq!(ex.report["refusals"], serde_json::json!([]));
    let p = &ex.report["properties"][0];
    assert_eq!(p["fairness"], serde_json::json!(["WF_vars(inc)"]));
    assert_eq!(p["assumptions"], serde_json::json!(["[]((x <= 3))"]));
    assert_eq!(ex.report["fairness_in_spec"], true);
    assert!(ex.tla.contains("Spec == Init /\\ [][Next]_vars /\\ Fairness\n"), "{}", ex.tla);
    assert!(
        ex.tla.contains("reaches_three ==\n    (([]((x <= 3)))) => (<>((x = 3)))\n"),
        "{}",
        ex.tla
    );
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let out = tlc_output_with(&jar, &ex.spec(), &ex.cfg, &[]);
    assert!(out.contains("No error has been found"), "{}", out);
}

/// Properties share their fairness when it comes from the same spec, even
/// where a property's own binder would rename the fairness's (`b`).
#[test]
fn tla_export_verus_tla_fairness_shared_by_source() {
    let ex = export_code(
        &liveness_counter_with(
            "lift_state(init()).and(always(lift_action(next()))).and(tla_forall(|b: bool| bump().weak_fairness(b)))",
            r#"
pub open spec fn a_first() -> TempPred<S> {
    tla_exists(|b: bool| eventually(lift_state(|s: S| s.x == 2 || b)))
}

pub open spec fn reaches_three() -> TempPred<S> { eventually(lift_state(|s: S| s.x == 3)) }
"#,
        ),
        "test_crate",
    );
    assert_eq!(ex.report["refusals"], serde_json::json!([]));
    let props = ex.report["properties"].as_array().unwrap();
    assert_eq!(props.len(), 2, "{:?}", props);
    for p in props {
        assert_eq!(
            p["fairness"],
            serde_json::json!(["(\\A b \\in BOOLEAN : WF_vars(bump(b)))"]),
            "{}",
            ex.tla
        );
    }
    assert_eq!(ex.report["fairness_in_spec"], true);
    assert!(ex.tla.contains("Spec == Init /\\ [][Next]_vars /\\ Fairness\n"), "{}", ex.tla);
    assert!(ex.tla.contains("reaches_three ==\n    <>((x = 3))\n"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let out = tlc_output_with(&jar, &ex.spec(), &ex.cfg, &[]);
    assert!(out.contains("No error has been found"), "{}", out);
}

/// What a lemma's requires assume is its spec, not a property: `fair_inc()`
/// used only there is not a PROPERTY. A `spec().entails(p)` lemma's
/// `requires spec().entails(c)` is a conjunct of its spec, and a requires
/// that is neither is noted. A rule lemma generic over TempPreds, and one
/// with a non-TempPred parameter, are skipped with a note.
#[test]
fn tla_export_verus_tla_lemma_requires_are_the_spec() {
    let ex = export_code(
        &liveness_counter_with(
            "lift_state(init()).and(always(lift_action(next())))",
            r#"
pub open spec fn fair_inc() -> TempPred<S> { inc().weak_fairness(()) }

pub proof fn reaches(m: TempPred<S>)
    requires
        m.entails(spec()),
        m.entails(fair_inc()),
    ensures
        m.entails(eventually(lift_state(|s: S| s.x == 3))),
{
    admit();
}

pub proof fn reaches_given_fairness()
    requires
        spec().entails(fair_inc()),
        1u8 + 1u8 == 2u8,
    ensures
        spec().entails(eventually(lift_state(|s: S| s.x >= 2))),
{
    admit();
}

pub proof fn trans(m: TempPred<S>, p: TempPred<S>, q: TempPred<S>)
    requires
        m.entails(p),
        m.entails(p.implies(q)),
    ensures
        m.entails(q),
{
    admit();
}

pub proof fn indexed(i: int)
    ensures
        spec().entails(eventually(lift_state(|s: S| s.x == 3))),
{
    admit();
}
"#,
        ),
        "test_crate",
    );
    assert_eq!(ex.report["refusals"], serde_json::json!([]));
    let props = ex.report["properties"].as_array().unwrap();
    let ops: Vec<&str> = props.iter().map(|p| p["operator"].as_str().unwrap()).collect();
    assert_eq!(ops, ["reaches", "reaches_given_fairness"], "{}", ex.tla);
    for p in props {
        assert_eq!(p["fairness"], serde_json::json!(["WF_vars(inc)"]), "{}", ex.tla);
        assert_eq!(p["without_fairness"], false);
    }
    let notes = props[1]["notes"].as_array().unwrap();
    assert!(notes.iter().any(|n| n.as_str().unwrap().contains("read as a conjunct of its spec")));
    // Both take their fairness from fair_inc's body: it is shared.
    assert_eq!(ex.report["fairness_in_spec"], true);
    assert!(ex.tla.contains("Spec == Init /\\ [][Next]_vars /\\ Fairness\n"), "{}", ex.tla);
    let temporal: Vec<&str> = ex.report["temporal_notes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|n| n.as_str().unwrap())
        .collect();
    let has = |s: &str| temporal.iter().any(|n| n.contains(s));
    assert!(has("reaches_given_fairness: a requires clause at"), "{:?}", temporal);
    assert!(has("trans: not exported, it is generic over the TempPred `p`"), "{:?}", temporal);
    assert!(has("indexed: not exported, its parameter `i` is not a TempPred"), "{:?}", temporal);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let out = tlc_output_with(&jar, &ex.spec(), &ex.cfg, &[]);
    assert!(out.contains("No error has been found"), "{}", out);
}

/// A TempPred spec fn another property beside `spec()` reads is a building
/// block of it, not a property: `done()` alone fails in the initial state.
#[test]
fn tla_export_verus_tla_leaves_out_a_property_another_reads() {
    let ex = export_code(
        &liveness_counter_with(
            "lift_state(init()).and(always(lift_action(next()))).and(inc().weak_fairness(()))",
            r#"
pub open spec fn done() -> TempPred<S> { lift_state(|s: S| s.x == 3) }

pub open spec fn reaches_three() -> TempPred<S> { eventually(done()) }
"#,
        ),
        "test_crate",
    );
    assert_eq!(ex.report["refusals"], serde_json::json!([]));
    let props = ex.report["properties"].as_array().unwrap();
    let ops: Vec<(&str, bool)> = props
        .iter()
        .map(|p| (p["operator"].as_str().unwrap(), p["included"].as_bool().unwrap()))
        .collect();
    assert_eq!(ops, [("done", false), ("reaches_three", true)], "{}", ex.tla);
    assert!(
        props[0]["left_out"].as_str().unwrap().starts_with("read by the property reaches_three"),
        "{:?}",
        props[0]
    );
    assert_eq!(props[1]["left_out"], serde_json::Value::Null);
    assert!(ex.cfg.contains("PROPERTIES\n  reaches_three\n"), "{}", ex.cfg);
    assert!(ex.cfg.contains("\\* PROPERTY done is left out"), "{}", ex.cfg);
    assert_eq!(ex.report["fairness_in_spec"], true);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let out = tlc_output_with(&jar, &ex.spec(), &ex.cfg, &[]);
    assert!(out.contains("No error has been found"), "{}", out);
}

/// TLC checks an action formula only as `[][A]_vars` conjoined at the top of
/// a property with no premise, `[]<><<A>>_vars` or `<>[][A]_vars`; a
/// property with one anywhere else is left out of the .cfg with a note,
/// since TLC would refuse it and with it the whole run.
#[test]
fn tla_export_verus_tla_action_formulas_only_where_tlc_checks_them() {
    let ex = export_code(
        &liveness_counter_with(
            "lift_state(init()).and(always(lift_action(next()))).and(inc().weak_fairness(()))",
            r#"
pub open spec fn small_steps() -> ActionPred<S> { |s: S, s_prime: S| s_prime.x <= s.x + 1 }

pub open spec fn steps_and_reaches() -> TempPred<S> {
    always(lift_action(small_steps())).and(eventually(lift_state(|s: S| s.x == 3)))
}

pub open spec fn settles() -> TempPred<S> {
    eventually(always(lift_action(|s: S, s_prime: S| s_prime.x == s.x)))
}

pub open spec fn keeps_incrementing() -> TempPred<S> {
    always(eventually(lift_action(inc().forward(()))))
}

pub open spec fn increments_once() -> TempPred<S> { eventually(lift_action(inc().forward(()))) }

pub proof fn small_steps_given(m: TempPred<S>)
    requires
        m.entails(spec()),
        m.entails(always(lift_state(|s: S| s.x <= 3))),
    ensures
        m.entails(always(lift_action(small_steps()))),
{
    admit();
}

pub proof fn reaches_given_small_steps(m: TempPred<S>)
    requires
        m.entails(spec()),
        m.entails(always(lift_action(small_steps()))),
    ensures
        m.entails(eventually(lift_state(|s: S| s.x == 3))),
{
    admit();
}
"#,
        ),
        "test_crate",
    );
    assert_eq!(ex.report["refusals"], serde_json::json!([]));
    let props = ex.report["properties"].as_array().unwrap();
    let get = |op: &str| props.iter().find(|p| p["operator"] == op).expect(op);
    for op in ["steps_and_reaches", "settles", "keeps_incrementing"] {
        assert_eq!(get(op)["included"], true, "{op}: {:?}", get(op));
    }
    assert_eq!(get("steps_and_reaches")["formula"], "([][small_steps]_vars /\\ <>((x = 3)))");
    assert_eq!(get("keeps_incrementing")["formula"], "[](<><<inc>>_vars)");
    let left_out = |op: &str| {
        assert_eq!(get(op)["included"], false, "{op}: {:?}", get(op));
        assert!(ex.cfg.contains(&format!("\\* PROPERTY {op} is left out")), "{}", ex.cfg);
        get(op)["left_out"].as_str().unwrap().to_string()
    };
    assert!(left_out("increments_once").contains("<><<inc>>_vars"));
    // Its [][A]_vars is the conclusion of `[](x <= 3) => ...`.
    assert!(left_out("small_steps_given").contains("under the premises"));
    // Its [][A]_vars is a premise.
    assert!(left_out("reaches_given_small_steps").contains("[][small_steps]_vars"));
    assert!(
        ex.cfg.contains("PROPERTIES\n  steps_and_reaches\n  settles\n  keeps_incrementing\n"),
        "{}",
        ex.cfg
    );
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let only = |p: &str| {
        ex.cfg
            .replace("  steps_and_reaches\n  settles\n  keeps_incrementing\n", &format!("  {p}\n"))
    };
    for op in ["steps_and_reaches", "settles"] {
        let out = tlc_output_with(&jar, &ex.spec(), &only(op), &[]);
        assert!(out.contains("No error has been found"), "{op}: {}", out);
    }
    // Once x is 3, inc is disabled: TLC checks []<><<inc>>_vars and finds
    // the behaviour that stops incrementing.
    let out = tlc_output_with(&jar, &ex.spec(), &only("keeps_incrementing"), &[]);
    assert!(out.contains("Error: Temporal property keeps_incrementing was violated"), "{}", out);
}

/// A state predicate a temporal property reads is checked by that property
/// only when the property is in the .cfg: one read only by properties left
/// out is checked as an invariant after all, and one an included property
/// reads stays out, the report naming that property.
#[test]
fn tla_export_verus_tla_invariant_read_only_by_left_out_properties() {
    let ex = export_code(
        &liveness_counter_with(
            "lift_state(init()).and(always(lift_action(next()))).and(inc().weak_fairness(()))",
            r#"
pub open spec fn below_three() -> StatePred<S> { |s: S| s.x < 3 }

pub open spec fn three() -> StatePred<S> { |s: S| s.x == 3 }

pub open spec fn reaches_three() -> TempPred<S> { eventually(lift_state(three())) }

pub open spec fn below_then_moving() -> TempPred<S> {
    always(lift_state(below_three()))
        .and(eventually(lift_state(three())))
        .and(eventually(lift_action(inc().forward(()))))
}
"#,
        ),
        "test_crate",
    );
    assert_eq!(ex.report["refusals"], serde_json::json!([]));
    let props = ex.report["properties"].as_array().unwrap();
    let get = |op: &str| props.iter().find(|p| p["operator"] == op).expect(op);
    assert_eq!(get("reaches_three")["included"], true);
    assert_eq!(get("below_then_moving")["included"], false);
    // below_three is read only by below_then_moving, which is left out.
    assert_eq!(names(&ex.report["invariants"]), ["below_three"], "{}", ex.cfg);
    let cands = candidates(&ex.report);
    assert!(cands.contains(&("below_three".to_string(), true)), "{:?}", cands);
    assert!(cands.contains(&("three".to_string(), false)), "{:?}", cands);
    let reason = |f: &str| {
        ex.report["candidates"]
            .as_array()
            .unwrap()
            .iter()
            .find(|c| c["function"].as_str().unwrap().ends_with(&format!("::{f}")))
            .map(|c| c["reason"].as_str().unwrap().to_string())
            .unwrap()
    };
    assert!(
        reason("below_three").starts_with(
            "read only by temporal properties left out of the .cfg (below_then_moving)"
        ),
        "{}",
        reason("below_three")
    );
    // three is read by the included reaches_three too.
    assert!(
        reason("three").starts_with("read by the temporal property reaches_three"),
        "{}",
        reason("three")
    );
    assert!(ex.cfg.contains("INVARIANTS\n  below_three\n"), "{}", ex.cfg);
    assert!(ex.cfg.contains("PROPERTIES\n  reaches_three\n"), "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    // TLC checks it: x reaches 3.
    let out = tlc_output_with(&jar, &ex.spec(), &ex.cfg, &[]);
    assert!(out.contains("Error: Invariant below_three is violated"), "{}", out);
    let out =
        tlc_output_with(&jar, &ex.spec(), &ex.cfg.replace("INVARIANTS\n  below_three\n", ""), &[]);
    assert!(out.contains("No error has been found"), "{}", out);
}

#[test]
fn tla_export_reports_the_type_map_and_the_steps() {
    let ex = export(&fixture("counter.rs"), "test_crate");
    let map = &ex.report["type_map"];
    assert_eq!(map["state"], "test_crate::State");
    assert_eq!(
        map["variables"],
        serde_json::json!([
            {"variable": "x", "field": "x", "label": "x", "typ": {"kind": "int", "rust": "nat"}},
            {"variable": "y", "field": "y", "label": "y", "typ": {"kind": "int", "rust": "nat"}},
        ])
    );
    let step = &map["datatypes"]["test_crate::Step"];
    assert_eq!(step["tagged"], true);
    assert_eq!(step["kind"], "enum");
    assert_eq!(
        names(&serde_json::json!(
            step["variants"]
                .as_array()
                .unwrap()
                .iter()
                .map(|v| v["name"].clone())
                .collect::<Vec<_>>()
        )),
        ["Inc", "Dbl"]
    );
    assert_eq!(map["datatypes"]["test_crate::State"]["tagged"], false);
    assert_eq!(map["datatypes"]["test_crate::State"]["kind"], "struct");
    // `next` is `exists|step: Step| next_step(pre, post, step)`, and
    // `next_step` matches on the step, one transition per arm.
    let steps = &ex.report["steps"];
    assert_eq!(steps["binder"], "step");
    assert_eq!(steps["body"], "next_step(step)");
    assert_eq!(steps["domain"], "({[tag |-> \"Inc\"]} \\cup {[tag |-> \"Dbl\"]})");
    assert_eq!(
        steps["arms"],
        serde_json::json!([
            {"variant": "Inc", "function": "test_crate::t_inc", "operator": "t_inc", "args": []},
            {"variant": "Dbl", "function": "test_crate::t_dbl", "operator": "t_dbl", "args": []},
        ])
    );
    assert_eq!(ex.report["exprs"], serde_json::json!([]));
}

#[test]
fn tla_export_steps_name_the_fields_passed_to_each_transition() {
    let ex = export(&fixture("adder_sync.rs"), "test_crate::Adder");
    let steps = &ex.report["steps"];
    assert_eq!(steps["domain"], "({[tag |-> \"add\", v0 |-> v0__] : v0__ \\in Dom_Step_add_v0})");
    let arms = steps["arms"].as_array().unwrap();
    let add = arms.iter().find(|a| a["variant"] == "add").expect("the add arm");
    assert_eq!(add["operator"], "add");
    assert_eq!(add["args"], serde_json::json!([{"param": "v", "field": "0"}]));
    let layout = &ex.report["type_map"]["datatypes"]["test_crate::Adder::Step"];
    let variant = layout["variants"].as_array().unwrap().iter().find(|v| v["name"] == "add");
    assert_eq!(
        variant.unwrap()["fields"],
        serde_json::json!([{"label": "v0", "name": "0", "typ": {"kind": "int", "rust": "int"}}])
    );
}

/// A model with collections, and expressions in a child module the way
/// verus-tools-mcp's model tools append them.
const EXPR_MODEL: &str = r#"
use vstd::prelude::*;
verus! {
pub enum Role { Idle, Busy { job: nat } }
pub struct Host { pub role: Role, pub log: Seq<u8>, pub seen: Set<int>, pub acks: Map<int, bool>, pub pair: (bool, int) }
pub struct S { pub n: nat, pub hosts: Seq<Host> }
pub open spec fn init(s: S) -> bool { s.n == 0 && s.hosts == Seq::<Host>::empty() }
pub open spec fn next(pre: S, post: S) -> bool { post.n == pre.n + 1 && post.hosts == pre.hosts }
pub open spec fn small(s: S) -> bool { s.n < 3 }
pub open spec fn helper(s: S, i: int) -> bool { 0 <= i < s.hosts.len() ==> s.hosts[i].log.len() < 4 }

pub mod exprs {
    use super::*;
    pub open spec fn cand(s: S) -> bool { forall|i: int| 0 <= i < s.hosts.len() ==> helper(s, i) }
    pub open spec fn unbounded(s: S) -> bool { forall|x: int| x > s.n ==> x > 0 }
    pub open spec fn picked(s: S) -> int { choose|x: int| x == s.n }
    pub open spec fn grew(pre: S, post: S) -> bool { post.n > pre.n && small(pre) }
    pub open spec fn first(s: S) -> Host { s.hosts[0] }
    pub open spec fn via(s: S) -> bool { unbounded(s) && s.n < 7 }
    pub open spec fn modded(s: S) -> bool { (s.n as int) % ((s.n as int) - 5) >= 0 }
    pub open spec fn later(s: S) -> bool { helper(s, 0) && s.n < 9 }
}
}
"#;

#[test]
fn tla_export_exports_named_expressions_in_the_models_names() {
    let src = TempDir::new().expect("temp dir");
    let entry = src.path().join("test.rs");
    std::fs::write(&entry, format!("{}\n{}\n{}\n", FEATURE_PRELUDE, USE_PRELUDE, EXPR_MODEL))
        .unwrap();
    let plain = export_with(&entry, "test_crate", &["--no-verify"]);
    let names = [
        "test_crate::exprs::cand",
        "test_crate::exprs::unbounded",
        "test_crate::exprs::picked",
        "test_crate::exprs::grew",
        "test_crate::exprs::first",
        "test_crate::exprs::via",
        "test_crate::exprs::modded",
        "test_crate::exprs::later",
        "test_crate::exprs::missing",
    ];
    let with = export_with(
        &entry,
        "test_crate",
        &[&format!("-V tla-export-expr={}", names.join(",")), "--no-verify"],
    );
    // The model is exported exactly as without the expressions.
    assert_eq!(plain.tla, with.tla);
    assert_eq!(plain.cfg, with.cfg);
    assert_eq!(plain.report["operators"], with.report["operators"]);
    let exprs = with.report["exprs"].as_array().unwrap();
    assert_eq!(exprs.len(), names.len());
    let entry = |f: &str| {
        exprs
            .iter()
            .find(|e| e["function"] == format!("test_crate::exprs::{f}"))
            .unwrap_or_else(|| panic!("no entry for {}", f))
    };
    let defs_of = |e: &serde_json::Value| -> Vec<String> {
        e["definitions"]
            .as_array()
            .unwrap()
            .iter()
            .map(|d| d.as_str().unwrap().to_string())
            .collect()
    };
    let cand = entry("cand");
    assert_eq!(cand["operator"], "cand");
    assert_eq!(cand["states"], 1);
    assert_eq!(cand["ret"], serde_json::json!({"kind": "bool"}));
    assert_eq!(cand["error"], serde_json::Value::Null);
    assert_eq!(cand["tainted"], false);
    // `helper` is not in the model's module, so it comes with the expression,
    // before it; `small` is, so it does not.
    let defs = defs_of(cand);
    assert_eq!(defs.len(), 2, "{:?}", defs);
    assert!(defs[0].starts_with("helper(i) =="), "{:?}", defs);
    assert!(defs[1].starts_with("cand =="), "{:?}", defs);
    assert!(!defs.iter().any(|d| d.contains("\\*")), "{:?}", defs);
    // An unbounded quantifier is a hole whose constant the model does not
    // declare; a `choose` is refused.
    let unbounded = entry("unbounded");
    assert_eq!(names_of(&unbounded["undeclared"]), ["Dom_int"]);
    assert_eq!(unbounded["holes"].as_array().unwrap().len(), 1);
    let picked = entry("picked");
    assert_eq!(picked["tainted"], true);
    assert_eq!(picked["refusals"].as_array().unwrap().len(), 1);
    assert_eq!(picked["ret"], serde_json::json!({"kind": "int", "rust": "int"}));
    // A pair of states reads the second primed.
    let grew = entry("grew");
    assert_eq!(grew["states"], 2);
    let grew_defs = defs_of(grew);
    assert_eq!(grew_defs.len(), 1, "{:?}", grew_defs);
    assert!(grew_defs[0].contains("(n' > n)"), "{:?}", grew_defs);
    // An entry carries only the operators its own operator reaches: never
    // an earlier entry's hole or refusal it does not call.
    for f in ["grew", "first", "modded", "later"] {
        let e = entry(f);
        let defs = defs_of(e);
        assert!(
            !defs.iter().any(|d| d.contains("Dom_int") || d.contains("Assert(FALSE")),
            "{}: {:?}",
            f,
            defs
        );
        assert_eq!(names_of(&e["undeclared"]), Vec::<String>::new(), "{f}");
        assert_eq!(e["holes"], serde_json::json!([]), "{f}");
        assert_eq!(e["refusals"], serde_json::json!([]), "{f}");
    }
    // One calling an earlier entry's operator carries it, and its hole.
    let via = entry("via");
    let via_defs = defs_of(via);
    assert_eq!(via_defs.len(), 2, "{:?}", via_defs);
    assert!(via_defs[0].starts_with("unbounded =="), "{:?}", via_defs);
    assert_eq!(names_of(&via["undeclared"]), ["Dom_int"]);
    assert_eq!(via["holes"].as_array().unwrap().len(), 1);
    // The Euclidean operators come with the entry that divides, only.
    let modded_defs = defs_of(entry("modded"));
    assert_eq!(modded_defs.len(), 2, "{:?}", modded_defs);
    assert!(modded_defs[0].starts_with("EuclidMod("), "{:?}", modded_defs);
    assert!(modded_defs[1].contains("EuclidMod("), "{:?}", modded_defs);
    for f in ["cand", "grew", "via", "later"] {
        assert!(!defs_of(entry(f)).iter().any(|d| d.contains("Euclid")), "{}", f);
    }
    // `helper` came with `cand`, and comes again with `later`, which calls it.
    let later_defs = defs_of(entry("later"));
    assert_eq!(later_defs.len(), 2, "{:?}", later_defs);
    assert!(later_defs[0].starts_with("helper(i) =="), "{:?}", later_defs);
    // A datatype result is laid out in the type map, with what it holds.
    let first = entry("first");
    assert_eq!(
        first["ret"],
        serde_json::json!({"kind": "datatype", "path": "test_crate::Host", "args": []})
    );
    let dts = &with.report["type_map"]["datatypes"];
    let host = &dts["test_crate::Host"]["variants"][0]["fields"];
    assert_eq!(
        host[1]["typ"],
        serde_json::json!({"kind": "seq", "elem": {"kind": "int", "rust": "u8"}})
    );
    assert_eq!(
        host[2]["typ"],
        serde_json::json!({"kind": "set", "elem": {"kind": "int", "rust": "int"}})
    );
    assert_eq!(
        host[3]["typ"],
        serde_json::json!({"kind": "map", "key": {"kind": "int", "rust": "int"}, "value": {"kind": "bool"}})
    );
    assert_eq!(
        host[4]["typ"],
        serde_json::json!({"kind": "tuple", "elems": [{"kind": "bool"}, {"kind": "int", "rust": "int"}]})
    );
    assert_eq!(dts["test_crate::Role"]["tagged"], true);
    assert_eq!(dts["test_crate::Role"]["variants"][1]["fields"][0]["label"], "job");
    assert!(entry("missing")["error"].as_str().unwrap().contains("no function"));
    let Some(jar) = tla_tools() else { return };
    // Every entry that can be evaluated against the model (no error, no
    // undeclared constant, no refusal) parses in a module extending it,
    // with its definitions in a LET.
    let module = with.module.clone();
    let mut probed = Vec::new();
    for (i, e) in exprs.iter().enumerate() {
        let blocked = !e["error"].is_null()
            || !e["undeclared"].as_array().unwrap().is_empty()
            || e["tainted"] == true;
        if blocked {
            continue;
        }
        let recursive: Vec<&str> =
            e["recursive"].as_array().unwrap().iter().map(|r| r.as_str().unwrap()).collect();
        let recursive = if recursive.is_empty() {
            String::new()
        } else {
            format!("RECURSIVE {}\n", recursive.join(", "))
        };
        let name = format!("Probe{i}");
        let probe = with.dir.path().join("log").join(format!("{name}.tla"));
        std::fs::write(
            &probe,
            format!(
                "---- MODULE {name} ----\nEXTENDS {module}\nC == LET\n{recursive}{}IN {}\n====\n",
                defs_of(e).join(""),
                e["operator"].as_str().unwrap()
            ),
        )
        .unwrap();
        sany(&jar, &probe);
        probed.push(e["function"].as_str().unwrap().to_string());
    }
    assert_eq!(
        probed,
        ["cand", "grew", "first", "modded", "later"]
            .map(|f| format!("test_crate::exprs::{f}"))
            .to_vec()
    );
}

fn names_of(v: &serde_json::Value) -> Vec<String> {
    v.as_array().unwrap().iter().map(|x| x.as_str().unwrap().to_string()).collect()
}

/// Fields whose Rust name is not their record label, and datatypes whose
/// encoding does not say whether they are structs or enums.
const LAYOUTS: &str = r#"
use vstd::prelude::*;
verus! {
pub enum One { Only { x: int } }
pub enum Mark { Set }
pub struct Pt(pub int, pub bool);
pub struct S { pub tag: bool, pub vars: nat, pub one: One, pub mark: Mark, pub pt: Pt, pub o: Option<u8> }
pub open spec fn init(s: S) -> bool {
    s.tag == false && s.vars == 0 && s.one == (One::Only { x: 0 }) && s.mark == Mark::Set
        && s.pt == Pt(0, true) && s.o == Option::<u8>::None
}
pub open spec fn next(pre: S, post: S) -> bool { post == pre }
pub struct T(pub nat, pub bool);
pub open spec fn t_init(t: T) -> bool { t.0 == 0 && t.1 }
pub open spec fn t_next(pre: T, post: T) -> bool { post == pre }
pub mod pos {
    use super::*;
    pub open spec fn init(t: T) -> bool { t_init(t) }
    pub open spec fn next(pre: T, post: T) -> bool { t_next(pre, post) }
}
}
"#;

#[test]
fn tla_export_type_map_names_rust_fields_and_datatype_kinds() {
    let src = TempDir::new().expect("temp dir");
    let entry = src.path().join("test.rs");
    std::fs::write(&entry, format!("{}\n{}\n{}\n", FEATURE_PRELUDE, USE_PRELUDE, LAYOUTS)).unwrap();
    let ex = export_with(&entry, "test_crate", &["--no-verify"]);
    let map = &ex.report["type_map"];
    let vars: Vec<(String, String, String)> = map["variables"]
        .as_array()
        .unwrap()
        .iter()
        .map(|v| {
            let s = |k: &str| v[k].as_str().unwrap().to_string();
            (s("variable"), s("field"), s("label"))
        })
        .collect();
    let v = |a: &str, b: &str, c: &str| (a.to_string(), b.to_string(), c.to_string());
    // A field `tag` is labelled `tag_`, a field `vars` held in `vars_v`: the
    // field is always the Rust name.
    assert_eq!(
        vars,
        [
            v("tag_", "tag", "tag_"),
            v("vars_v", "vars", "vars"),
            v("one", "one", "one"),
            v("mark", "mark", "mark"),
            v("pt", "pt", "pt"),
            v("o", "o", "o"),
        ]
    );
    let dts = &map["datatypes"];
    let kind = |p: &str| dts[p]["kind"].as_str().unwrap_or_else(|| panic!("{}", p)).to_string();
    // An enum with one variant is encoded untagged, as a struct is; its kind
    // says it is written `One::Only { x: 0 }`.
    assert_eq!(dts["test_crate::One"]["tagged"], false);
    assert_eq!(kind("test_crate::One"), "enum");
    assert_eq!(dts["test_crate::One"]["variants"][0]["name"], "Only");
    assert_eq!(dts["test_crate::Mark"]["tagged"], false);
    assert_eq!(kind("test_crate::Mark"), "enum");
    assert!(ex.tla.contains("(mark = [tag |-> \"unit\"])"), "{}", ex.tla);
    assert_eq!(kind("test_crate::Pt"), "struct");
    assert_eq!(dts["test_crate::Pt"]["variants"][0]["positional"], true);
    assert_eq!(kind("test_crate::S"), "struct");
    assert_eq!(kind("core::option::Option"), "enum");
    assert_eq!(dts["core::option::Option"]["tagged"], true);
    // A positional state's fields are `0`, `1`, labelled `v0`, `v1`.
    let ex = export_with(&entry, "test_crate::pos", &["--no-verify"]);
    let vars = &ex.report["type_map"]["variables"];
    assert_eq!(
        vars,
        &serde_json::json!([
            {"variable": "v0", "field": "0", "label": "v0", "typ": {"kind": "int", "rust": "nat"}},
            {"variable": "v1", "field": "1", "label": "v1", "typ": {"kind": "bool"}},
        ])
    );
}

/// Run Verus with `options` on the expression model, expecting it to fail.
fn verus_fails(options: &[&str]) -> String {
    let src = TempDir::new().expect("temp dir");
    let entry = src.path().join("test.rs");
    std::fs::write(&entry, format!("{}\n{}\n{}\n", FEATURE_PRELUDE, USE_PRELUDE, EXPR_MODEL))
        .unwrap();
    let log = format!("--log-dir {}", src.path().join("log").display());
    let mut options = options.to_vec();
    options.push(&log);
    let output = run_verus(&options, src.path(), &entry, true, true);
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert!(!output.status.success(), "{}", stderr);
    stderr
}

#[test]
fn tla_export_expr_needs_tla_export_and_a_value() {
    let stderr = verus_fails(&["-V tla-export-expr=test_crate::exprs::cand", "--no-verify"]);
    assert!(stderr.contains("it needs -V tla-export"), "{}", stderr);
    let stderr = verus_fails(&["-V tla-export=test_crate", "-V tla-export-expr=", "--no-verify"]);
    assert!(stderr.contains("-V tla-export-expr needs spec fn paths"), "{}", stderr);
}

// ─── vstd collections ──────────────────────────────────────────────────

/// A model over the vstd collections: `n` counts to 4, and each step pushes
/// `n` onto `s`, inserts it into `t`, maps it to its square in `m` and adds
/// its parity to `b`, so `s` is `0..n`, `t` its set, `m` the squares on `t`
/// and `b` holds `(n + 1) / 2` zeros and `n / 2` ones. `STEP` assigns the
/// derived fields `d`, `e` and `w` (reading `post`, so a closure reads the
/// primed variables), and `INVARIANTS` are the spec fns TLC checks.
const COLLECTIONS: &str = r#"
use vstd::prelude::*;
use vstd::multiset::Multiset;
verus! {
pub struct State {
    pub s: Seq<int>, pub t: Set<int>, pub m: Map<int, int>, pub b: Multiset<u8>, pub n: nat,
    pub d: Seq<int>, pub e: Set<int>, pub w: Map<int, int>,
}

pub open spec fn init(s: State) -> bool {
    &&& s.s == Seq::<int>::empty() && s.t == Set::<int>::empty() && s.m == Map::<int, int>::empty()
    &&& s.b == Multiset::<u8>::empty() && s.n == 0
    &&& s.d == Seq::<int>::empty() && s.e == Set::<int>::empty() && s.w == Map::<int, int>::empty()
}

pub open spec fn next(pre: State, post: State) -> bool {
    &&& pre.n < 4
    &&& post.s == pre.s.push(pre.n as int)
    &&& post.t == pre.t.insert(pre.n as int)
    &&& post.m == pre.m.insert(pre.n as int, (pre.n * pre.n) as int)
    &&& post.b == pre.b.insert((pre.n % 2) as u8)
    &&& post.n == pre.n + 1
    &&& STEP
}

INVARIANTS
}
"#;

/// A [`COLLECTIONS`] step that leaves the derived fields alone.
const SAME: &str = "post.d == pre.d && post.e == pre.e && post.w == pre.w";

/// Export a [`COLLECTIONS`] model and check it: no refusal and no hole,
/// every invariant in the .cfg, SANY accepts the module, and TLC finds
/// exactly the invariants `violated` violated on the model's 5 states.
fn check_collections(step: &str, invariants: &str, violated: &[&str]) -> Exported {
    let code = COLLECTIONS.replace("STEP", step).replace("INVARIANTS", invariants);
    let ex = export_code(&code, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(ex.report["holes"], serde_json::json!([]), "{}", ex.tla);
    let declared = invariants.matches("pub open spec fn").count();
    assert_eq!(names(&ex.report["invariants"]).len(), declared, "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return ex };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    let mut found = run.violated.clone();
    found.sort();
    found.dedup();
    assert_eq!(found, violated, "{run:?}\n{}", ex.tla);
    assert_eq!(run.distinct, 5, "{run:?}\n{}", ex.tla);
    ex
}

#[test]
fn tla_export_seq_map_is_a_function_over_the_positions() {
    // The closure's index is the Verus index, one below the TLA+ position.
    // The elements are the squares, so `x - i` tells the index from the
    // element (`i - x` differs from `n == 3`).
    let ex = check_collections(
        "post.d == post.s.map_values(|x: int| x + 1) && post.e == pre.e && post.w == pre.w",
        r#"
pub open spec fn indexed(s: State) -> bool {
    &&& s.s.map(|i: int, x: int| x + i) =~= Seq::new(s.n, |i: int| 2 * i)
    &&& s.s.map_values(|x: int| x * x).map(|i: int, x: int| x - i) =~= Seq::new(s.n, |i: int| i * i - i)
}
pub open spec fn values(s: State) -> bool { s.d =~= Seq::new(s.n, |i: int| i + 1) }
"#,
        &[],
    );
    assert!(ex.tla.contains("|-> (LET i == i__ - 1 x == s__[i__] IN (x + i))]"), "{}", ex.tla);
    assert!(ex.tla.contains("(LET s__ == s' IN [i__ \\in 1..Len(s__) |->"), "{}", ex.tla);
}

#[test]
fn tla_export_closure_body_reads_the_post_state() {
    // A closure's body reads the post state as it does in Verus: `post.n`
    // is `n'` inside the comprehension, assigned by an earlier conjunct.
    let ex = check_collections(
        r#"post.d == pre.s.push(pre.n as int).map_values(|x: int| x + post.n)
            && post.e == post.t.filter(|y: int| y + 1 < post.n)
            && post.w == post.m.map_values(|v: int| v + post.n)"#,
        r#"
pub open spec fn shifted(s: State) -> bool { s.d =~= Seq::new(s.n, |i: int| i + s.n) }
pub open spec fn below(s: State) -> bool { s.e =~= Set::new(|x: int| 0 <= x < s.n - 1).unwrap() }
pub open spec fn values(s: State) -> bool { s.w =~= Map::new(s.t, |k: int| k * k + s.n) }
"#,
        &[],
    );
    assert!(ex.tla.contains("(LET x == s__[i__] IN (x + n'))"), "{}", ex.tla);
    assert!(ex.tla.contains("IN ((y + 1) < n'))"), "{}", ex.tla);
    assert!(ex.tla.contains("IN (v + n'))"), "{}", ex.tla);
}

#[test]
fn tla_export_seq_filter_is_selectseq() {
    let ex = check_collections(
        "post.d == post.s.filter(|x: int| x >= 2) && post.e == pre.e && post.w == pre.w",
        r#"
pub open spec fn evens(s: State) -> bool {
    let e = s.s.filter(|x: int| x % 2 == 0);
    e.len() == (s.n + 1) / 2 && forall|i: int| 0 <= i < e.len() ==> e[i] == 2 * i
}
pub open spec fn tail(s: State) -> bool { s.d.len() == (if s.n > 2 { s.n - 2 } else { 0 }) }
"#,
        &[],
    );
    assert!(
        ex.tla.contains("SelectSeq(s', LAMBDA x__2 : (LET x == x__2 IN (x >= 2)))"),
        "{}",
        ex.tla
    );
}

#[test]
fn tla_export_seq_folds_are_recursive_operators() {
    // Folding `push` rebuilds the sequence from the left and reverses it
    // from the right; `wrong_order` expects the left fold to reverse, and
    // TLC finds it violated once `s` has two elements. `seeded` folds from
    // seeds that are no identity, so the seed is seen once, at its end.
    let ex = check_collections(
        SAME,
        r#"
pub open spec fn sum(s: State) -> bool {
    s.s.fold_left(0int, |acc: int, x: int| acc + x) == s.n * (s.n - 1) / 2
}
pub open spec fn left(s: State) -> bool {
    &&& s.s.fold_left(Seq::<int>::empty(), |acc: Seq<int>, x: int| acc.push(x)) =~= s.s
    &&& s.s.fold_left_alt(Seq::<int>::empty(), |acc: Seq<int>, x: int| acc.push(x)) =~= s.s
}
pub open spec fn right(s: State) -> bool {
    let rev = Seq::new(s.n, |i: int| s.n - 1 - i);
    &&& s.s.fold_right(|x: int, acc: Seq<int>| acc.push(x), Seq::<int>::empty()) =~= rev
    &&& s.s.fold_right_alt(|x: int, acc: Seq<int>| acc.push(x), Seq::<int>::empty()) =~= rev
}
pub open spec fn wrong_order(s: State) -> bool {
    s.s.fold_left(Seq::<int>::empty(), |acc: Seq<int>, x: int| acc.push(x))
        =~= Seq::new(s.n, |i: int| s.n - 1 - i)
}
pub open spec fn seeded(s: State) -> bool {
    let rev = Seq::new(s.n, |i: int| s.n - 1 - i);
    &&& s.s.fold_left(10int, |acc: int, x: int| acc + x) == 10 + s.n * (s.n - 1) / 2
    &&& s.s.fold_left(seq![9int], |acc: Seq<int>, x: int| acc.push(x)) =~= seq![9int].add(s.s)
    &&& s.s.fold_right(|x: int, acc: Seq<int>| acc.push(x), seq![9int]) =~= seq![9int].add(rev)
}
"#,
        &["wrong_order"],
    );
    assert!(
        ex.tla.contains("RECURSIVE fold__(_) fold__(k__) == IF k__ = 0 THEN (0) ELSE (LET acc == fold__(k__ - 1) x == s__[k__] IN (acc + x)) IN fold__(Len(s__))"),
        "{}",
        ex.tla
    );
    assert!(ex.tla.contains("IF k__2 > Len(s__2) THEN"), "{}", ex.tla);
}

#[test]
fn tla_export_set_new_is_bounded_by_the_guard_or_the_type() {
    // As a quantifier's binder is: `0 <= x < n` bounds `x` by `0..n-1`,
    // and a `bool` ranges over BOOLEAN. `Set::new` is `Some` of the set.
    let ex = check_collections(
        SAME,
        r#"
pub open spec fn guarded(s: State) -> bool { s.t =~= Set::new(|x: int| 0 <= x < s.n).unwrap() }
pub open spec fn typed(s: State) -> bool { Set::new(|b: bool| b).unwrap() =~= set![true] && s.n >= 0 }
pub open spec fn iset(s: State) -> bool { ISet::new(|x: int| 0 <= x && x < s.n).len() == s.n }
"#,
        &[],
    );
    assert!(
        ex.tla.contains("[tag |-> \"Some\", v0 |-> {x \\in 0..(n) - 1 : ((0 <= x) /\\ (x < n))}]"),
        "{}",
        ex.tla
    );
    assert!(ex.tla.contains("{b_2 \\in BOOLEAN : b_2}"), "{}", ex.tla);
}

const SET_NEW_HOLE: &str = r#"
use vstd::prelude::*;
verus! {
pub struct State { pub t: Set<int>, pub n: nat }

pub open spec fn init(s: State) -> bool { s.t == Set::new(|x: int| x * x == 2 * x).unwrap() && s.n == 0 }

pub open spec fn next(pre: State, post: State) -> bool { pre.n < 2 && post.t == pre.t && post.n == pre.n + 1 }

pub open spec fn roots(s: State) -> bool { s.t =~= set![0int, 2] }
}
"#;

#[test]
fn tla_export_set_new_without_a_bound_leaves_a_hole() {
    // `x * x == 2 * x` bounds nothing and `int` has no finite domain: the
    // comprehension ranges over the hole `Dom_int`, given in the .cfg
    // (`0..3`, which holds both roots, so the set is Verus's `{0, 2}`).
    // Over a hole the set is taken to be finite, so `Set::new` is `Some`.
    let ex = export_code(SET_NEW_HOLE, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    let holes = ex.report["holes"].as_array().unwrap();
    assert_eq!(holes.len(), 1, "{holes:?}");
    assert_eq!(holes[0]["constant"], "Dom_int");
    assert_eq!(holes[0]["variable"], "x");
    assert!(holes[0]["location"].as_str().unwrap().contains("test.rs:"), "{:?}", holes);
    assert!(ex.tla.contains("{x \\in Dom_int : ((x * x) = (2 * x))}"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &format!("{}CONSTANTS Dom_int = {{0, 1, 2, 3}}\n", ex.cfg));
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 3, "{run:?}");
}

#[test]
fn tla_export_set_map_is_a_set_of_images() {
    let ex = check_collections(
        "post.d == pre.d && post.e == post.t.map(|x: int| x * 2) && post.w == pre.w",
        r#"
pub open spec fn doubled(s: State) -> bool {
    s.e =~= Set::new(|y: int| 0 <= y < 2 * s.n && y % 2 == 0).unwrap()
}
pub open spec fn squares(s: State) -> bool { s.t.map(|x: int| x * x) =~= s.m.values() }
"#,
        &[],
    );
    assert!(ex.tla.contains("{(LET x == x__2 IN (x * 2)) : x__2 \\in t'}"), "{}", ex.tla);
}

#[test]
fn tla_export_set_filter_is_a_subset() {
    let ex = check_collections(
        "post.d == pre.d && post.e == post.t.filter(|x: int| x % 2 == 1) && post.w == pre.w",
        r#"
pub open spec fn odds(s: State) -> bool { s.e.len() == s.n / 2 && s.e.subset_of(s.t) }
pub open spec fn small(s: State) -> bool {
    s.t.filter(|x: int| x < 2) =~= Set::new(|x: int| 0 <= x < 2 && x < s.n).unwrap()
}
"#,
        &[],
    );
    assert!(ex.tla.contains("{x__2 \\in t' : (LET x == x__2 IN ((x % 2) = 1))}"), "{}", ex.tla);
}

#[test]
fn tla_export_set_fold_is_a_recursive_operator() {
    // TLC folds in CHOOSE's order, which agrees with every other for the
    // commutative `f` the export accepts: `acc op g(x)` for a commutative
    // and associative `op`, here `+`, `&&` and `insert`.
    let ex = check_collections(
        SAME,
        r#"
pub open spec fn sum(s: State) -> bool { s.t.fold(0int, |acc: int, x: int| acc + x) == s.n * (s.n - 1) / 2 }
pub open spec fn seeded(s: State) -> bool { s.t.fold(10int, |acc: int, x: int| acc + x) == 10 + s.n * (s.n - 1) / 2 }
pub open spec fn count(s: State) -> bool { s.t.fold(0nat, |acc: nat, x: int| acc + 1) == s.n }
pub open spec fn all(s: State) -> bool { s.t.fold(true, |acc: bool, x: int| acc && x < 4) }
pub open spec fn doubled(s: State) -> bool {
    s.t.fold(Set::<int>::empty(), |acc: Set<int>, x: int| acc.insert(2 * x)) =~= s.t.map(|x: int| 2 * x)
}
"#,
        &[],
    );
    assert!(
        ex.tla.contains("RECURSIVE fold__(_) fold__(t__) == IF t__ = {} THEN (0)"),
        "{}",
        ex.tla
    );
    assert!(ex.tla.contains("CHOOSE c__ \\in t__ : TRUE"), "{}", ex.tla);
}

#[test]
fn tla_export_map_new_is_a_function_over_its_domain() {
    // `Map::new(keys, f)` and `IMap::new(p, f)`, whose domain is bounded as
    // a set comprehension's is.
    let ex = check_collections(
        "post.d == pre.d && post.e == pre.e && post.w == Map::new(post.t, |k: int| k + 1)",
        r#"
pub open spec fn squares(s: State) -> bool {
    s.m =~= Map::new(Set::new(|k: int| 0 <= k < s.n).unwrap(), |k: int| k * k)
}
pub open spec fn shifted(s: State) -> bool { s.w.dom() =~= s.t && forall|k: int| s.t.contains(k) ==> s.w[k] == k + 1 }
pub open spec fn imap(s: State) -> bool {
    &&& IMap::new(|k: int| 0 <= k < s.n, |k: int| k * k).dom().len() == s.n
    &&& forall|k: int| #![trigger s.m[k]] 0 <= k < s.n ==> IMap::new(|j: int| 0 <= j < s.n, |j: int| j * j)[k] == s.m[k]
}
"#,
        &[],
    );
    assert!(ex.tla.contains("[k__ \\in t' |-> (LET k == k__ IN (k + 1))]"), "{}", ex.tla);
}

#[test]
fn tla_export_map_values_and_entries_map_the_values() {
    let ex = check_collections(
        "post.d == pre.d && post.e == pre.e && post.w == post.m.map_values(|v: int| v + 1)",
        r#"
pub open spec fn values(s: State) -> bool { s.w =~= Map::new(s.t, |k: int| k * k + 1) }
pub open spec fn entries(s: State) -> bool {
    s.m.map_entries(|k: int, v: int| v - k) =~= Map::new(s.t, |k: int| k * k - k)
}
"#,
        &[],
    );
    assert!(
        ex.tla.contains(
            "(LET m__2 == m' IN [k__ \\in DOMAIN m__2 |-> (LET v == m__2[k__] IN (v + 1))])"
        ),
        "{}",
        ex.tla
    );
}

#[test]
fn tla_export_map_filter_keys_and_restrict_shrink_the_domain() {
    let ex = check_collections(
        "post.d == pre.d && post.e == pre.e && post.w == post.m.filter_keys(|k: int| k % 2 == 0)",
        r#"
pub open spec fn filtered(s: State) -> bool {
    s.w.dom() =~= s.t.filter(|k: int| k % 2 == 0) && forall|k: int| s.w.dom().contains(k) ==> s.w[k] == k * k
}
pub open spec fn restricted(s: State) -> bool {
    &&& s.m.restrict(set![0int, 1]).dom() =~= s.t.intersect(set![0int, 1])
    &&& s.m.remove_keys(set![0int]).dom() =~= s.t.remove(0)
}
"#,
        &[],
    );
    assert!(
        ex.tla.contains("[y__ \\in {k__ \\in DOMAIN m__2 : (LET k == k__ IN ((k % 2) = 0))} |->"),
        "{}",
        ex.tla
    );
    assert!(ex.tla.contains("(DOMAIN m__) \\cap ((({} \\cup {0}) \\cup {1}))"), "{}", ex.tla);
    assert!(ex.tla.contains("(DOMAIN m__2) \\ (({} \\cup {0}))"), "{}", ex.tla);
}

#[test]
fn tla_export_map_union_prefer_right_is_the_right_map_first() {
    // `@@` prefers its left operand, so `a.union_prefer_right(b)` is
    // `b @@ a`.
    let ex = check_collections(
        SAME,
        r#"
pub open spec fn unioned(s: State) -> bool {
    let u = s.m.union_prefer_right(map![0int => 7int, 9int => 9int]);
    &&& u[0] == 7 && u[9] == 9
    &&& u.dom() =~= s.t.union(set![0int, 9])
    &&& (s.n < 2 || u[1] == 1)
}
"#,
        &[],
    );
    assert!(ex.tla.contains(" @@ m)"), "{}", ex.tla);
}

#[test]
fn tla_export_multiset_is_a_function_to_counts() {
    // A multiset is the function from the elements it holds to their
    // counts (never 0), so `=` is its extensional equality.
    let ex = check_collections(
        SAME,
        r#"
pub open spec fn counts(s: State) -> bool {
    &&& s.b.count(0) == (s.n + 1) / 2 && s.b.count(1) == s.n / 2 && s.b.count(7) == 0
    &&& s.b.len() == s.n
    &&& s.b.contains(0) == (s.n > 0)
}
pub open spec fn arithmetic(s: State) -> bool {
    &&& s.b.add(s.b).count(0) == 2 * s.b.count(0) && s.b.add(s.b).len() == 2 * s.n
    &&& s.b.remove(0).count(0) == (if s.n == 0 { 0nat } else { (s.b.count(0) - 1) as nat })
    &&& s.b.insert(5).remove(5) =~= s.b
    &&& s.b.sub(s.b) =~= Multiset::empty()
    &&& s.b.sub(Multiset::singleton(1)).len() == (if s.n >= 2 { (s.n - 1) as nat } else { s.n })
    &&& s.b.subset_of(s.b.insert(3)) && (s.n == 0 || !s.b.insert(3).subset_of(s.b))
    &&& s.b.update(0, 9).count(0) == 9 && s.b.update(1, 0).len() == s.b.count(0)
    &&& s.b.update(1, 0) =~= s.b.filter(|x: u8| x != 1) && !s.b.update(1, 0).contains(1)
    &&& (s.b has 0) == (s.n > 0) && !(s.b has 7)
    &&& s.b <= s.b.insert(3) && (s.n == 0 || !(s.b.insert(3) <= s.b))
    &&& s.b.is_empty() == (s.n == 0) && Multiset::<u8>::empty().is_empty()
}
pub open spec fn conversions(s: State) -> bool {
    &&& Multiset::from_set(set![1u8, 2]).len() == 2
    &&& Multiset::from_map(map![4u8 => 2nat, 6u8 => 0nat]).len() == 2
    &&& Multiset::from_map(map![4u8 => 2nat, 6u8 => 0nat]) =~= Multiset::singleton(4u8).insert(4)
    &&& !Multiset::from_map(map![4u8 => 2nat, 6u8 => 0nat]).contains(6)
    &&& s.b.dom() =~= (if s.n == 0 { Set::empty() } else if s.n == 1 { set![0u8] } else { set![0u8, 1] })
    &&& s.b.filter(|x: u8| x == 1).len() == s.n / 2
    &&& s.s.to_multiset().count(0) == (if s.n == 0 { 0nat } else { 1nat })
    &&& seq![1u8, 1, 2].to_multiset().count(1) == 2 && seq![1u8, 1, 2].to_multiset().len() == 3
    &&& s.s.add(s.s).to_multiset() =~= s.s.to_multiset().add(s.s.to_multiset())
}
"#,
        &[],
    );
    // Its counts are above 0 in TypeOK, and its elements keep their type's
    // range.
    assert!(
        ex.tla.contains("(\\A e__2 \\in DOMAIN b : (b[e__2] > 0 /\\ (0 <= e__2 /\\ e__2 <= 255)))"),
        "{}",
        ex.tla
    );
    assert!(
        ex.tla.contains("(LET m__3 == b IN IF (7) \\in DOMAIN m__3 THEN m__3[7] ELSE 0)"),
        "{}",
        ex.tla
    );
}

#[test]
fn tla_export_seq_to_set_is_the_set_of_its_elements() {
    let ex = check_collections(
        "post.d == pre.d && post.e == post.s.to_set() && post.w == pre.w",
        "pub open spec fn same(s: State) -> bool { s.e =~= s.t && s.s.push(0).to_set() =~= s.t.insert(0) }\n",
        &[],
    );
    assert!(ex.tla.contains("(LET s__ == s' IN {s__[i__] : i__ \\in 1..Len(s__)})"), "{}", ex.tla);
}

#[test]
fn tla_export_seq_flatten_concatenates() {
    let ex = check_collections(
        "post.d == seq![pre.d, seq![pre.n as int]].flatten() && post.e == pre.e && post.w == pre.w",
        r#"
pub open spec fn flat(s: State) -> bool {
    &&& s.d =~= s.s
    &&& seq![s.s, seq![9int], s.s].flatten() =~= s.s.push(9).add(s.s)
    &&& Seq::<Seq<int>>::empty().flatten().len() == 0
}
"#,
        &[],
    );
    assert!(ex.tla.contains("RECURSIVE flat__(_) flat__(k__) == IF k__ > Len(s__) THEN << >> ELSE s__[k__] \\o flat__(k__ + 1)"), "{}", ex.tla);
}

#[test]
fn tla_export_seq_no_duplicates_compares_the_positions() {
    let ex = check_collections(
        SAME,
        "pub open spec fn distinct(s: State) -> bool { s.s.no_duplicates() && (s.n == 0 || !s.s.push(0).no_duplicates()) }\n",
        &[],
    );
    assert!(
        ex.tla.contains("\\A i__, j__ \\in 1..Len(s__) : i__ # j__ => s__[i__] # s__[j__]"),
        "{}",
        ex.tla
    );
}

#[test]
fn tla_export_seq_max_and_min_choose_the_extremum() {
    // vstd's max and min of the empty sequence are 0.
    let ex = check_collections(
        SAME,
        r#"
pub open spec fn extrema(s: State) -> bool {
    &&& s.s.max() == (if s.n == 0 { 0 } else { s.n - 1 })
    &&& s.s.min() == 0
    &&& seq![3int, -2, 5].max() == 5 && seq![3int, -2, 5].min() == -2
}
"#,
        &[],
    );
    assert!(ex.tla.contains("IF Len(s__) = 0 THEN 0 ELSE CHOOSE m__ \\in"), "{}", ex.tla);
}

const CHOOSE_AND_PARAMETER: &str = r#"
use vstd::prelude::*;
use vstd::multiset::Multiset;
verus! {
pub struct State { pub t: Set<int>, pub n: int }

pub open spec fn init(s: State) -> bool { s.t == set![1int, 2] && s.n == 0 }

pub open spec fn total(t: Set<int>, f: spec_fn(int, int) -> int) -> int { t.fold(0, f) }
pub open spec fn members(p: spec_fn(int) -> bool) -> Set<int> { Set::new(p).unwrap() }

pub open spec fn next(pre: State, post: State) -> bool { pre.n < 2 && post.t == pre.t && post.n == pre.n + 1 }

pub open spec fn picked(s: State) -> bool { s.t.contains(s.t.choose()) }
pub open spec fn summed(s: State) -> bool { total(s.t, |a: int, x: int| a + x) == 3 }
pub open spec fn built(s: State) -> bool { members(|x: int| 0 <= x < 2).len() == 2 }
pub open spec fn ordered(s: State) -> bool {
    s.t.fold(Seq::<int>::empty(), |acc: Seq<int>, x: int| acc.push(x)) =~= seq![2int, 1]
}
pub open spec fn clipped(s: State) -> bool {
    set![-1int, 1].fold(0nat, |acc: nat, x: int| (acc + x) as nat) == 0
}
pub open spec fn finite(s: State) -> bool { ISet::new(|x: int| 0 <= x < 2).finite() }
pub open spec fn picked_count(s: State) -> bool { Multiset::singleton(s.n).choose() == s.n }
pub open spec fn small(s: State) -> bool { s.n <= 2 }
}
"#;

#[test]
fn tla_export_refuses_set_choose_and_a_function_parameter() {
    // `Set::choose` and `Multiset::choose` stay refused, as `choose` is:
    // TLC's CHOOSE is one fixed value, and Verus's choice is any value
    // satisfying the predicate, so TLC's verdict would hold for one choice
    // only. So is a `Set::fold` of a function not seen to be commutative
    // (`push`, and a checked cast that `-1` leaves in one order and not in
    // the other): Verus's fold is a choice among the orders, and TLC would
    // hold `ordered` and `clipped` for the one it takes. `ISet::finite` is
    // refused, as every set TLC builds is finite. A fold or `Set::new`
    // given a `spec_fn` parameter has no closure to apply (`total` and
    // `members` are operators of their own); every refusal names its
    // location, and the invariants reaching them are left out of the .cfg.
    let ex = export_code(CHOOSE_AND_PARAMETER, "test_crate");
    let refusals: Vec<(String, String)> = ex.report["refusals"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| (r["what"].as_str().unwrap().into(), r["location"].as_str().unwrap().into()))
        .collect();
    let at = |what: &str| -> Vec<String> {
        refusals.iter().filter(|r| r.0 == what).map(|r| r.1.clone()).collect()
    };
    for (what, count) in [
        ("choose (TLC cannot evaluate it)", 2),
        ("vstd operation given a function that does not reduce to a closure", 1),
        ("vstd operation given a predicate that does not reduce to a closure", 1),
        ("Set::fold of a function not seen to be commutative", 2),
        ("ISet::finite (the export builds only finite sets)", 1),
    ] {
        let at = at(what);
        assert_eq!(at.len(), count, "{what}: {:?}", refusals);
        assert!(at.iter().all(|l| l.contains("test.rs:")), "{what}: {:?}", at);
    }
    assert_eq!(names(&ex.report["invariants"]), ["small"], "{}", ex.cfg);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
}

#[test]
fn tla_export_trace_spec_decodes_a_multiset_as_a_map() {
    // A multiset is logged as a map from its elements to their counts; an
    // element logged with count 0 is not held, as `Multiset::count` has it.
    let ex = export_code(
        r#"
use vstd::prelude::*;
use vstd::multiset::Multiset;
verus! {
pub struct State { pub b: Multiset<u8> }
pub open spec fn init(s: State) -> bool { s.b == Multiset::<u8>::empty() }
pub open spec fn t_add(pre: State, post: State, k: u8) -> bool { k < 3 && post.b == pre.b.insert(k) }
pub open spec fn next(pre: State, post: State) -> bool { exists|k: u8| t_add(pre, post, k) }
}
"#,
        "test_crate",
    );
    let (spec, _, cfg) = trace_spec(&ex);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &spec);
    let log = ex.dir.path().join("t.ndjson");
    let lines = [
        r#"{"module": "State_tla", "export": "test_crate", "state": {"b": []}}"#,
        r#"{"step": "t_add", "params": {"k": 1}, "state": {"b": [[1, 1], [2, 0]]}}"#,
        r#"{"step": "t_add", "params": {"k": 1}, "state": {"b": [[1, 2]]}}"#,
    ];
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 3, "{out}");
    // A count the model does not reach, or an element it does not hold,
    // stops the log at the step observing it.
    for bad in [r#""b": [[1, 3]]"#, r#""b": [[1, 2], [0, 1]]"#] {
        let line = lines[2].replace(r#""b": [[1, 2]]"#, bad);
        std::fs::write(&log, format!("{}\n{}\n{line}\n", lines[0], lines[1])).unwrap();
        let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
        assert_eq!(depth, 2, "{bad}\n{out}");
    }
}

const INFINITE_COLLECTIONS: &str = r#"
use vstd::prelude::*;
use vstd::multiset::Multiset;
verus! {
pub struct State { pub i: ISet<u8>, pub m: IMap<u8, u8>, pub b: Multiset<u8>, pub n: nat }

pub open spec fn init(s: State) -> bool {
    &&& s.i == ISet::<u8>::empty() && s.m == IMap::<u8, u8>::empty()
    &&& s.b == Multiset::<u8>::empty() && s.n == 0
}
pub open spec fn t_add(pre: State, post: State, k: u8) -> bool {
    &&& pre.n < 3 && k < 3
    &&& post.i == pre.i.insert(k)
    &&& post.m == pre.m.insert(k, (k + 1) as u8)
    &&& post.b == pre.b.insert(k)
    &&& post.n == pre.n + 1
}
pub open spec fn next(pre: State, post: State) -> bool { exists|k: u8| t_add(pre, post, k) }

pub open spec fn counted(i: ISet<u8>) -> nat { i.len() }
pub open spec fn members(s: State) -> bool {
    let j = s.i.insert(7);
    &&& forall|x: u8| s.i.contains(x) <==> s.b.contains(x)
    &&& counted(s.i) <= s.n && j.contains(7) && !s.i.remove(0).contains(0)
    &&& forall|k: u8| s.m.contains_key(k) ==> s.i.contains(k) && s.m[k] == k + 1
}
}
"#;

#[test]
fn tla_export_iset_imap_and_multiset_state_fields() {
    // An `ISet` and an `IMap` are a TLA+ set and function wherever the
    // export reads their type, as a `Set` and a `Map` are: TypeOK keeps
    // their elements in range, `type_map` calls them `set` and `map` (and a
    // `Multiset` a `multiset`), a trace logs them as a `Set` and a `Map`,
    // and a `let` or a parameter holding one is a value, not a closure.
    let ex = export_code(INFINITE_COLLECTIONS, "test_crate");
    assert_eq!(ex.report["refusals"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(ex.report["holes"], serde_json::json!([]), "{}", ex.tla);
    assert_eq!(names(&ex.report["invariants"]), ["members"], "{}", ex.cfg);
    let u8_ = serde_json::json!({"kind": "int", "rust": "u8"});
    let typ = |v: &str| {
        let vars = ex.report["type_map"]["variables"].as_array().unwrap();
        vars.iter().find(|x| x["variable"] == v).unwrap()["typ"].clone()
    };
    assert_eq!(typ("i"), serde_json::json!({"kind": "set", "elem": u8_}));
    assert_eq!(typ("m"), serde_json::json!({"kind": "map", "key": u8_, "value": u8_}));
    assert_eq!(typ("b"), serde_json::json!({"kind": "multiset", "elem": u8_}));
    assert!(ex.tla.contains("(\\A e__ \\in i : (0 <= e__ /\\ e__ <= 255))"), "{}", ex.tla);
    assert!(ex.tla.contains("(\\A k__ \\in DOMAIN m : ((0 <= k__ /\\ k__ <= 255)"), "{}", ex.tla);
    let Some(jar) = tla_tools() else { return };
    sany(&jar, &ex.spec());
    // The multisets of at most 3 elements of {0, 1, 2}.
    let run = tlc(&jar, &ex.spec(), &ex.cfg);
    assert_eq!(run.violated, Vec::<String>::new(), "{}", ex.tla);
    assert_eq!(run.distinct, 20, "{run:?}");
    let (spec, _, cfg) = trace_spec(&ex);
    sany(&jar, &spec);
    let log = ex.dir.path().join("t.ndjson");
    let lines = [
        r#"{"module": "State_tla", "export": "test_crate", "state": {"i": [], "m": [], "b": [], "n": 0}}"#,
        r#"{"step": "t_add", "params": {"k": 1}, "state": {"i": [1], "m": [[1, 2]], "b": [[1, 1]], "n": 1}}"#,
        r#"{"step": "t_add", "params": {"k": 1}, "state": {"i": [1], "m": [[1, 2]], "b": [[1, 2]], "n": 2}}"#,
    ];
    std::fs::write(&log, lines.join("\n") + "\n").unwrap();
    let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
    assert_eq!(depth, 3, "{out}");
    // A set element or a map value the model does not reach stops the log
    // at the step observing it.
    for bad in [r#""i": [0, 1]"#, r#""m": [[1, 3]]"#] {
        let line = lines[2]
            .replace(if bad.contains("\"i\"") { r#""i": [1]"# } else { r#""m": [[1, 2]]"# }, bad);
        std::fs::write(&log, format!("{}\n{}\n{line}\n", lines[0], lines[1])).unwrap();
        let (depth, out) = follow(&jar, &spec, &cfg, &log, "");
        assert_eq!(depth, 2, "{bad}\n{out}");
    }
}
