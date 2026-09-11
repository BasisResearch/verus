//! Dynamic verified coverage (`verus --dyncov`): the instrumented build
//! runs, counts calls and contract verdicts, and the reporter joins the
//! profile with the static report.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

use std::collections::BTreeMap;
use std::path::Path;
use tempfile::TempDir;

/// Builds `code` with `--dyncov` (and `--reach`), runs the binary, and
/// returns the merged profile and the static graph.
fn run_dyncov(code: &str) -> (verus_reach::dyncov::Profile, verus_reach::Graph, TempDir) {
    let tempdir = TempDir::new().expect("temp dir");
    let dir = tempdir.path();
    let entry_file = dir.join("test.rs");
    let code = format!(
        "{}\n{}\n#[allow(unused_imports)] use vstd::prelude::*;\n{}\n",
        FEATURE_PRELUDE, USE_PRELUDE, code
    );
    std::fs::write(&entry_file, code).expect("write source file");
    std::fs::create_dir_all(dir.join("reach")).unwrap();
    std::fs::create_dir_all(dir.join("out")).unwrap();
    let output = run_verus_raw(
        &["--no-verify", "--reach", "reach", "--dyncov", entry_file.to_str().unwrap()],
        dir,
    );
    assert!(
        output.status.success(),
        "verus --dyncov failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let exe = dir.join(if cfg!(target_os = "windows") { "test.exe" } else { "test" });
    let run = std::process::Command::new(&exe)
        .current_dir(dir)
        .env("VERUS_DYNCOV_OUT", dir.join("out"))
        .env("LLVM_PROFILE_FILE", dir.join("test.profraw"))
        .output()
        .expect("run the instrumented binary");
    assert!(run.status.success(), "binary failed:\n{}", String::from_utf8_lossy(&run.stderr));
    let profile = verus_reach::dyncov::load_profiles(&[dir.join("out")]).expect("profile");
    let reports = verus_reach::load(&[dir.join("reach")]).expect("reports");
    let graph = verus_reach::Graph::new(&reports, &verus_reach::Roots::default()).expect("graph");
    (profile, graph, tempdir)
}

/// The profile of the function named `name` (there must be exactly one).
fn fn_profile<'a>(
    profile: &'a verus_reach::dyncov::Profile,
    name: &str,
) -> &'a verus_reach::dyncov::FnProfile {
    let found: Vec<_> =
        profile.functions.iter().filter(|(id, _)| id.ends_with(&format!(":{}", name))).collect();
    assert_eq!(found.len(), 1, "functions named {}: {:?}", name, found);
    found[0].1
}

/// Clause verdict counts of a function, by clause index in order
fn clauses(f: &verus_reach::dyncov::FnProfile, prefix: &str) -> Vec<[u64; 3]> {
    let mut by_index: BTreeMap<usize, [u64; 3]> = BTreeMap::new();
    for (k, v) in &f.clauses {
        if let Some(rest) = k.strip_prefix(&format!("{}:", prefix)) {
            let idx: usize = rest.split('@').next().unwrap().parse().unwrap();
            by_index.insert(idx, *v);
        }
    }
    by_index.into_values().collect()
}

const E2E: &str = verus_code_str! {
    pub open spec fn is_small(x: u64) -> bool { x < 10 }

    pub open spec fn all_small(v: Seq<u64>) -> bool {
        forall|i: int| 0 <= i < v.len() ==> is_small(v[i])
    }

    // (a) always called with a false precondition
    pub fn always_false(x: u64) -> u64
        requires x > 100,
    { x }

    // (b) mixed calls
    pub fn mixed(x: u64) -> u64
        requires is_small(x),
    { x }

    // (c) called only from a trusted function whose ensures is false
    pub fn via_trusted(v: &Vec<u64>) -> u64
        requires all_small(v@), v.len() > 0,
    { v[0] }

    #[verifier::external_body]
    pub fn trusted_lies(v: &Vec<u64>) -> (r: u64)
        ensures r == v@.len() + 1,
    { via_trusted(v) }

    // A verified caller relying on the trusted function
    pub fn relies_on_trusted(v: &Vec<u64>) -> u64
        requires v.len() > 0,
    { trusted_lies(v) }

    pub fn with_assume(x: u64) -> u64 {
        assume(x > 5);
        x
    }

    // (d) a dead trait impl the static walk marks reachable because the
    // type is used
    pub trait Speak { fn speak(&self) -> u64; }
    pub struct Dead;
    impl Speak for Dead {
        fn speak(&self) -> u64 { 7 }
    }

    pub fn use_dead(d: &Dead) -> u64 { let _ = d; 0 }

    fn main() {
        always_false(1);
        always_false(2);
        mixed(1);
        mixed(20);
        let v = vec![1u64, 2, 3];
        relies_on_trusted(&v);
        with_assume(3);
        with_assume(9);
        use_dead(&Dead);
    }
};

#[test]
fn end_to_end_sets_and_taint() {
    let (profile, graph, _dir) = run_dyncov(E2E);
    assert_eq!(fn_profile(&profile, "always_false").pre, [0, 0, 2]);
    assert_eq!(fn_profile(&profile, "mixed").pre, [1, 0, 1]);
    assert_eq!(fn_profile(&profile, "via_trusted").pre, [1, 0, 0]);
    assert_eq!(fn_profile(&profile, "trusted_lies").post, [0, 0, 1]);
    assert_eq!(fn_profile(&profile, "with_assume").calls, 2);
    assert_eq!(profile.assumes.len(), 1);
    assert_eq!(profile.assumes.values().next().unwrap(), &[1, 0, 1]);
    // The trusted ensures taints the verified callers on the stack (main
    // included), not the callee that ran inside the trusted body; the
    // assume taints its own fn (and main)
    let tainted: Vec<&str> = profile.tainted.keys().map(|k| k.as_str()).collect();
    assert_eq!(tainted.len(), 3, "{:?}", tainted);
    assert!(tainted.iter().any(|k| k.ends_with(":relies_on_trusted")));
    assert!(tainted.iter().any(|k| k.ends_with(":with_assume")));
    assert!(tainted.iter().any(|k| k.ends_with(":main")));

    let dynamic = verus_reach::dyncov::Dynamic::new(&graph, &profile);
    assert!(dynamic.unmatched.is_empty(), "{:?}", dynamic.unmatched);
    // D ⊆ S
    for id in &dynamic.called {
        assert!(graph.reachable.contains(id), "{} called but not statically reachable", id);
    }
    let name = |id: &String| graph.nodes[id].name().to_string();
    let t: Vec<String> = dynamic.true_reachable.iter().map(name).collect();
    // main is verified here (it is inside verus!), so its false calls are
    // lowering disagreements, which do not affect coverage
    assert_eq!(
        t,
        vec!["always_false", "mixed", "use_dead", "via_trusted"]
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>(),
        "T = {:?}",
        t
    );
    assert_eq!(dynamic.lowering_disagreements.len(), 3);
    let speak = graph.nodes.values().find(|n| n.name() == "speak").unwrap();
    assert!(graph.is_reachable(speak));
    assert!(!dynamic.called.contains(&speak.id));
    assert_eq!(dynamic.excluded.iter().filter(|(_, e)| e.tainted > 0).count(), 3);
}

#[test]
fn unverified_callers_make_violations() {
    let code = verus_code_str! {
        pub fn needs_small(x: u64) -> u64
            requires x < 10,
        { x }
    }
    .to_string()
        + "\nfn main() { needs_small(3); needs_small(30); needs_small(31); }\n";
    let (profile, graph, _dir) = run_dyncov(&code);
    let f = fn_profile(&profile, "needs_small");
    assert_eq!(f.calls, 3);
    assert_eq!(f.pre, [1, 0, 2]);
    assert_eq!(f.pre_false_sites.len(), 2);
    let dynamic = verus_reach::dyncov::Dynamic::new(&graph, &profile);
    assert!(dynamic.lowering_disagreements.is_empty());
    assert!(dynamic.true_reachable.is_empty());
    let ex = dynamic.excluded.values().next().unwrap();
    assert_eq!(ex.violations.len(), 2);
    assert!(
        matches!(&ex.violations[0], verus_reach::dyncov::Violation::Violation { caller: Some(c), .. } if c.ends_with("main"))
    );
}

const LOWERING: &str = verus_code_str! {
    #[allow(unused_imports)] use vstd::float::FloatBitsProperties;

    pub struct Point { pub x: u64, pub y: u64 }

    impl View for Point {
        type V = (int, int);
        open spec fn view(&self) -> (int, int) { (self.x as int, self.y as int) }
    }

    impl Point {
        pub open spec fn norm1(self) -> int { self.x + self.y }
    }

    pub enum Shape { Dot, Line(u64), Box { w: u64, h: u64 } }

    pub open spec fn area(s: Shape) -> int {
        match s {
            Shape::Dot => 0,
            Shape::Line(n) => n as int,
            Shape::Box { w, h } => w * h,
        }
    }

    pub open spec fn sum_to(n: nat) -> nat
        decreases n,
    {
        if n == 0 { 0 } else { n + sum_to((n - 1) as nat) }
    }

    pub fn views_and_methods(p: &Point, s: Shape) -> u64
        requires
            p@.0 < p@.1,
            p.norm1() == 3,
            area(s) >= 0,
            s matches Shape::Line(n) ==> n > 0,
            s is Line || s is Box,
    { p.x }

    pub fn quantifiers(v: &Vec<u8>) -> usize
        requires
            forall|i: int| 0 <= i < v.len() ==> v[i] < 100,
            exists|i: int| 0 <= i < v@.len() && v@[i] == 1,
            forall|b: u8| b < 255 ==> b + 1 <= 255,
    { v.len() }

    pub fn arithmetic(a: u64, b: u64) -> u64
        requires
            a + b < 20,
            a * b != 7,
            (a as int) - (b as int) >= -10,
            0 <= a <= b < 100,
            a & 1 == 1 || b % 2 == 0,
            sum_to(3) == 6,
    { a }

    pub fn old_and_mut(p: &mut Point)
        requires old(p).x < 1000,
    { p.x = p.x + 1; }

    #[verifier::external_body]
    pub fn trusted_mut(p: &mut Point)
        ensures final(p).x == old(p).x + 1, final(p).y == old(p).y,
    { p.x = p.x + 1; }

    #[verifier::external_body]
    pub fn trusted_ret(v: &Vec<u64>) -> (r: (Option<u64>, usize))
        ensures r.1 == v@.len(), r.0 is Some ==> v.len() > 0, r.0 matches Some(x) ==> x == v[0],
    { (v.first().copied(), v.len()) }

    pub fn overflow(a: u64) -> u64
        requires a + 170141183460469231731687303715884105727 < 1,
    { a }

    pub fn deque_is_opaque(v: &std::collections::VecDeque<u64>, w: &std::collections::VecDeque<u64>) -> usize
        requires v == w, v.len() < 100,
    { v.len() }

    pub fn strings(s: &str, t: &Vec<char>) -> usize
        requires s@.len() == 2, s@[0] == 'a', t@.len() > 0 ==> t@[0] == 'x',
    { s.len() }

    pub fn floats(x: f64) -> bool
        requires x.is_finite_spec(), !x.is_sign_negative_spec(),
    { true }

    fn main() {
        let p = Point { x: 1, y: 2 };
        views_and_methods(&p, Shape::Line(3));
        views_and_methods(&p, Shape::Box { w: 2, h: 2 });
        views_and_methods(&p, Shape::Dot);
        quantifiers(&vec![1u8, 2, 3]);
        quantifiers(&vec![2u8, 200]);
        arithmetic(1, 3);
        arithmetic(3, 4);
        let mut q = Point { x: 5, y: 6 };
        old_and_mut(&mut q);
        trusted_mut(&mut q);
        trusted_ret(&vec![4u64, 5]);
        trusted_ret(&vec![]);
        overflow(1);
        let d = std::collections::VecDeque::from(vec![1u64]);
        deque_is_opaque(&d, &d);
        strings("ab", &vec!['x']);
        strings("abc", &vec![]);
        floats(1.5);
        floats(-1.5);
    }
};

#[test]
fn lowering_verdicts() {
    let (profile, _graph, _dir) = run_dyncov(LOWERING);
    let f = fn_profile(&profile, "views_and_methods");
    // Line(3): all hold. Box: `matches` antecedent false, holds. Dot: last clause false.
    assert_eq!(f.pre, [2, 0, 1], "{:?}", f.pre_unknown_reasons);
    assert_eq!(clauses(f, "pre"), vec![[3, 0, 0], [3, 0, 0], [3, 0, 0], [3, 0, 0], [2, 0, 1]]);

    let f = fn_profile(&profile, "quantifiers");
    assert_eq!(f.pre, [1, 0, 1], "{:?}", f.pre_unknown_reasons);
    assert_eq!(clauses(f, "pre"), vec![[1, 0, 1], [1, 0, 0], [1, 0, 0]]);

    let f = fn_profile(&profile, "arithmetic");
    // (1,3): 4<20, 3!=7, -2>=-10, 0<=1<=3<100, 1&1==1, 6==6. (3,4): 12!=7 ok, but 3&1==1 ok too... all hold
    assert_eq!(f.pre, [2, 0, 0], "{:?} {:?}", f.pre_unknown_reasons, clauses(f, "pre"));

    assert_eq!(fn_profile(&profile, "old_and_mut").pre, [1, 0, 0]);
    let f = fn_profile(&profile, "trusted_mut");
    assert_eq!(f.post, [1, 0, 0], "{:?}", f.post_unknown_reasons);
    let f = fn_profile(&profile, "trusted_ret");
    assert_eq!(f.post, [2, 0, 0], "{:?}", f.post_unknown_reasons);

    let f = fn_profile(&profile, "overflow");
    assert_eq!(f.pre, [0, 1, 0]);
    assert_eq!(f.pre_unknown_reasons.keys().next().map(String::as_str), Some("int overflow"));

    let f = fn_profile(&profile, "deque_is_opaque");
    // VecDeque has a model (a Seq), so `v == w` is decided
    assert_eq!(f.pre, [1, 0, 0], "{:?}", f.pre_unknown_reasons);

    let f = fn_profile(&profile, "strings");
    assert_eq!(f.pre, [1, 0, 1], "{:?}", f.pre_unknown_reasons);

    let f = fn_profile(&profile, "floats");
    assert_eq!(f.pre, [1, 0, 1], "{:?}", f.pre_unknown_reasons);
}

const UNKNOWNS: &str = verus_code_str! {
    pub uninterp spec fn oracle(x: u64) -> bool;

    pub struct Opaque(pub u64);

    pub fn calls_uninterp(x: u64) -> u64
        requires oracle(x),
    { x }

    pub fn unbounded(x: u64) -> u64
        requires forall|y: u64| y > x ==> y > 0,
    { x }

    pub fn ghost_param(x: u64, Ghost(g): Ghost<u64>) -> u64
        requires g < 10, x < 10,
    { x }

    pub fn choose_it(x: u64) -> u64
        requires (choose|y: u64| y > x) > x,
    { x }

    pub fn budget(v: &Vec<u64>) -> usize
        requires forall|i: int, j: int| 0 <= i < 100000 && 0 <= j < 100000 ==> i + j >= 0,
    { v.len() }

    pub fn panics_inside(v: &Vec<u64>) -> usize
        requires v@.subrange(5, 2).len() == 0,
    { v.len() }

    fn main() {
        calls_uninterp(1);
        unbounded(1);
        ghost_param(1, Ghost(2));
        choose_it(1);
        budget(&vec![]);
        panics_inside(&vec![]);
    }
};

#[test]
fn unsupported_constructs_are_unknown_not_errors() {
    let (profile, graph, _dir) = run_dyncov(UNKNOWNS);
    for name in
        ["calls_uninterp", "unbounded", "ghost_param", "choose_it", "budget", "panics_inside"]
    {
        let f = fn_profile(&profile, name);
        assert_eq!(f.calls, 1, "{}", name);
        assert_eq!(f.pre, [0, 1, 0], "{}: {:?}", name, f.pre_unknown_reasons);
    }
    assert!(fn_profile(&profile, "budget").pre_unknown_reasons.contains_key("budget exceeded"));
    assert!(
        fn_profile(&profile, "unbounded").pre_unknown_reasons.contains_key("unbounded quantifier")
    );
    // Unknown counts as covered
    let dynamic = verus_reach::dyncov::Dynamic::new(&graph, &profile);
    assert_eq!(dynamic.true_reachable.len(), 7, "{:?}", dynamic.true_reachable);
}

const SHAPES: &str = verus_code_str! {
    pub struct Counter { pub n: u64 }

    impl Counter {
        pub fn bump(&mut self, by: u64) -> (r: u64)
            requires old(self).n + by < 1000,
            ensures r == old(self).n + by,
        {
            self.n = self.n + by;
            if by == 0 { return self.n; }
            self.n
        }

        pub fn consume(self) -> u64
            requires self.n < 1000,
        { self.n }
    }

    pub trait Named {
        fn name(&self) -> u64
            requires true;
        fn twice(&self) -> u64
            requires true,
        { self.name() * 2 }
    }

    impl Named for Counter {
        fn name(&self) -> u64 { self.n }
    }

    pub fn generic<T: Copy>(x: T, n: u64) -> T
        requires n < 5,
    { let _ = n; x }

    pub fn early_return(x: u64) -> Result<u64, u64>
        requires x < 100,
    {
        if x == 0 { return Err(0); }
        let y = if x > 50 { Err(x)? } else { x };
        Ok(y)
    }

    pub fn returns_ref<'a>(v: &'a Vec<u64>) -> &'a u64
        requires v.len() > 0,
    { &v[0] }

    pub unsafe fn unsafe_fn(x: u64) -> u64
        requires x < 10,
    { x }

    fn main() {
        let mut c = Counter { n: 1 };
        c.bump(2);
        c.bump(0);
        c.twice();
        c.consume();
        generic(1u8, 1);
        generic("s", 9);
        let _ = early_return(0);
        let _ = early_return(70);
        let _ = early_return(7);
        returns_ref(&vec![1]);
        unsafe { unsafe_fn(5); }
    }
};

#[test]
fn wrapper_shapes() {
    let (profile, _graph, _dir) = run_dyncov(SHAPES);
    assert_eq!(fn_profile(&profile, "bump").pre, [2, 0, 0]);
    assert_eq!(fn_profile(&profile, "consume").pre, [1, 0, 0]);
    assert_eq!(fn_profile(&profile, "twice").pre, [1, 0, 0]);
    assert_eq!(fn_profile(&profile, "name").calls, 1);
    assert_eq!(fn_profile(&profile, "generic").pre, [1, 0, 1]);
    assert_eq!(fn_profile(&profile, "early_return").pre, [3, 0, 0]);
    assert_eq!(fn_profile(&profile, "returns_ref").pre, [1, 0, 0]);
    let f = fn_profile(&profile, "unsafe_fn");
    assert_eq!(f.calls, 1);
}

#[test]
fn reporter_end_to_end() {
    let (_profile, _graph, dir) = run_dyncov(E2E);
    let bin = {
        let current_exe = std::env::current_exe().unwrap();
        let target_path = current_exe.parent().unwrap().parent().unwrap();
        target_path.join("verus-reach")
    };
    let out = std::process::Command::new(&bin)
        .args(["--dynamic", "out", "reach"])
        .current_dir(dir.path())
        .output()
        .expect("run verus-reach");
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains("true verified reachable (T):             4  (50% of V)"), "{}", text);
    assert!(text.contains("LOWERING DISAGREEMENT"), "{}", text);
    assert!(!out.status.success(), "lowering disagreements fail the run");
    let lcov = std::process::Command::new(&bin)
        .args(["--dynamic", "out", "--lcov", "--only-verified-exec", "reach"])
        .current_dir(dir.path())
        .output()
        .expect("run verus-reach");
    let lcov = String::from_utf8_lossy(&lcov.stdout);
    assert!(lcov.contains("FNDA:0,test(bin)::always_false\n"), "{}", lcov);
    assert!(lcov.contains("FNDA:1,test(bin)::via_trusted\n"), "{}", lcov);
    assert!(lcov.contains("BRDA:"), "{}", lcov);
    let diff = std::process::Command::new(&bin)
        .args(["--dynamic", "out", "--diff", "reach"])
        .current_dir(dir.path())
        .output()
        .expect("run verus-reach");
    let diff = String::from_utf8_lossy(&diff.stdout);
    assert!(diff.contains("D \\ T, tainted: 3"), "{}", diff);
    assert!(diff.contains("speak"), "{}", diff);
    let _ = Path::new("");
}
