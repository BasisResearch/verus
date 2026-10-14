//! Runtime for dynamic verified coverage (`verus --dyncov`).
//!
//! The `verus!` macro, in dyncov mode, wraps every exec function of a user
//! crate: on entry the wrapper registers a frame and evaluates the lowered
//! `requires` on the real arguments; an `external_body` function also has
//! its `ensures` evaluated on the result; an `assume(e)` in exec code is
//! evaluated where it stands. The outcomes are counted here and [`flush`]
//! writes them as JSON, which `verus-reach --dynamic` joins with the static
//! reachability reports.
//!
//! Nothing here changes the behaviour of the program: a lowered contract
//! runs under `catch_unwind` (a panic inside it counts as `Unknown`), and a
//! violated contract is recorded, not enforced.
//!
//! The lowered contracts are produced by the verus-spec-check engine
//! (vendored in the Verus fork); the executable vocabulary they use lives
//! in [`rt`] (the `verus_spec_check` runtime subset: math integers and
//! sequence helpers) and [`vstd_ext`] (the `exec_spec` companions of the
//! vstd spec types), both ported here without a dependency on vstd.
//!
//! Limits: the frame stack is per thread, so a trusted violation on a
//! spawned thread does not taint the spawner.

#![allow(clippy::all)]

pub mod rt;
pub mod vstd_ext;

/// The method traits the lowered code calls, as anonymous imports: the
/// macro adds `use ::verus_dyncov::prelude::*;` to every instrumented
/// module, and a glob of `_` names binds no name of its own.
pub mod prelude {
    pub use crate::rt::{
        DcFloat as _, DcMapMore as _, DcOption as _, DcResult as _, DcSeqMore as _, DcSetMore as _,
        DcVal as _, DcView as _, VcheckBTreeMapExec as _, VcheckBTreeSetExec as _,
        VcheckMapIndexOwned as _,
    };
    pub use crate::vstd_ext::{
        DeepViewClone as _, ExecSpecEq as _, ExecSpecIndex as _, ExecSpecLen as _,
        ExecSpecMapContainsKey as _, ExecSpecMapDom as _, ExecSpecMapEmpty as _,
        ExecSpecMapGet as _, ExecSpecMapInsert as _, ExecSpecMapRemove as _,
        ExecSpecMultisetCount as _, ExecSpecOptionUnwrap as _, ExecSpecSeqAdd as _,
        ExecSpecSeqContains as _, ExecSpecSeqDropFirst as _, ExecSpecSeqDropLast as _,
        ExecSpecSeqEmpty as _, ExecSpecSeqFirst as _, ExecSpecSeqIndexOf as _,
        ExecSpecSeqIndexOfFirst as _, ExecSpecSeqIndexOfLast as _, ExecSpecSeqIsPrefixOf as _,
        ExecSpecSeqIsSuffixOf as _, ExecSpecSeqLast as _, ExecSpecSeqPush as _,
        ExecSpecSeqSkip as _, ExecSpecSeqSubrange as _, ExecSpecSeqTake as _,
        ExecSpecSeqToMultiset as _, ExecSpecSeqUpdate as _, ExecSpecSetContains as _,
        ExecSpecSetDifference as _, ExecSpecSetEmpty as _, ExecSpecSetInsert as _,
        ExecSpecSetIntersect as _, ExecSpecSetRemove as _, ExecSpecSetUnion as _, ToOwned as _,
        ToRef as _,
    };
}

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::panic::Location;
use std::sync::{Mutex, Once, RwLock};

/// Where a wrapped function is defined: the `file:line` of its `fn`
/// token, which is also how the static report identifies its span.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct FnId {
    pub file: &'static str,
    pub line: u32,
    pub name: &'static str,
}

impl FnId {
    pub fn key(&self) -> String {
        format!("{}:{}:{}", self.file, self.line, self.name)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    /// A verified exec function: its `requires` is checked, its `ensures`
    /// is trusted to Verus.
    Verified,
    /// An `external_body` exec function: both clauses are checked, and a
    /// false `ensures` taints every verified caller on the stack.
    Trusted,
}

/// The outcome of evaluating a clause or a list of clauses.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Verdict {
    True,
    Unknown,
    False,
}

impl Verdict {
    /// Index into a `[true, unknown, false]` triple.
    pub fn index(self) -> usize {
        match self {
            Verdict::True => 0,
            Verdict::Unknown => 1,
            Verdict::False => 2,
        }
    }

    pub fn and(self, other: Verdict) -> Verdict {
        match (self, other) {
            (Verdict::False, _) | (_, Verdict::False) => Verdict::False,
            (Verdict::Unknown, _) | (_, Verdict::Unknown) => Verdict::Unknown,
            _ => Verdict::True,
        }
    }
}

/// What a lowered clause evaluates to: its truth value, or why it could
/// not be evaluated.
pub type Clause = Result<bool, &'static str>;

#[derive(Default, Clone, Debug)]
pub struct FnStats {
    pub calls: u64,
    /// `[true, unknown, false]`
    pub pre: [u64; 3],
    pub post: [u64; 3],
    pub pre_false_sites: BTreeMap<String, u64>,
    pub pre_unknown_reasons: BTreeMap<String, u64>,
    pub post_unknown_reasons: BTreeMap<String, u64>,
    /// Per clause: `"pre:0@<line>"`, `"post:1@<line>"`, ... → `[true, unknown, false]`
    pub clauses: BTreeMap<String, [u64; 3]>,
}

#[derive(Default, Debug)]
pub struct Stats {
    pub functions: BTreeMap<FnId, FnStats>,
    /// Verified frames popped while tainted
    pub tainted: BTreeMap<FnId, u64>,
    /// Trusted `ensures` (keyed by function) and `assume`s (keyed by
    /// `assume@file:line:col`) observed false
    pub trust_violations: BTreeMap<String, u64>,
    pub assume_stats: BTreeMap<String, [u64; 3]>,
    pub assume_unknown_reasons: BTreeMap<String, u64>,
}

static STATS: Mutex<Stats> = Mutex::new(Stats {
    functions: BTreeMap::new(),
    tainted: BTreeMap::new(),
    trust_violations: BTreeMap::new(),
    assume_stats: BTreeMap::new(),
    assume_unknown_reasons: BTreeMap::new(),
});

fn stats() -> std::sync::MutexGuard<'static, Stats> {
    STATS.lock().unwrap_or_else(|e| e.into_inner())
}

struct Frame {
    id: FnId,
    kind: Kind,
    tainted: bool,
}

thread_local! {
    static STACK: RefCell<Vec<Frame>> = const { RefCell::new(Vec::new()) };
}

/// Pops its frame on drop, which also runs during unwinding.
pub struct Guard {
    depth: usize,
    id: FnId,
}

impl Drop for Guard {
    fn drop(&mut self) {
        let tainted = STACK.with(|s| {
            let mut s = s.borrow_mut();
            s.truncate(self.depth + 1);
            s.pop().map_or(false, |f| f.tainted)
        });
        if tainted {
            *stats().tainted.entry(self.id).or_default() += 1;
        }
    }
}

extern "C" {
    fn atexit(callback: extern "C" fn()) -> i32;
}

extern "C" fn flush_at_exit() {
    flush();
}

/// Arranges for the profile to be written when the process exits, even
/// through `std::process::exit`, which skips destructors.
fn install_atexit() {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        // SAFETY: `atexit` is provided by the C runtime std links against,
        // and the callback is a plain `extern "C" fn` that never unwinds
        // (`flush` only writes a file).
        unsafe {
            atexit(flush_at_exit);
        }
    });
}

/// A process that is killed (a test cluster's server, a fuzz target on a
/// timeout) never reaches `atexit`; a background thread flushes the
/// counters every `VERUS_DYNCOV_FLUSH_SECS` seconds (default 1, 0 to
/// disable) so that at most that much of the run is lost, and on SIGTERM
/// it flushes and exits, so a harness that terminates instead of killing
/// loses nothing.
fn install_periodic_flush() {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        if std::env::var("VERUS_DYNCOV_OUT").map_or(true, |v| v.is_empty()) {
            return;
        }
        let secs: u64 =
            std::env::var("VERUS_DYNCOV_FLUSH_SECS").ok().and_then(|s| s.parse().ok()).unwrap_or(1);
        install_term_handler();
        let _ = std::thread::Builder::new().name("dyncov-flush".into()).spawn(move || {
            let tick = std::time::Duration::from_millis(10);
            let mut waited = std::time::Duration::ZERO;
            loop {
                std::thread::sleep(tick);
                waited += tick;
                if TERM_REQUESTED.load(std::sync::atomic::Ordering::SeqCst) {
                    // Asked to stop: write the counters, then die the way
                    // the signal would have made us
                    flush();
                    std::process::exit(143);
                }
                if secs > 0 && waited >= std::time::Duration::from_secs(secs) {
                    waited = std::time::Duration::ZERO;
                    flush();
                }
            }
        });
    });
}

static TERM_REQUESTED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// SIGTERM (Unix) sets a flag the flush thread acts on: a process that a
/// harness stops with SIGTERM instead of SIGKILL keeps its profile. The
/// handler itself only stores the flag, which is async-signal-safe.
#[cfg(unix)]
fn install_term_handler() {
    extern "C" {
        fn signal(signum: i32, handler: usize) -> usize;
    }
    extern "C" fn on_term(_: i32) {
        TERM_REQUESTED.store(true, std::sync::atomic::Ordering::SeqCst);
    }
    const SIGTERM: i32 = 15;
    // SAFETY: `signal` is provided by the C runtime std links against; the
    // handler is an `extern "C" fn` that only stores an atomic.
    unsafe {
        signal(SIGTERM, on_term as usize);
    }
}

#[cfg(not(unix))]
fn install_term_handler() {}

/// Flushes from the calling thread when the counters have been changing
/// and `VERUS_DYNCOV_FLUSH_MS` (default 100) has passed since the last
/// flush: a busy process that is then killed loses at most that much.
fn flush_on_activity() {
    use std::sync::atomic::{AtomicU64, Ordering};
    static CALLS: AtomicU64 = AtomicU64::new(0);
    static LAST: AtomicU64 = AtomicU64::new(0);
    static INTERVAL: RwLock<Option<u64>> = RwLock::new(None);
    if CALLS.fetch_add(1, Ordering::Relaxed) % 16 != 0 {
        return;
    }
    let interval = {
        let cached = *INTERVAL.read().unwrap_or_else(|e| e.into_inner());
        match cached {
            Some(v) => v,
            None => {
                let v = if std::env::var("VERUS_DYNCOV_OUT").map_or(true, |v| v.is_empty()) {
                    0
                } else {
                    std::env::var("VERUS_DYNCOV_FLUSH_MS")
                        .ok()
                        .and_then(|s| s.parse().ok())
                        .unwrap_or(100)
                };
                *INTERVAL.write().unwrap_or_else(|e| e.into_inner()) = Some(v);
                v
            }
        }
    };
    if interval == 0 {
        return;
    }
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0);
    let last = LAST.load(Ordering::Relaxed);
    if now.saturating_sub(last) >= interval
        && LAST.compare_exchange(last, now, Ordering::Relaxed, Ordering::Relaxed).is_ok()
    {
        flush();
    }
}

/// Called on entry to a wrapped function.
pub fn enter(id: FnId, kind: Kind) -> Guard {
    install_atexit();
    install_periodic_flush();
    flush_on_activity();
    stats().functions.entry(id).or_default().calls += 1;
    let depth = STACK.with(|s| {
        let mut s = s.borrow_mut();
        s.push(Frame { id, kind, tainted: false });
        s.len() - 1
    });
    Guard { depth, id }
}

/// The outcome of evaluating a list of clauses.
pub struct Eval {
    pub verdict: Verdict,
    /// `(source line, verdict)` of every clause evaluated, in order
    pub clauses: Vec<(u32, Verdict)>,
    pub unknown_reason: Option<std::borrow::Cow<'static, str>>,
}

impl Eval {
    pub fn unknown(reason: impl Into<std::borrow::Cow<'static, str>>) -> Eval {
        Eval { verdict: Verdict::Unknown, clauses: vec![], unknown_reason: Some(reason.into()) }
    }
}

fn record_clauses(f: &mut FnStats, prefix: &str, eval: &Eval) {
    for (i, (line, v)) in eval.clauses.iter().enumerate() {
        f.clauses.entry(format!("{prefix}:{i}@{line}")).or_default()[v.index()] += 1;
    }
}

/// Records the verdict of the `requires` of the current frame.
pub fn pre(guard: &Guard, eval: Eval, caller: &'static Location<'static>) {
    let mut stats = stats();
    let f = stats.functions.entry(guard.id).or_default();
    f.pre[eval.verdict.index()] += 1;
    record_clauses(f, "pre", &eval);
    match eval.verdict {
        Verdict::False => {
            let site = format!("{}:{}:{}", caller.file(), caller.line(), caller.column());
            *f.pre_false_sites.entry(site).or_default() += 1;
        }
        Verdict::Unknown => {
            let reason = eval.unknown_reason.as_deref().unwrap_or("unknown");
            *f.pre_unknown_reasons.entry(reason.to_string()).or_default() += 1;
        }
        Verdict::True => {}
    }
}

/// Marks every verified frame on this thread's stack as relying on a
/// false assumption.
fn trust_violation(source: String) {
    *stats().trust_violations.entry(source).or_default() += 1;
    STACK.with(|s| {
        for frame in s.borrow_mut().iter_mut() {
            if frame.kind == Kind::Verified {
                frame.tainted = true;
            }
        }
    });
}

/// Records the verdict of the `ensures` of a trusted function.
pub fn trusted_post(guard: &Guard, eval: Eval) {
    {
        let mut stats = stats();
        let f = stats.functions.entry(guard.id).or_default();
        f.post[eval.verdict.index()] += 1;
        record_clauses(f, "post", &eval);
        if eval.verdict == Verdict::Unknown {
            let reason = eval.unknown_reason.as_deref().unwrap_or("unknown");
            *f.post_unknown_reasons.entry(reason.to_string()).or_default() += 1;
        }
    }
    if eval.verdict == Verdict::False {
        trust_violation(guard.id.key());
    }
}

/// Records the verdict of an `assume` in exec code.
pub fn assume(eval: Eval, site: &'static Location<'static>) {
    let key = format!("assume@{}:{}:{}", site.file(), site.line(), site.column());
    {
        let mut stats = stats();
        stats.assume_stats.entry(key.clone()).or_default()[eval.verdict.index()] += 1;
        if eval.verdict == Verdict::Unknown {
            let reason = eval.unknown_reason.as_deref().unwrap_or("unknown");
            *stats.assume_unknown_reasons.entry(format!("{key} {reason}")).or_default() += 1;
        }
    }
    if eval.verdict == Verdict::False {
        trust_violation(key);
    }
}

// ---------------------------------------------------------------------------
// Evaluation of lowered clauses

thread_local! {
    static SILENT: Cell<bool> = const { Cell::new(false) };
}

/// With `VERUS_DYNCOV_DEBUG` set, the message of every distinct panic inside
/// a lowered clause is printed once, to see what became `Unknown` and why.
fn install_panic_hook() {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        let previous = std::panic::take_hook();
        let debug =
            std::env::var("VERUS_DYNCOV_DEBUG").map_or(false, |v| !v.is_empty() && v != "0");
        let seen: Mutex<std::collections::BTreeSet<String>> = Mutex::new(Default::default());
        std::panic::set_hook(Box::new(move |info| {
            if !SILENT.with(|s| s.get()) {
                previous(info);
            } else if debug {
                let msg = info.to_string();
                if seen.lock().unwrap_or_else(|e| e.into_inner()).insert(msg.clone()) {
                    eprintln!("dyncov: unknown: {msg}");
                }
            }
        }));
    });
}

/// Runs lowered clauses under `catch_unwind`. Each clause is its source
/// line and a closure; evaluation stops at the first `False`. A clause
/// that panics (an index out of range, an `int` outside the `i128` model,
/// a `choose` with no witness) makes the whole evaluation `Unknown`.
pub fn eval(clauses: &[(u32, &dyn Fn() -> Clause)]) -> Eval {
    install_panic_hook();
    let was_silent = SILENT.with(|s| s.replace(true));
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut verdicts = Vec::with_capacity(clauses.len());
        let mut verdict = Verdict::True;
        let mut reason = None;
        for (line, clause) in clauses {
            let v = match clause() {
                Ok(true) => Verdict::True,
                Ok(false) => Verdict::False,
                Err(why) => {
                    if reason.is_none() {
                        reason = Some(std::borrow::Cow::Borrowed(why));
                    }
                    Verdict::Unknown
                }
            };
            verdicts.push((*line, v));
            verdict = verdict.and(v);
            if v == Verdict::False {
                break;
            }
        }
        Eval { verdict, clauses: verdicts, unknown_reason: reason }
    }));
    SILENT.with(|s| s.set(was_silent));
    match result {
        Ok(eval) => eval,
        Err(payload) => {
            let reason = if let Some(s) = payload.downcast_ref::<&'static str>() {
                panic_reason(s)
            } else if let Some(s) = payload.downcast_ref::<String>() {
                panic_reason(s)
            } else {
                std::borrow::Cow::Borrowed("panic")
            };
            Eval::unknown(reason)
        }
    }
}

/// A short classification of a panic message from a lowered clause, so
/// that the spec report can group the reasons. A stub's own message
/// (`dyncov: spec fn \`f\`: ...`) is kept, since it names the spec function
/// and says why it has no lowering.
fn panic_reason(msg: &str) -> std::borrow::Cow<'static, str> {
    if let Some(own) = msg.strip_prefix("dyncov: ").filter(|m| m.starts_with("spec fn `")) {
        return std::borrow::Cow::Owned(own.to_string());
    }
    std::borrow::Cow::Borrowed(if msg.contains("uninterpreted") {
        "uninterpreted spec fn"
    } else if msg.contains("does not compile") {
        "spec fn whose lowering does not compile"
    } else if msg.contains("not lowered") {
        "spec fn not lowered"
    } else if msg.contains("i128") || msg.contains("out of range") {
        "int outside the i128 model"
    } else if msg.contains("index out of bounds") || msg.contains("out of bounds") {
        "index out of bounds"
    } else if msg.contains("division by zero") || msg.contains("modulo by zero") {
        "division by zero"
    } else if msg.contains("unwrap") || msg.contains("None") {
        "unwrap on None"
    } else if msg.contains("choose") {
        "choose without a witness"
    } else {
        "panic"
    })
}

/// Runs a snapshot (the `old(x)` clone a trusted wrapper takes of a
/// parameter) under `catch_unwind`.
pub fn snapshot<T>(f: impl FnOnce() -> T) -> Option<T> {
    install_panic_hook();
    let was_silent = SILENT.with(|s| s.replace(true));
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    SILENT.with(|s| s.set(was_silent));
    result.ok()
}

/// Placed in `main` by the macro: writes the profile when `main` returns.
pub struct FlushOnExit;

impl Drop for FlushOnExit {
    fn drop(&mut self) {
        flush();
    }
}

fn json_str(out: &mut String, s: &str) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

fn json_counts(out: &mut String, counts: &BTreeMap<String, u64>) {
    out.push('{');
    for (i, (k, v)) in counts.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        json_str(out, k);
        out.push_str(&format!(":{v}"));
    }
    out.push('}');
}

fn json_triple(out: &mut String, t: &[u64; 3]) {
    out.push_str(&format!("[{},{},{}]", t[0], t[1], t[2]));
}

fn json_triples(out: &mut String, m: &BTreeMap<String, [u64; 3]>) {
    out.push('{');
    for (j, (k, v)) in m.iter().enumerate() {
        if j > 0 {
            out.push(',');
        }
        json_str(out, k);
        out.push(':');
        json_triple(out, v);
    }
    out.push('}');
}

/// The profile as JSON, schema version 2 (see `verus-reach`).
pub fn to_json() -> String {
    let stats = stats();
    let mut out = String::new();
    out.push_str("{\"schema_version\":2,\"functions\":{");
    let mut fns: Vec<(&FnId, &FnStats)> = stats.functions.iter().collect();
    fns.sort_by_key(|(id, _)| id.key());
    for (i, (id, f)) in fns.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        json_str(&mut out, &id.key());
        out.push_str(&format!(":{{\"calls\":{},\"pre\":", f.calls));
        json_triple(&mut out, &f.pre);
        out.push_str(",\"post\":");
        json_triple(&mut out, &f.post);
        out.push_str(",\"pre_false_sites\":");
        json_counts(&mut out, &f.pre_false_sites);
        out.push_str(",\"pre_unknown_reasons\":");
        json_counts(&mut out, &f.pre_unknown_reasons);
        out.push_str(",\"post_unknown_reasons\":");
        json_counts(&mut out, &f.post_unknown_reasons);
        out.push_str(",\"clauses\":");
        json_triples(&mut out, &f.clauses);
        out.push('}');
    }
    out.push_str("},\"tainted\":");
    let tainted: BTreeMap<String, u64> = stats.tainted.iter().map(|(k, v)| (k.key(), *v)).collect();
    json_counts(&mut out, &tainted);
    out.push_str(",\"trust_violations\":");
    json_counts(&mut out, &stats.trust_violations);
    out.push_str(",\"assumes\":");
    json_triples(&mut out, &stats.assume_stats);
    out.push_str(",\"assume_unknown_reasons\":");
    json_counts(&mut out, &stats.assume_unknown_reasons);
    out.push_str("}\n");
    out
}

fn output_path() -> Option<String> {
    static TOKEN: RwLock<Option<String>> = RwLock::new(None);
    let prefix = std::env::var("VERUS_DYNCOV_OUT").ok()?;
    if prefix.is_empty() {
        return None;
    }
    let token = {
        let read = TOKEN.read().unwrap_or_else(|e| e.into_inner());
        match &*read {
            Some(t) => t.clone(),
            None => {
                drop(read);
                let start = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .map(|d| d.as_millis())
                    .unwrap_or(0);
                let t = format!("{}-{}", std::process::id(), start);
                *TOKEN.write().unwrap_or_else(|e| e.into_inner()) = Some(t.clone());
                t
            }
        }
    };
    let path = std::path::Path::new(&prefix);
    Some(if path.is_dir() {
        path.join(format!("dyncov.{token}.json")).display().to_string()
    } else {
        format!("{prefix}.{token}.json")
    })
}

/// Writes the profile to `$VERUS_DYNCOV_OUT.<pid>-<start>.json` (or into
/// that directory, if it names one). Counters are cumulative, so a later
/// flush overwrites an earlier one. Does nothing when the variable is not
/// set.
pub fn flush() {
    let Some(path) = output_path() else { return };
    let json = to_json();
    if let Some(parent) = std::path::Path::new(&path).parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    if let Err(e) = std::fs::write(&path, json) {
        eprintln!("dyncov: could not write {path}: {e}");
    }
}

/// Clears all counters (for tests).
pub fn reset() {
    *stats() = Stats::default();
}

/// A snapshot of the counters (for tests).
pub fn stats_snapshot() -> Stats {
    let s = stats();
    Stats {
        functions: s.functions.clone(),
        tainted: s.tainted.clone(),
        trust_violations: s.trust_violations.clone(),
        assume_stats: s.assume_stats.clone(),
        assume_unknown_reasons: s.assume_unknown_reasons.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // The counters are global; the tests share them and run serially.
    static LOCK: Mutex<()> = Mutex::new(());

    fn id(name: &'static str) -> FnId {
        FnId { file: "t.rs", line: 1, name }
    }

    fn here() -> &'static Location<'static> {
        Location::caller()
    }

    #[test]
    fn verdicts_and_short_circuit() {
        let _l = LOCK.lock().unwrap_or_else(|e| e.into_inner());
        reset();
        let e = eval(&[
            (1, &|| Ok(true)),
            (2, &|| Err("ghost")),
            (3, &|| Ok(false)),
            (4, &|| Ok(true)),
        ]);
        assert_eq!(e.verdict, Verdict::False);
        assert_eq!(e.clauses.len(), 3, "stops at the first false");
        assert_eq!(e.unknown_reason.as_deref(), Some("ghost"));
        let e = eval(&[(1, &|| Ok(true)), (2, &|| Err("ghost"))]);
        assert_eq!(e.verdict, Verdict::Unknown);
        let e = eval(&[(1, &|| {
            let v: Vec<u8> = vec![];
            Ok(v[3] == 0)
        })]);
        assert_eq!(e.verdict, Verdict::Unknown);
        assert_eq!(e.unknown_reason.as_deref(), Some("index out of bounds"));
        let e = eval(&[(1, &|| Ok(rt::__vcheck_int::add(i128::MAX, 1) > 0))]);
        assert_eq!(e.unknown_reason.as_deref(), Some("int outside the i128 model"));
    }

    #[test]
    fn counting_and_taint() {
        let _l = LOCK.lock().unwrap_or_else(|e| e.into_inner());
        reset();
        {
            let outer = enter(id("outer"), Kind::Verified);
            pre(&outer, eval(&[(1, &|| Ok(true))]), here());
            {
                let done = enter(id("done"), Kind::Verified);
                pre(&done, eval(&[(1, &|| Ok(false))]), here());
            }
            {
                let trusted = enter(id("trusted"), Kind::Trusted);
                trusted_post(&trusted, eval(&[(5, &|| Ok(false))]));
            }
            {
                let _after = enter(id("after"), Kind::Verified);
            }
            assume(eval(&[(9, &|| Ok(false))]), here());
        }
        let s = stats_snapshot();
        assert_eq!(s.functions[&id("outer")].calls, 1);
        assert_eq!(s.functions[&id("outer")].pre, [1, 0, 0]);
        assert_eq!(s.functions[&id("done")].pre, [0, 0, 1]);
        assert_eq!(s.functions[&id("done")].pre_false_sites.len(), 1);
        assert_eq!(s.functions[&id("trusted")].post, [0, 0, 1]);
        assert_eq!(s.tainted.get(&id("outer")), Some(&1), "on the stack during the violation");
        assert_eq!(s.tainted.get(&id("done")), None, "returned before it");
        assert_eq!(s.tainted.get(&id("after")), None, "entered after it");
        assert_eq!(s.tainted.get(&id("trusted")), None, "never verified");
        assert_eq!(s.trust_violations.len(), 2);
        assert_eq!(s.assume_stats.len(), 1);
        let json = to_json();
        assert!(json.contains("\"schema_version\":2"));
        assert!(json.contains("t.rs:1:outer"));
    }

    #[test]
    fn unwinding_pops_frames() {
        let _l = LOCK.lock().unwrap_or_else(|e| e.into_inner());
        reset();
        let r = std::panic::catch_unwind(|| {
            let _g = enter(id("panics"), Kind::Verified);
            panic!("boom");
        });
        assert!(r.is_err());
        STACK.with(|s| assert!(s.borrow().is_empty()));
    }
}
