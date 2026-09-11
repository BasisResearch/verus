//! Runtime for dynamic verified coverage (`verus --dyncov`).
//!
//! The `verus!` macro, in dyncov mode, wraps every verified exec function
//! that has a `requires`, every `external_body` exec function that has a
//! `requires` or `ensures`, and every `assume` in exec code, with calls
//! into this module. The wrappers evaluate the lowered contracts on the
//! real arguments and count the outcomes; [`flush`] writes the counters as
//! JSON, which `verus-reach --dynamic` joins with the static reachability
//! reports.
//!
//! Nothing here changes the behaviour of the program: no panic escapes a
//! lowered contract (it is evaluated under `catch_unwind` and a step
//! budget, and either failure counts as `Unknown`), and a violated
//! contract is recorded, not enforced.
//!
//! Limits: the frame stack is per thread, so a trusted violation on a
//! spawned thread does not taint the spawner; `std::process::exit`
//! bypasses [`FlushOnExit`], so call [`flush`] before it; a fuzz target
//! should call [`flush`] periodically.

#![allow(clippy::all)]

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::panic::Location;
use std::sync::{Mutex, Once, RwLock};

mod value;
pub use value::*;

/// Where a wrapped function is defined: the `file:line` of its `fn`
/// token, which is also how the static report identifies its span.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct FnId {
    pub file: &'static str,
    pub line: u32,
    pub name: &'static str,
    /// `std::any::type_name` of a probe declared in the body, for display
    pub path: &'static str,
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

#[derive(Default, Clone, Debug)]
pub struct FnStats {
    pub calls: u64,
    /// `[true, unknown, false]`
    pub pre: [u64; 3],
    pub post: [u64; 3],
    pub pre_false_sites: BTreeMap<String, u64>,
    pub pre_unknown_reasons: BTreeMap<String, u64>,
    pub post_unknown_reasons: BTreeMap<String, u64>,
    /// Per clause: `"pre:0"`, `"post:1"`, ... → `[true, unknown, false]`
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
}

static STATS: Mutex<Stats> = Mutex::new(Stats {
    functions: BTreeMap::new(),
    tainted: BTreeMap::new(),
    trust_violations: BTreeMap::new(),
    assume_stats: BTreeMap::new(),
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

fn current_id() -> Option<FnId> {
    STACK.with(|s| s.borrow().last().map(|f| f.id))
}

/// The outcome of evaluating a list of clauses.
pub struct Eval {
    pub verdict: Verdict,
    /// `(source line, verdict)` of every clause evaluated, in order
    pub clauses: Vec<(u32, Verdict)>,
    pub unknown_reason: Option<&'static str>,
}

impl Eval {
    pub fn unknown(reason: &'static str) -> Eval {
        Eval { verdict: Verdict::Unknown, clauses: vec![], unknown_reason: Some(reason) }
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
            let reason = eval.unknown_reason.unwrap_or("unknown");
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
            let reason = eval.unknown_reason.unwrap_or("unknown");
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
    stats().assume_stats.entry(key.clone()).or_default()[eval.verdict.index()] += 1;
    if eval.verdict == Verdict::False {
        trust_violation(key);
    }
}

// ---------------------------------------------------------------------------
// Evaluation of lowered clauses

thread_local! {
    static SILENT: Cell<bool> = const { Cell::new(false) };
}

fn install_panic_hook() {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !SILENT.with(|s| s.get()) {
                previous(info);
            }
        }));
    });
}

fn budget() -> u64 {
    static BUDGET: RwLock<Option<u64>> = RwLock::new(None);
    if let Some(b) = *BUDGET.read().unwrap_or_else(|e| e.into_inner()) {
        return b;
    }
    let b =
        std::env::var("VERUS_DYNCOV_BUDGET").ok().and_then(|s| s.parse().ok()).unwrap_or(1_000_000);
    *BUDGET.write().unwrap_or_else(|e| e.into_inner()) = Some(b);
    b
}

/// Runs lowered clauses under `catch_unwind` and the step budget. Each
/// clause is its source line and a closure returning a [`Dyn`];
/// evaluation stops at the first `False`.
pub fn eval(clauses: &[(u32, &dyn Fn() -> Dyn)]) -> Eval {
    install_panic_hook();
    set_budget(budget());
    let was_silent = SILENT.with(|s| s.replace(true));
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut verdicts = Vec::with_capacity(clauses.len());
        let mut verdict = Verdict::True;
        let mut reason = None;
        for (line, clause) in clauses {
            let d = clause();
            let v = d.verdict();
            verdicts.push((*line, v));
            if v == Verdict::Unknown && reason.is_none() {
                reason = Some(d.unknown_reason().unwrap_or("not a bool"));
            }
            verdict = verdict.and(v);
            if v == Verdict::False {
                break;
            }
        }
        Eval { verdict, clauses: verdicts, unknown_reason: reason }
    }));
    SILENT.with(|s| s.set(was_silent));
    set_budget(u64::MAX);
    match result {
        Ok(eval) => eval,
        Err(payload) => {
            let reason = if payload.is::<BudgetExceeded>() { "budget exceeded" } else { "panic" };
            Eval::unknown(reason)
        }
    }
}

/// Views a value under the budget and `catch_unwind`, for the snapshots a
/// wrapper takes of its parameters.
pub fn snapshot(f: impl FnOnce() -> Dyn) -> Dyn {
    install_panic_hook();
    set_budget(budget());
    let was_silent = SILENT.with(|s| s.replace(true));
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    SILENT.with(|s| s.set(was_silent));
    set_budget(u64::MAX);
    match result {
        Ok(d) => d,
        Err(payload) => {
            if payload.is::<BudgetExceeded>() {
                Dyn::Unknown("budget exceeded")
            } else {
                Dyn::Unknown("panic")
            }
        }
    }
}

fn int_range(lo: &Dyn, hi: &Dyn) -> Result<(i128, i128), Dyn> {
    match (lo, hi) {
        (Dyn::Int(a), Dyn::Int(b)) => Ok((*a, *b)),
        (Dyn::Unknown(r), _) | (_, Dyn::Unknown(r)) => Err(Dyn::Unknown(r)),
        _ => Err(Dyn::Unknown("non-int quantifier bound")),
    }
}

/// `forall|i| lo <= i < hi ==> body`, by enumeration
pub fn forall1(lo: &Dyn, hi: &Dyn, body: &dyn Fn(Dyn) -> Dyn) -> Dyn {
    let (lo, hi) = match int_range(lo, hi) {
        Ok(r) => r,
        Err(e) => return e,
    };
    let mut result = Verdict::True;
    let mut i = lo;
    while i < hi {
        tick();
        match body(Dyn::Int(i)).verdict() {
            Verdict::False => return Dyn::Bool(false),
            Verdict::Unknown => result = Verdict::Unknown,
            Verdict::True => {}
        }
        i += 1;
    }
    Dyn::from_verdict(result)
}

/// `exists|i| lo <= i < hi && body`, by enumeration
pub fn exists1(lo: &Dyn, hi: &Dyn, body: &dyn Fn(Dyn) -> Dyn) -> Dyn {
    let (lo, hi) = match int_range(lo, hi) {
        Ok(r) => r,
        Err(e) => return e,
    };
    let mut result = Verdict::False;
    let mut i = lo;
    while i < hi {
        tick();
        match body(Dyn::Int(i)).verdict() {
            Verdict::True => return Dyn::Bool(true),
            Verdict::Unknown => result = Verdict::Unknown,
            Verdict::False => {}
        }
        i += 1;
    }
    Dyn::from_verdict(result)
}

/// `Seq::new(len, |i| body)`
pub fn seq_new(len: &Dyn, body: &dyn Fn(Dyn) -> Dyn) -> Dyn {
    let n = match len {
        Dyn::Int(n) if *n >= 0 => *n,
        Dyn::Unknown(r) => return Dyn::Unknown(r),
        _ => return Dyn::Unknown("Seq::new length"),
    };
    let mut items = Vec::new();
    let mut i = 0;
    while i < n {
        tick();
        let v = body(Dyn::Int(i));
        if let Dyn::Unknown(r) = v {
            return Dyn::Unknown(r);
        }
        items.push(v);
        i += 1;
    }
    Dyn::seq(items)
}

/// `s.filter(|x| p)`, `s.map(|x| f)`, `s.map_values(..)`, `s.all(..)`,
/// `s.any(..)` on a `Seq` or `Set`
pub fn seq_closure_op(recv: &Dyn, op: &str, f: &dyn Fn(Dyn) -> Dyn) -> Dyn {
    let (items, is_set) = match recv {
        Dyn::Seq(v) => (v.clone(), false),
        Dyn::Set(v) => (v.clone(), true),
        Dyn::Str(_) => (
            std::rc::Rc::new(match recv.clone() {
                Dyn::Str(s) => s.chars().map(Dyn::Char).collect::<Vec<_>>(),
                _ => unreachable!(),
            }),
            false,
        ),
        Dyn::Unknown(r) => return Dyn::Unknown(r),
        _ => return Dyn::Unknown("closure method on a non-sequence"),
    };
    match op {
        "filter" => {
            let mut out = Vec::new();
            for x in items.iter() {
                tick();
                match f(x.clone()).verdict() {
                    Verdict::True => out.push(x.clone()),
                    Verdict::False => {}
                    Verdict::Unknown => return Dyn::Unknown("filter predicate"),
                }
            }
            if is_set { Dyn::set(out) } else { Dyn::seq(out) }
        }
        "map" | "map_values" => {
            let mut out = Vec::new();
            for x in items.iter() {
                tick();
                let v = f(x.clone());
                if let Dyn::Unknown(r) = v {
                    return Dyn::Unknown(r);
                }
                out.push(v);
            }
            if is_set { Dyn::set(out) } else { Dyn::seq(out) }
        }
        "all" => {
            let mut result = Verdict::True;
            for x in items.iter() {
                tick();
                match f(x.clone()).verdict() {
                    Verdict::False => return Dyn::Bool(false),
                    Verdict::Unknown => result = Verdict::Unknown,
                    Verdict::True => {}
                }
            }
            Dyn::from_verdict(result)
        }
        "any" => {
            let mut result = Verdict::False;
            for x in items.iter() {
                tick();
                match f(x.clone()).verdict() {
                    Verdict::True => return Dyn::Bool(true),
                    Verdict::Unknown => result = Verdict::Unknown,
                    Verdict::False => {}
                }
            }
            Dyn::from_verdict(result)
        }
        _ => Dyn::Unknown("closure method"),
    }
}

// ---------------------------------------------------------------------------
// Lowered spec functions

pub type SpecFn = fn(&[Dyn]) -> Dyn;

/// One lowered spec function: the type it is a method of (empty for a
/// free function), its name, its arity (counting `self`), and the code.
pub struct SpecEntry {
    pub owner: &'static str,
    pub name: &'static str,
    pub arity: usize,
    pub func: SpecFn,
    /// A `View` impl, whose `view` is what `@` means on the owner
    pub is_view: bool,
    /// The declared parameter types by their last path segment (`""` when
    /// not a simple path), used to tell same-named functions apart
    pub params: &'static [&'static str],
}

/// Whether an argument could have the declared type, judging by shape.
fn shape_compatible(decl: &str, arg: &Dyn) -> bool {
    // `Outer<Inner>`: check the outer shape, and the inner one on the
    // first element of a sequence
    if let Some((outer, inner)) = decl.strip_suffix('>').and_then(|d| d.split_once('<')) {
        if !shape_compatible(outer, arg) {
            return false;
        }
        return match arg {
            Dyn::Seq(items) => items.first().map_or(true, |x| shape_compatible(inner, x)),
            _ => true,
        };
    }
    match decl {
        "" | "Self" => true,
        "int" | "nat" | "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "i8" | "i16" | "i32"
        | "i64" | "i128" | "isize" => matches!(arg, Dyn::Int(_)),
        "bool" => matches!(arg, Dyn::Bool(_)),
        "char" => matches!(arg, Dyn::Char(_)),
        "f32" | "f64" => matches!(arg, Dyn::Float(_)),
        "Seq" => matches!(arg, Dyn::Seq(_) | Dyn::Str(_)),
        "Set" => matches!(arg, Dyn::Set(_)),
        "Map" => matches!(arg, Dyn::Map(_)),
        "String" | "str" => matches!(arg, Dyn::Str(_)),
        "Option" | "Result" => matches!(arg, Dyn::Adt(a) if a.type_name.ends_with(decl)),
        d if d.chars().next().map_or(false, |c| c.is_uppercase()) => match arg {
            Dyn::Adt(a) => short_type_name(a.type_name) == d,
            Dyn::Opaque(o) => short_type_name(o.type_name) == d,
            Dyn::Tuple(_) => false,
            _ => true,
        },
        _ => true,
    }
}

/// The lowered spec functions of one `verus!` block.
pub struct Table {
    pub module: &'static str,
    pub entries: &'static [SpecEntry],
}

#[derive(Default)]
struct Registry {
    registered: Vec<usize>,
    /// (owner, name, arity) → (module, func)
    index: BTreeMap<(&'static str, &'static str, usize), Vec<(&'static str, &'static SpecEntry)>>,
}

static REGISTRY: RwLock<Registry> =
    RwLock::new(Registry { registered: Vec::new(), index: BTreeMap::new() });

/// Adds a block's spec functions. Called from a constructor at load time
/// and again (idempotently) from every wrapper of the block, in case the
/// constructor was dropped by the linker.
pub fn register(table: &'static Table) {
    let key = table as *const Table as usize;
    if REGISTRY.read().unwrap_or_else(|e| e.into_inner()).registered.contains(&key) {
        return;
    }
    let mut reg = REGISTRY.write().unwrap_or_else(|e| e.into_inner());
    if reg.registered.contains(&key) {
        return;
    }
    reg.registered.push(key);
    for entry in table.entries {
        reg.index
            .entry((entry.owner, entry.name, entry.arity))
            .or_default()
            .push((table.module, entry));
    }
}

thread_local! {
    static DEPTH: Cell<u32> = const { Cell::new(0) };
}

const MAX_DEPTH: u32 = 200;

/// The lowered functions a call may mean. Several when the name is
/// defined in more than one module and the call site does not say which
/// (the `use` that resolves it is outside the macro's view); the caller
/// then evaluates all of them and accepts a unanimous answer.
fn resolve(
    module: &str,
    qualifier: &str,
    owner: &str,
    name: &'static str,
    args: &[Dyn],
) -> Result<Vec<SpecFn>, &'static str> {
    let arity = args.len();
    let reg = REGISTRY.read().unwrap_or_else(|e| e.into_inner());
    let owner_key: &str = owner;
    // Owner names are compared by their last segment, so look the key up
    // by name and filter
    let candidates: Vec<&(&'static str, &'static SpecEntry)> = reg
        .index
        .iter()
        .filter(|((o, n, a), _)| {
            *n == name && *a == arity && short_type_name(o) == short_type_name(owner_key)
        })
        .flat_map(|(_, v)| v.iter())
        .collect();
    let candidates: Vec<_> = if qualifier.is_empty() {
        candidates
    } else {
        // `m::f(...)`: the qualifier names the module (a suffix of its
        // path) or, for `Type::f`, the owner
        let filtered: Vec<_> = candidates
            .iter()
            .copied()
            .filter(|(m, e)| {
                *m == qualifier
                    || m.ends_with(&format!("::{qualifier}"))
                    || short_type_name(e.owner) == short_type_name(qualifier)
            })
            .collect();
        if filtered.is_empty() { candidates } else { filtered }
    };
    match candidates.len() {
        0 => Err(reason("spec fn not lowered", name)),
        1 => Ok(vec![candidates[0].1.func]),
        _ => {
            let same_module: Vec<_> = candidates.iter().filter(|(m, _)| *m == module).collect();
            if same_module.len() == 1 {
                return Ok(vec![same_module[0].1.func]);
            }
            // The declared parameter types may tell them apart
            let fitting: Vec<_> = candidates
                .iter()
                .filter(|(_, e)| {
                    e.params.len() == args.len()
                        && e.params.iter().zip(args).all(|(d, a)| shape_compatible(d, a))
                })
                .collect();
            if fitting.len() == 1 {
                return Ok(vec![fitting[0].1.func]);
            }
            Ok(candidates.iter().map(|(_, e)| e.func).collect())
        }
    }
}

/// A `&'static str` for an `Unknown` reason that names a function. The
/// set of names is bounded by the program, so interning them is fine.
fn reason(prefix: &str, name: &str) -> &'static str {
    static INTERNED: RwLock<BTreeMap<String, &'static str>> = RwLock::new(BTreeMap::new());
    let key = format!("{prefix}: {name}");
    if let Some(s) = INTERNED.read().unwrap_or_else(|e| e.into_inner()).get(&key) {
        return s;
    }
    let leaked: &'static str = Box::leak(key.clone().into_boxed_str());
    INTERNED.write().unwrap_or_else(|e| e.into_inner()).entry(key).or_insert(leaked)
}

fn call_one(func: SpecFn, args: &[Dyn]) -> Dyn {
    tick();
    let depth = DEPTH.with(|d| d.get());
    if depth >= MAX_DEPTH {
        return Dyn::Unknown("recursion depth");
    }
    DEPTH.with(|d| d.set(depth + 1));
    let r = func(args);
    DEPTH.with(|d| d.set(depth));
    r
}

/// Calls every candidate; the answer stands only if they all agree (the
/// real callee is one of them, so a unanimous answer is its answer).
fn call(funcs: &[SpecFn], name: &'static str, args: &[Dyn]) -> Dyn {
    if let [f] = funcs {
        return call_one(*f, args);
    }
    let mut result: Option<Dyn> = None;
    for f in funcs {
        let r = call_one(*f, args);
        if let Dyn::Unknown(_) = r {
            return Dyn::Unknown(reason("ambiguous spec fn", name));
        }
        match &result {
            None => result = Some(r),
            Some(prev) => {
                if equals(prev, &r) != Verdict::True {
                    return Dyn::Unknown(reason("ambiguous spec fn", name));
                }
            }
        }
    }
    result.unwrap_or(Dyn::Unknown("no candidate"))
}

/// `f(args)` or `q::f(args)` in a spec, from code in module `module`.
pub fn call_spec(
    module: &'static str,
    qualifier: &'static str,
    name: &'static str,
    args: &[Dyn],
) -> Dyn {
    if let Some(Dyn::Unknown(r)) = args.iter().find(|a| matches!(a, Dyn::Unknown(_))) {
        return Dyn::Unknown(r);
    }
    match resolve(module, qualifier, "", name, args) {
        Ok(f) => call(&f, name, args),
        Err(_) => match resolve(module, "", qualifier, name, args) {
            Ok(f) => call(&f, name, args),
            Err(e) => Dyn::Unknown(e),
        },
    }
}

/// `recv.m(args)` in a spec: a vstd method, or a lowered spec method of
/// the receiver's type.
pub fn call_method(module: &'static str, recv: &Dyn, name: &'static str, args: &[Dyn]) -> Dyn {
    if let Some(r) = builtin_method(recv, name, args) {
        return r;
    }
    let owner = match recv {
        Dyn::Adt(adt) => adt.type_name,
        Dyn::Opaque(o) => o.type_name,
        _ => "",
    };
    let mut all = Vec::with_capacity(args.len() + 1);
    all.push(recv.clone());
    all.extend(args.iter().cloned());
    match resolve(module, "", owner, name, &all) {
        Ok(f) => call(&f, name, &all),
        Err(_) if owner.is_empty() => Dyn::Unknown("unsupported method"),
        Err(e) => Dyn::Unknown(e),
    }
}

/// `x@` / `x.view()`: the identity on values that are their own view, the
/// lowered `View` impl of a user type, `Unknown` otherwise.
pub fn view(recv: &Dyn) -> Dyn {
    match recv {
        Dyn::Adt(adt) => {
            let reg = REGISTRY.read().unwrap_or_else(|e| e.into_inner());
            let found = reg
                .index
                .iter()
                .filter(|((o, n, a), _)| {
                    *n == "view" && *a == 1 && short_type_name(o) == short_type_name(adt.type_name)
                })
                .flat_map(|(_, v)| v.iter())
                .find(|(_, e)| e.is_view)
                .map(|(_, e)| e.func);
            drop(reg);
            match found {
                Some(f) => call(&[f], "view", std::slice::from_ref(recv)),
                None => Dyn::Unknown("view not lowered"),
            }
        }
        Dyn::Opaque(_) => Dyn::Unknown("view of an opaque value"),
        other => other.clone(),
    }
}

// ---------------------------------------------------------------------------
// Output

/// Flushes the profile on drop; the wrapped `main` holds one.
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

/// The profile as JSON, schema version 1 (see `verus-reach`).
pub fn to_json() -> String {
    let stats = stats();
    let mut out = String::new();
    out.push_str("{\"schema_version\":1,\"functions\":{");
    let mut fns: Vec<(&FnId, &FnStats)> = stats.functions.iter().collect();
    fns.sort_by_key(|(id, _)| id.key());
    for (i, (id, f)) in fns.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        json_str(&mut out, &id.key());
        out.push_str(":{\"path\":");
        json_str(&mut out, id.path);
        out.push_str(&format!(",\"calls\":{},\"pre\":", f.calls));
        json_triple(&mut out, &f.pre);
        out.push_str(",\"post\":");
        json_triple(&mut out, &f.post);
        out.push_str(",\"pre_false_sites\":");
        json_counts(&mut out, &f.pre_false_sites);
        out.push_str(",\"pre_unknown_reasons\":");
        json_counts(&mut out, &f.pre_unknown_reasons);
        out.push_str(",\"post_unknown_reasons\":");
        json_counts(&mut out, &f.post_unknown_reasons);
        out.push_str(",\"clauses\":{");
        for (j, (k, v)) in f.clauses.iter().enumerate() {
            if j > 0 {
                out.push(',');
            }
            json_str(&mut out, k);
            out.push(':');
            json_triple(&mut out, v);
        }
        out.push_str("}}");
    }
    out.push_str("},\"tainted\":");
    let tainted: BTreeMap<String, u64> = stats.tainted.iter().map(|(k, v)| (k.key(), *v)).collect();
    json_counts(&mut out, &tainted);
    out.push_str(",\"trust_violations\":");
    json_counts(&mut out, &stats.trust_violations);
    out.push_str(",\"assumes\":{");
    for (j, (k, v)) in stats.assume_stats.iter().enumerate() {
        if j > 0 {
            out.push(',');
        }
        json_str(&mut out, k);
        out.push(':');
        json_triple(&mut out, v);
    }
    out.push_str("}}\n");
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
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The counters are global; tests that reset them run one at a time
    fn serial() -> std::sync::MutexGuard<'static, ()> {
        static LOCK: Mutex<()> = Mutex::new(());
        LOCK.lock().unwrap_or_else(|e| e.into_inner())
    }

    fn id(name: &'static str) -> FnId {
        FnId { file: "x.rs", line: 1, name, path: name }
    }

    #[track_caller]
    fn here() -> &'static Location<'static> {
        Location::caller()
    }

    fn t() -> Dyn {
        Dyn::Bool(true)
    }

    fn f() -> Dyn {
        Dyn::Bool(false)
    }

    fn u() -> Dyn {
        Dyn::Unknown("test")
    }

    #[test]
    fn clause_lists_are_three_valued() {
        assert_eq!(eval(&[(0, &t), (0, &t)]).verdict, Verdict::True);
        assert_eq!(eval(&[(0, &t), (0, &u), (0, &t)]).verdict, Verdict::Unknown);
        let e = eval(&[(0, &t), (0, &u), (0, &f)]);
        assert_eq!(e.verdict, Verdict::False);
        assert_eq!(e.clauses, vec![(0, Verdict::True), (0, Verdict::Unknown), (0, Verdict::False)]);
        assert_eq!(eval(&[]).verdict, Verdict::True);
    }

    #[test]
    fn panics_and_budget_are_unknown() {
        let boom = || -> Dyn { panic!("inside a contract") };
        let e = eval(&[(0, &boom)]);
        assert_eq!(e.verdict, Verdict::Unknown);
        assert_eq!(e.unknown_reason, Some("panic"));

        let forever = || -> Dyn {
            loop {
                tick();
            }
        };
        let e = eval(&[(0, &forever)]);
        assert_eq!(e.verdict, Verdict::Unknown);
        assert_eq!(e.unknown_reason, Some("budget exceeded"));
    }

    #[test]
    fn frames_count_calls_and_verdicts() {
        let _serial = serial();
        reset();
        {
            let g = enter(id("a"), Kind::Verified);
            pre(&g, eval(&[(0, &t)]), here());
        }
        {
            let g = enter(id("a"), Kind::Verified);
            pre(&g, eval(&[(0, &f)]), here());
        }
        let s = stats_snapshot();
        let a = &s.functions[&id("a")];
        assert_eq!(a.calls, 2);
        assert_eq!(a.pre, [1, 0, 1]);
        assert_eq!(a.pre_false_sites.len(), 1);
        assert_eq!(a.clauses["pre:0@0"], [1, 0, 1]);
    }

    #[test]
    fn trusted_violation_taints_verified_frames_on_the_stack() {
        let _serial = serial();
        reset();
        {
            let outer = enter(id("outer"), Kind::Verified);
            pre(&outer, eval(&[(0, &t)]), here());
            {
                let mid = enter(id("mid"), Kind::Trusted);
                {
                    let inner = enter(id("inner"), Kind::Verified);
                    pre(&inner, eval(&[(0, &t)]), here());
                    {
                        let trusted = enter(id("trusted"), Kind::Trusted);
                        trusted_post(&trusted, eval(&[(0, &f)]));
                    }
                }
                trusted_post(&mid, eval(&[(0, &t)]));
            }
            // A frame entered after the violation is not tainted
            let later = enter(id("later"), Kind::Verified);
            drop(later);
        }
        let s = stats_snapshot();
        assert_eq!(s.tainted.get(&id("outer")), Some(&1));
        assert_eq!(s.tainted.get(&id("inner")), Some(&1));
        assert_eq!(s.tainted.get(&id("mid")), None);
        assert_eq!(s.tainted.get(&id("later")), None);
        assert_eq!(s.trust_violations["x.rs:1:trusted"], 1);
        assert_eq!(s.functions[&id("trusted")].post, [0, 0, 1]);
    }

    #[test]
    fn assume_violation_taints() {
        let _serial = serial();
        reset();
        {
            let g = enter(id("v"), Kind::Verified);
            assume(eval(&[(0, &u)]), here());
            assume(eval(&[(0, &f)]), here());
            drop(g);
        }
        let s = stats_snapshot();
        assert_eq!(s.tainted.get(&id("v")), Some(&1));
        assert_eq!(s.trust_violations.len(), 1);
        assert_eq!(s.assume_stats.len(), 2);
    }

    #[test]
    fn unwinding_pops_frames() {
        let _serial = serial();
        reset();
        let r = std::panic::catch_unwind(|| {
            let _g = enter(id("p"), Kind::Verified);
            panic!("body panics");
        });
        assert!(r.is_err());
        assert_eq!(STACK.with(|s| s.borrow().len()), 0);
        // The stack is clean: a violation now taints nobody
        trust_violation("nobody".into());
        assert!(stats_snapshot().tainted.is_empty());
    }

    #[test]
    fn json_round_trip_shape() {
        let _serial = serial();
        reset();
        {
            let g = enter(id("j"), Kind::Trusted);
            pre(&g, eval(&[(0, &t), (0, &u)]), here());
            trusted_post(&g, eval(&[(0, &t)]));
        }
        let json = to_json();
        assert!(json.contains("\"schema_version\":1"), "{json}");
        assert!(
            json.contains(
                "\"x.rs:1:j\":{\"path\":\"j\",\"calls\":1,\"pre\":[0,1,0],\"post\":[1,0,0]"
            ),
            "{json}"
        );
        assert!(json.contains("\"pre_unknown_reasons\":{\"test\":1}"), "{json}");
    }

    fn spec_double(args: &[Dyn]) -> Dyn {
        mul(&args[0], &Dyn::Int(2))
    }

    fn spec_view(args: &[Dyn]) -> Dyn {
        field(&args[0], "inner")
    }

    static TABLE: Table = Table {
        module: "test::m",
        entries: &[
            SpecEntry {
                owner: "",
                name: "double",
                arity: 1,
                func: spec_double,
                is_view: false,
                params: &["int"],
            },
            SpecEntry {
                owner: "Foo",
                name: "view",
                arity: 1,
                func: spec_view,
                is_view: true,
                params: &["Foo"],
            },
        ],
    };

    #[test]
    fn registry_resolves_free_fns_methods_and_views() {
        register(&TABLE);
        register(&TABLE);
        assert_eq!(call_spec("test::m", "", "double", &[Dyn::Int(21)]).as_int(), Some(42));
        assert_eq!(call_spec("other", "m", "double", &[Dyn::Int(1)]).as_int(), Some(2));
        assert!(matches!(call_spec("test::m", "", "triple", &[Dyn::Int(1)]), Dyn::Unknown(_)));
        let foo = Dyn::adt("test::m::Foo", "", vec![("inner", Dyn::Int(7))]);
        assert_eq!(view(&foo).as_int(), Some(7));
        assert_eq!(call_method("test::m", &foo, "view", &[]).as_int(), Some(7));
        assert!(matches!(view(&Dyn::adt("Bar", "", vec![])), Dyn::Unknown(_)));
    }

    #[test]
    fn values_and_operators() {
        assert_eq!(
            equals(&Dyn::seq(vec![Dyn::Int(1)]), &Dyn::seq(vec![Dyn::Int(1)])),
            Verdict::True
        );
        assert_eq!(
            equals(&Dyn::Str("ab".into()), &Dyn::seq(vec![Dyn::Char('a'), Dyn::Char('b')])),
            Verdict::True
        );
        assert_eq!(and(f(), || panic!("must not run")).verdict(), Verdict::False);
        assert_eq!(and(u(), || f()).verdict(), Verdict::False);
        assert_eq!(and(u(), || t()).verdict(), Verdict::Unknown);
        assert_eq!(or(t(), || panic!("must not run")).verdict(), Verdict::True);
        assert_eq!(implies(f(), || u()).verdict(), Verdict::True);
        assert!(matches!(add(&Dyn::Int(i128::MAX), &Dyn::Int(1)), Dyn::Unknown("int overflow")));
        assert_eq!(div(&Dyn::Int(-7), &Dyn::Int(2)).as_int(), Some(-4));
        assert_eq!(rem(&Dyn::Int(-7), &Dyn::Int(2)).as_int(), Some(1));
        assert_eq!(cast(&Dyn::Int(300), "u8").as_int(), Some(44));
        let s = Dyn::seq(vec![Dyn::Int(1), Dyn::Int(2), Dyn::Int(3)]);
        assert_eq!(builtin_method(&s, "len", &[]).unwrap().as_int(), Some(3));
        assert_eq!(index(&s, &Dyn::Int(1)).as_int(), Some(2));
        assert!(matches!(index(&s, &Dyn::Int(3)), Dyn::Unknown(_)));
        let sub = builtin_method(&s, "subrange", &[Dyn::Int(1), Dyn::Int(3)]).unwrap();
        assert_eq!(builtin_method(&sub, "len", &[]).unwrap().as_int(), Some(2));
        let v = 7u8.dyn_view();
        assert_eq!(v.as_int(), Some(7));
        assert_eq!(crate::dyncov_view!(&vec![1u8, 2]).describe(), "seq[2]");
        assert_eq!(crate::dyncov_view!(&Some(3u32)).describe(), "Option::Some");
        #[derive(PartialEq, Clone)]
        struct Foreign(u8);
        let a = crate::dyncov_view!(&Foreign(1));
        let b = crate::dyncov_view!(&Foreign(1));
        let c = crate::dyncov_view!(&Foreign(2));
        assert_eq!(equals(&a, &b), Verdict::True);
        assert_eq!(equals(&a, &c), Verdict::False);
        struct Nothing;
        let n = crate::dyncov_view!(&Nothing);
        assert_eq!(equals(&n, &n), Verdict::Unknown);
        let mut b = Vec::new();
        let opt = Dyn::option(Some(Dyn::Int(5)));
        assert_eq!(pat_match(&opt, &Pat::Variant("", "Some", &[Pat::Bind]), &mut b), Some(true));
        assert_eq!(b[0].as_int(), Some(5));
        assert_eq!(pat_match(&opt, &Pat::Variant("", "None", &[]), &mut b), Some(false));
        assert_eq!(pat_match(&Dyn::Int(1), &Pat::Variant("", "None", &[]), &mut b), None);
    }
}
