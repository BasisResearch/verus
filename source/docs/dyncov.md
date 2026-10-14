# Dynamic verified coverage (`verus --dyncov`)

The static check (`verus --reach DIR` and `verus-reach`) reports which
verified exec functions are *reachable* from `main`. It over-approximates:
a function counts as covered if any call path exists, whether or not the
path is taken, and whether or not the function's precondition holds on the
inputs the program actually passes. `dyncov` is the dynamic complement: the
program is built with its contracts lowered to executable code, run on a
workload, and the result is the set of *true verified reachable*
functions, those that ran, whose `requires` held on every call, and whose
proof did not rely on a trusted assumption that was observed false.

## Running it

```
verus --dyncov [--no-verify] main.rs        # or: cargo verus build -- --dyncov --no-verify
VERUS_DYNCOV_OUT=profiles/ LLVM_PROFILE_FILE=llvm/%p.profraw ./main
verus-reach --dynamic profiles/ REACH_DIR   # summary; add --diff, --spec-report, --lcov, --html DIR
```

`--dyncov` compiles like `--compile`, with `--cfg verus_dyncov` for the
`verus!` macro and `-C instrument-coverage -Z coverage-options=branch` for
LLVM. Verification is not rerun, so `--no-verify` is the usual companion.
Pass `--reach DIR` on the same run (or an earlier one on the same sources)
to get the static reports the reporter needs. With cargo, use
`--fwd-verus-args-to roots` so that dependencies (vstd) are not asked for
reports.

The instrumented code refers to its runtime as `::vstd::dyncov`, the
`verus_dyncov` crate (`source/dyncov`, plain std Rust) that this fork's
vstd re-exports, so a crate needs nothing beyond vstd itself; the
re-export is inert in every other build. A crate that takes vstd from
crates.io must build with the fork's vstd and `verus!` macro instead, for
instance with cargo's `--config` patches, which leave `Cargo.toml` alone:

```
cargo verus build --fwd-verus-args-to roots \
  --config 'patch.crates-io.vstd.path="<verus checkout>/source/vstd"' \
  --config 'patch.crates-io.verus_builtin.path="<verus checkout>/source/builtin"' \
  --config 'patch.crates-io.verus_builtin_macros.path="<verus checkout>/source/builtin_macros"' \
  --config 'patch.crates-io.verus_state_machines_macros.path="<verus checkout>/source/state_machines_macros"' \
  --lib --bins -- --reach DIR --dyncov --no-verify
```

(`git = "https://github.com/BasisResearch/verus", rev = "<sha>"` in place
of `path` works too.) A standalone file gets the runtime from the Verus
build directory, where `vargo build` installs it beside vstd.

When the workload is a test suite, build the tests the same way
(`cargo verus build --tests -- --reach DIR --dyncov --no-verify`): the
test crates then write their own reports (`<crate>.test-<root>.json`),
whose harness `main` roots the static graph at the tests, so that a
function the tests call is in S as well as in D.

The instrumented program writes one JSON profile per process to
`$VERUS_DYNCOV_OUT` (an existing directory, which gets `dyncov.<pid>-<start>.json`,
or else a file prefix) when it exits,
including through `std::process::exit` and on SIGTERM (the profile is
written, then the process exits), and while it runs every
`VERUS_DYNCOV_FLUSH_SECS` seconds (default 1) and, when busy, every
`VERUS_DYNCOV_FLUSH_MS` milliseconds (default 100), so that a process that
gets SIGKILLed (a test cluster's server) loses at most that much; stop such
processes with SIGTERM to lose nothing. The reporter sums every profile it
is given. Long-running programs can also call `vstd::dyncov::flush()`.

## What is measured

Every exec function inside `verus!` gets a frame on a per-thread stack and
a call counter. On entry its `requires` is evaluated on the real
arguments; an `external_body` function also has its `ensures` evaluated on
the result. Each evaluation is `True`, `False`, or `Unknown`: a clause the
engine cannot lower, a ghost argument, an `int` outside the `i128` model,
or a panic inside the lowered code (an index out of range, an uninterpreted
spec function) all give `Unknown`, never an abort. A false trusted
`ensures` *taints* every verified frame on the thread's stack at that
moment: those functions' proofs relied on it.

The program's behaviour never changes: a violated contract is counted,
not enforced.

The reporter joins each profiled function to its static node by the
file and line of its definition and computes, over V (all verified exec
functions):

- S, statically reachable;
- D, called at least once;
- T, in D with no false precondition on any call and never tainted.

A false precondition is classified by its caller, the instrumented
function below it on the thread's frame stack (not the source location,
which `#[track_caller]` chains would misattribute): from a verified exec
function it is a *lowering disagreement* (Verus proved the precondition
there; the lowering is wrong; the run fails but coverage is not affected),
from a trusted function or from outside the instrumented code it is a
*violation* (the program uses the function outside its verified domain).
A trusted function's own false `requires` is listed under the trust
findings. `Unknown` counts as covered, like the static check: the function
ran and its contract was not disproven; the spec report lists why each
clause was unknown. Clauses after the first false one are not evaluated
(a later clause may assume the earlier ones), so their counts cover only
the calls that reached them.

Outputs: the summary (with the per-module S/D/T table, the functions not
in T with their reason, the trust findings, and diagnostics), `--diff`
(S \ D split by whether a static caller ran, D \ T split into violated and
tainted, D \ S), `--spec-report` (every clause with its true/unknown/false
counts), `--lcov`, whose function hits are the calls of functions in
T and whose `BRDA` records give, per contract clause, how often it held
(branch 0), failed (branch 1), and was unknown (branch 2), and `--html
DIR`, the per-file pages with T as the criterion for verified exec code.
`--llvm-export cov.json` adds the functions LLVM saw run, verified or not.

## The lowering

Contracts and spec functions are lowered by the `exec_spec` engine of
[verus-spec-check](https://github.com/verus-lang/verus-spec-check),
vendored at `dependencies/verus-spec-check`, in a *dyncov flavor* that the
fork adds to it:

- every spec function with a body gets an exec twin `exec_<name>` next to
  it, and a module named after it re-exports the twin as
  `<name>::__dyncov`, so that a `use` of the spec function brings the twin
  along and a contract in another module can call it;
- every contract clause is a synthetic spec function of the parameters it
  mentions (`self`, `old(p)` and the result are parameters too), lowered
  the same way and called by the wrapper with the real arguments converted
  to the twin's borrowed forms (`Vec<T>` as `&[T]`, `String` as `&str`,
  ...);
- `int` and `nat` are `i128`; every arithmetic operation and comparison of
  a lowered expression goes through checked `int` arithmetic, so the exec
  widths never overflow silently, and a value outside `i128` is `Unknown`;
  `<<` and `!` on an integer need the operand's width, which the model
  lost, and are `Unknown` too;
- a struct or enum declared inside `verus!` is its own exec model; the
  instrumented build adds `#[derive(Clone, PartialEq)]` to one that lacks
  them (unless it has a ghost field, or implements them by hand in the
  same file), since contracts compare and snapshot values; a spec-only
  type (ghost, or with `Seq`/`Set`/`Map`/`int` fields) gets a mirror with
  exec fields;
- bounded quantifiers (`forall|i: int| lo <= i < hi ==> ...`) are loops,
  `Unknown` when the range exceeds a million values; unbounded ones,
  `choose`, closures, and spec functions without a body (`uninterp`) are
  `Unknown`;
- `Seq`, `Set`, `Map`, `Option`, `String` and tuples use the executable
  companions in `vstd::dyncov::vstd_ext`, a port of the engine's
  `vstd_ext` crate that depends on nothing but std; the vstd spec
  functions with an executable meaning known to the lowering
  (`vstd::dyncov::rt::vstd_fns`, currently `increasing_seq`) are called
  there, any other call into vstd is `Unknown`.

Generated code that does not type-check (a construct the engine lowers to
something the real exec types do not support) does not fail the build:
`verus --dyncov` reads the compiler's diagnostics, reports each location
and its message, and recompiles with those clauses and spec functions
disabled (`VERUS_DYNCOV_DISABLE=file:line,...`, which can also be set by
hand); they evaluate to `Unknown`, and the spec report of the build shows
what became `Unknown` and why. `VERUS_DYNCOV_DEBUG=1` prints the full
diagnostics of every attempt, and at run time the first panic of each
clause.

Limits worth knowing: the frame stack is per thread, so a violation on a
spawned thread does not taint the spawner; `assume` statements are not
evaluated; trait and generic impls' spec methods have no twins; vstd's own
exec functions are not instrumented; every instrumented call takes a
global lock, and a busy thread writes the profile itself every
`VERUS_DYNCOV_FLUSH_MS`, which a multithreaded server will notice. The
profile is written whole (a temporary file, then a rename), so a reader
never sees a partial one. The runtime installs a SIGTERM handler only if
the program has none.

## Tests

- `cargo test -p verus_dyncov`: the runtime (three-valued evaluation,
  frames and taint, the executable companions).
- `cargo test -p verus-reach`: the reporter (join, classification, sets).
- `vargo test -p rust_verify_test --test dyncov`: end to end, from
  `verus --dyncov` through the binary to the reporter.
