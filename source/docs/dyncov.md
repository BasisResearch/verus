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
verus-reach --dynamic profiles/ REACH_DIR   # summary; add --diff, --spec-report, --lcov
```

`--dyncov` compiles like `--compile`, with `--cfg verus_dyncov` for the
`verus!` macro and `-C instrument-coverage -Z coverage-options=branch` for
LLVM. Verification is not rerun, so `--no-verify` is the usual companion.
Pass `--reach DIR` on the same run (or an earlier one on the same sources)
to get the static reports the reporter needs. With cargo, use
`--fwd-verus-args-to roots` so that dependencies (vstd) are not asked for
reports. When the workload is a test suite, build the tests the same way
(`cargo verus build --tests -- --reach DIR --dyncov --no-verify`): the
test crates then write their own reports (`<crate>.test-<root>.json`),
whose harness `main` roots the static graph at the tests, so that a
function the tests call is in S as well as in D.

The instrumented program writes one JSON profile per process to
`$VERUS_DYNCOV_OUT` (a directory, or a file prefix) when it exits,
including through `std::process::exit` and on SIGTERM (the profile is
written, then the process exits), and while it runs every
`VERUS_DYNCOV_FLUSH_SECS` seconds (default 1) and, when busy, every
`VERUS_DYNCOV_FLUSH_MS` milliseconds (default 100), so that a process that
gets SIGKILLed (a test cluster's server) loses at most that much; stop such
processes with SIGTERM to lose nothing; a test binary is one
process per run, and the reporter sums every profile it is given.
Long-running programs and fuzz targets can also call
`vstd::contrib::dyncov::flush()` themselves.

## What is measured

Every exec function inside `verus!` gets a frame on a per-thread stack and
a call counter. On entry its `requires` is evaluated on the real
arguments; an `external_body` function also has its `ensures` evaluated on
the result; an `assume(e)` directly in exec code is evaluated where it
stands. Each evaluation is `True`, `False`, or `Unknown`: unsupported
constructs, ghost arguments, opaque types, `int` overflow, a panic inside
the lowered code, and an exhausted step budget (`VERUS_DYNCOV_BUDGET`,
default one million operations) all give `Unknown`, never an abort. A
false trusted `ensures` or `assume` *taints* every verified frame on the
thread's stack at that moment: those functions' proofs relied on it.

The program's behaviour never changes: a violated contract is counted,
not enforced.

The reporter joins each profiled function to its static node by the
file and line of its definition and computes, over V (all verified exec
functions):

- S, statically reachable;
- D, called at least once;
- T, in D with no false precondition on any call and never tainted.

A false precondition is classified by its caller: from a verified exec
function it is a *lowering disagreement* (Verus proved the precondition
there; the lowering is wrong; the run fails but coverage is not affected),
from anything else it is a *violation* (the program uses the function
outside its verified domain). `Unknown` counts as covered, like the static
check: the function ran and its contract was not disproven; the spec
report lists why each clause was unknown.

Outputs: the summary (with the per-module S/D/T table, the functions not
in T with their reason, the trust findings, and diagnostics), `--diff`
(S \ D split by whether a static caller ran, D \ T split into violated and
tainted, D \ S), `--spec-report` (every clause with its true/unknown/false
counts), and `--lcov`, whose function hits are the calls of functions in
T and whose `BRDA` records give, per contract clause, how often it held
(branch 0), failed (branch 1), and was unknown (branch 2); `genhtml
--branch-coverage` renders them. `--llvm-export cov.json` adds the functions LLVM
saw run, verified or not.

## The lowering

Contracts are lowered syntactically by the macro (it sees tokens, not
types), so the lowered code works on a dynamic value model,
`vstd::contrib::dyncov::Dyn`: `int`/`nat` are `i128` with checked
arithmetic, `Seq`/`Set`/`Map` are vectors, strings are sequences of
characters, and every struct and enum declared inside `verus!` gets a
generated `DynView` that exposes its fields and variant; a value of any
other type is opaque and supports equality only (when it is `PartialEq`).
`x@` and `x.view()` call the lowered `View` impl of the type, if it was
declared in `verus!`. Every spec function with a body gets a lowered twin,
registered by name at load time (and again from every wrapper of the same
block, in case the linker dropped the registration), so that contracts can
call spec functions across modules. A call is resolved by name and
arity; when several modules define the name (the `use` that picks one is
outside the macro's view), the same-module one wins, else the declared
parameter types are matched against the arguments' shapes, else every
candidate is evaluated and only a unanimous answer is accepted. A call
that still resolves to no twin, or to several disagreeing ones, is
`Unknown`, and the spec report names the function. Bounded quantifiers (`forall|i: int| lo <= i < hi
==> ...`, and `u8`/`i8`/`bool` binders) are enumerated under the budget;
unbounded ones, `choose`, closures other than `filter`/`map`/`all`/`any`,
and spec functions without a body (`uninterp`, `external_body`) are
`Unknown`.

Limits worth knowing: the frame stack is per thread, so a violation on a
spawned thread does not taint the spawner; an `assume` inside an explicit
`proof { }` block is erased with the block and not counted; the twin of a
spec function in a module with no exec code may be dropped by the linker,
making calls to it `Unknown`; vstd's own exec functions are not
instrumented.

## Tests

- `cargo test -p dyncov-runtime-tests`: the runtime (three-valued
  evaluation, frames and taint, the registry, the value model).
- `cargo test -p verus-reach`: the reporter (join, classification, sets).
- `vargo test -p rust_verify_test --test dyncov`: end to end, from
  `verus --dyncov` through the binary to the reporter, including the
  lowering of each construct and the wrapper shapes (methods, `&mut`
  parameters, early returns, trait default methods, generics).
