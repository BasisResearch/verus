# Trace arm conformance evaluation

2026-10-07, aws-dev (8 vCPU, Linux), Basis TLC `basis-11305b4a05`, Java 25.

The three previously slow logs now all conform: **0/3 completed before, 3/3
after**, covering **35,238 logged steps**. The full exporter suite passes
**177/177 tests**, with `TLA2TOOLS_JAR` set. ToyDB's existing conformance runner
passes **58/58 goldenscripts**, covering **2,786 steps**.

## Design

The export already lowers `exists|step: Step| next_step(pre, post, step)`
into one existential per constructor. Retain those templates, including their
original field domains and dispatcher body. Each `TraceArm_<transition>(e)`
selects the constructor named by the logged transition and narrows directly
mapped field binders using `TraceParam`. Missing parameters keep their original
domains; logged values must belong to those domains. Nested quantifiers preserve
dependent field bounds. The dispatcher remains in the template, so guards outside
the transition function are preserved. `TypeOK'` remains conjoined when the
export has it.

This also handles VerusSync's generated `next_by` dispatch. A log naming the
dispatcher itself can supply its `Step` parameter directly, provided its domain
and state arguments exactly match the root existential.

Closure-valued verus-tla roots expose independent action-record disjuncts under
their builder names. Their whole lowered bodies retain preconditions, transition
closures and enclosing guards. Both `step(acquire(thread))` and
`acquire().forward(input)` are supported. Repeated call sites of one action are
combined under one log name, retaining the constraints on each site's input.
Legacy logs naming `next` remain valid.

`TraceNext` calls the selected relation, then the **unchanged observed-successor
comparison**. Unknown names alone take the state-only `OTHER -> Next` branch;
the report's `trace.unknown_step` explicitly describes this weaker check.
Ambiguous short names and unknown parameters of known steps still fail.

Selection is deliberately structural. General relations such as partially
assigning helpers, computed enum call arguments, and non-simple dispatch
patterns retain their existing `Next /\ logged_relation` semantics; the report
lists them in `trace.general_relation_steps`. They are not silently treated as
independent actions. Action extraction currently recognizes zero-parameter
branches and branches with a single directly quantified or fixed forward input.
The three measured models' concrete logged transitions all use selected arms.

## Timings and counts

Same logs and hole-domain generators as `wild/<crate>/run.sh` and `REPORT.md`.
The baseline is the supplied main binary at `152d37b7`; its exporter and exporter
tests are identical to this branch's starting commit `9abf2c0e`.

Each row is one fresh-JVM TLC run, one worker, `-Xss256m -Xmx4g
-XX:+UseParallelGC`, including JVM startup and JSON loading but excluding export.
Runs have external wall-clock limits (120 seconds before, 240 after). They ran
on the shared development machine alongside builds/tests, so these are observed
wall times, not statistically controlled microbenchmarks. A timeout is a lower
bound, not a measured completion time.

| Model / log | Steps | Before | After | After states / depth | Speedup lower bound |
|---|---:|---:|---:|---:|---:|
| raft-rs, flow-control move-forward `1504.ndjson` | 33,661 | timed out, 120.076 s | 5.508 s | 33,662 / 33,662 | >21.8x |
| lru-rs, `tests__test_pop_lru__0.ndjson` (256-key domain) | 551 | timed out, 120.130 s | 0.804 s | 552 / 552 | >149x |
| circular-buffer, `rust_out/main-3884610/1.ndjson` | 1,026 | timed out, 120.192 s | 1.004 s | 1,027 / 1,027 | >119x |

Completed-log counts: **0 -> 3**. Timeout counts: **3 -> 0**. Afterward all
**35,238 steps** conform, with **35,241 distinct states** across the three runs.
These counts concern the selected slow logs, not a rerun of all 3,973 wild logs.
Ranked by measured speedup lower bound: **LRU, circular-buffer, raft-rs**.

A separate integration check through the existing MCP server's `tlc_open` /
`tlc_conform` / `tlc_close` tools also reports all three conforming. The
`tlc_conform` calls took **8.117 s, 0.866 s, 1.260 s**, respectively (resident
TLC, excluding `tlc_open`; these are not the fresh-JVM timings above).

Raw timings and exact input paths: `before-timings.json`, `after-timings.json`.
MCP responses: `mcp-results.json`.

## Validation

- Full `rust_verify_test --test tla_export`: **177 passed, 0 failed**, 56.20 s
  for the tests, with `TLA2TOOLS_JAR` set to the Basis jar.
- The 19 existing trace-spec tests remain, with expectations updated for the
  requested unknown-name fallback, selected dispatch, and additional action
  names. Four new TLC regressions cover hand-written enum dispatch, VerusSync,
  action records, and repeated `.forward(input)` call sites. Each accepts a
  control log and rejects a log naming A where only B is enabled, even when the
  observed successor is identical. The enum regression puts A's guard in the
  dispatcher, outside its transition function.
- Existing missing-parameter, hole-domain, computed-argument, partial-state,
  collection-decoding, diagnostics and malformed-log tests pass.
- ToyDB `origin/yl/raft-safety-refine` at
  `c23eebe8c678bda4693748f8a5cbe05ddba2b2ff`: ran `tla/conform.sh` in an isolated
  archive of that branch. It reruns the Raft node goldenscripts with `tla-trace`,
  then checks all logs against the branch's hand-written `Raft_trace.tla`.
  **58 conform, 0 divergent, 0 errors**, 2,786 logged steps. The output is in
  `toydb-conform.log`. This is the requested existing toyDB conformance check;
  it is not a claim that those logs were checked against a newly exported model.
- Release build, rustfmt, and `git diff --check` pass.

## Reproduction

From the Verus worktree, with the sibling `wild/` evaluation data available:

```sh
export PATH=$HOME/.cargo/bin:$PATH
export TMPDIR=$HOME/tmp
export VERUS_MCP_ENABLED=1
export TLA2TOOLS_JAR=$HOME/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar

# Build from source/ (its .cargo/config.toml supplies Verus build settings).
(cd source && timeout 600 cargo build --release -p rust_verify)
(cd source && timeout 1800 cargo test --release -p rust_verify_test \
  --test tla_export -- --test-threads=4)

# The driver reads the original per-crate hole-domain generators and logs.
timeout 600 python3 trace-arm-eval/bench.py before \
  ../base/verus/source/target-verus/release/verus 120
timeout 900 python3 trace-arm-eval/bench.py after \
  source/target-verus/release/verus 240
timeout 240 python3 trace-arm-eval/mcp_check.py

# In an isolated checkout/archive of the toyDB branch above:
timeout 1800 bash tla/conform.sh
```

A freshly rebuilt builtin library requires rebuilding `vstd` as well; this run
used `timeout 300 cargo run --release -p vstd_build -- target-verus/release
--release --no-verify` from `source/` before running the exporter tests.
