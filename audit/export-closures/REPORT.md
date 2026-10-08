# Closure records and bounded choice

This lane extends `source/vir/src/tla.rs`; regression coverage lives in
`source/rust_verify_test/tests/tla_export.rs`.

## Reduction rules

* Closure literals passed to helpers are kept symbolically, including method
  receivers. The helper body is reduced with the caller's state roles. Ordinary
  arguments become fresh `LET` bindings and retain their lexical scope.
* Record fields can lead through constructors, nested fields, local aliases,
  and helper bodies with `let` bindings. Ordinary fields of a record that also
  holds closures are projected without printing its closures.
* A parameterized `a.forward(input)` resolves to its returned closure. For
  example, the test's nested action reduces to
  `LET input == 0 n == input + 1 IN LET offset == -1 k == offset + 1
  n_2 == n IN x < 3 /\ x' = x + n_2 + k`.
* Captured environments are immutable `Arc<Env>` values. Sharing avoids deep
  copying the entire capture graph when reducing Anvil's helper chains.
* Recursive closure-valued helpers, unresolved closures, and record values
  whose definitions are unavailable retain source-located refusals. Resolution
  has a depth limit of 64. This does not encode closures as TLA+ values.

## Choice rules

* `choose |x| P(x)` becomes `CHOOSE x \in D : P(x)`. The exporter uses the
  existing guard bounds, finite type domains, or explicit `Dom_<Type>` holes.
* `Set::choose()` uses the receiver as its domain; `Multiset::choose()` uses
  `DOMAIN receiver`, the elements with positive multiplicities.
* The JSON report lists choice variables, domains, locations, and warnings for
  finite hole carriers. Named expression reports also carry their choices.
* Integer choice holes have `ASSUME` constraints for integer membership and
  the source integer range. A header warning identifies finite choice carriers.
* TLC selects one fixed witness for a predicate. These runs do not prove a
  property for every possible witness selection in Verus. An empty witness set
  stops TLC; it is not replaced with a default value. Multiple-binder choices
  and unbounded generic choices remain explicit refusals.


## Symbolic-record guard scope repair

Anvil `sub_api_sm` previously passed a closure-valued record through a helper.
Definedness analysis eagerly walked an unused field of that record and emitted
`kind.tag = "CustomResourceKind"`. The `kind()` operator existed only in the
analysis snapshot, so the resulting module failed SANY.

Analysis now keeps closure-valued records symbolic and inspects a selected
ordinary field in the same captured environment as symbolic reduction. Any
required field guards are wrapped in that reduction's `LET` bindings. An unused
field does not constrain the action. Unresolved symbolic values still take the
existing source-located refusal path.

Two new TLC-backed tests cover a consumed field whose partial read depends on
an existentially bound parameter (including an invalid variant that must be
excluded), and an unused partial field that reproduced the exact unknown
`kind` operator error before the fix. The latter must still explore all three
states; simply disabling the action would fail the test.






## Cumulative campaign after rebase onto `fb8014b0`

The table measures all 33 requested export targets: Anvil’s five (including both API adapters), IronKV host, nrkernel’s six, NR’s three, and all 18 Splinter attempts. Five additional campaign adapters/controls follow separately. A compiler error or timeout is **not** a zero-refusal export. `Before` uses the original campaign binary; `L1–3` uses the clean lane-3 checkout at `fb8014b0`; `After` uses the rebased lane-4 binary. Binary hashes and version strings are saved in `cumulative-results.json` (the parent binary embeds its pre-commit dirty version string).

- **before:** 9/33 zero-refusal exports; 9/33 also pass SANY; 3/9 saved-bound TLC runs complete; 3/9 explore without an evaluation error.
- **parent:** 17/33 zero-refusal exports; 17/33 also pass SANY; 5/9 saved-bound TLC runs complete; 7/9 explore without an evaluation error.
- **after:** 20/33 zero-refusal exports; 20/33 also pass SANY; 5/9 saved-bound TLC runs complete; 7/9 explore without an evaluation error.

Since the previous stack on `5e38e1ee`, zero-refusal exports **20→20**, zero-refusal exports passing SANY **20→20**, completed campaign-bound TLC runs **5→5**, and explorations **7→7**.

The table distinguishes completed runs, invariant counterexamples, and progress until timeout. Lane 4’s additional zero-refusal targets over lane 3 are identified by the intermediate column.

Original `MC.tla`, `MC.cfg`, and TLC commands/timeouts were replayed unchanged, with their hashes recorded. The original campaign has no saved bounds for the other 24 primary targets (round-2 Anvil replays are reported separately); no new constants, table interpretations, adapters, or bounds were invented. Reaching states before a TLC evaluation error does not count as exploration. Lane-3 restrictions and finite carriers remain explicitly reported approximations, so a completed bounded run is not a proof of the unrestricted source.

L1 = traits; L2 = nrkernel bit operations/partial Init; L3 = partial reads/finite carriers; L4 = closure reduction/bounded choose. Intermediate attribution also uses the committed lane reports (`artifacts/nrkernel/report.txt`, `audit/export-partial/REPORT.md`) and the trait lane’s recorded campaign results. More refusals can mean reduction reached previously hidden unsupported expressions.


### Requested campaign targets

| Target | Before | L1–3 | After | SANY parent → after | TLC before → after (original campaign bounds) | Lane contribution |
|---|---:|---:|---:|---|---|---|
| anvil/Cluster-adapter | 22 | 22 | 62 | pass → pass | no saved bounds → no saved bounds | L1 trait tables; L4 reduces reachable records, exposing deeper callbacks/choices; still refused |
| anvil/sub_api | 14 | 8 | 58 | pass → pass | no saved bounds → no saved bounds | L1 trait tables; L3 carriers/guards; L4 action/choice reduction exposes deeper callbacks; still refused |
| anvil/sub_api_sm | 16 | 15 | 8 | pass → pass | no saved bounds → no saved bounds | L4 reduces helper receivers; choice over closure records remains |
| anvil/sub_controller | 9 | 9 | 0 | pass → pass | no saved bounds → no saved bounds | L1 trait tables + L4 record/receiver reduction jointly remove all refusals |
| anvil/sub_network | 2 | 2 | 0 | pass → pass | no saved bounds → no saved bounds | L4 removes both closure refusals |
| ironkv/host_protocol_t | 6 | 0 | 0 | pass → pass | no saved bounds → no saved bounds | L1 trait tables + L3 total collections already remove all refusals; L4 unchanged |
| nrkernel/hlspec | 4 | 1 | 0 | pass → pass | no saved bounds → no saved bounds | L1 trait table + L2 bit/Init + L3 carriers + L4 final bounded choose |
| nrkernel/mmu_rl1 | 95 | 0 | 0 | pass → pass | no saved bounds → no saved bounds | L1/L2 trait/bit rules; L3 cached definedness removes expansion-limit refusals |
| nrkernel/mmu_rl2 | 108 | 0 | 0 | pass → pass | no saved bounds → no saved bounds | L1/L2 trait/bit rules; L3 cached definedness removes export timeout |
| nrkernel/mmu_rl3 | 101 | 0 | 0 | pass → pass | no saved bounds → no saved bounds | L1/L2 trait/bit rules; L3 cached definedness removes export timeout |
| nrkernel/os | 135 | 7 | 6 | pass → pass | no saved bounds → no saved bounds | L1/L2 trait/bit rules; L3 removes timeout; L4 removes choose; integer type bounds remain (os.rs:242,249; mmu/defs.rs:434) |
| nrkernel/os_ext | 1 | 0 | 0 | pass → pass | no saved bounds → no saved bounds | L2 bit/Init removes final refusal |
| nr/AsynchronousSingleton | 3 | 0 | 0 | pass → pass | no saved bounds → no saved bounds | L1 concrete dispatch/typed tables |
| nr/SimpleLog | 4 | 0 | 0 | pass → pass | no saved bounds → no saved bounds | L1 concrete dispatch/typed tables |
| nr/UnboundedLog | 4 | 0 | 0 | pass → pass | no saved bounds → no saved bounds | L1 concrete dispatch/typed tables; L3 carriers |
| splinter/AbstractJournal | 0 | 0 | 0 | pass → pass | evaluation/config error → complete (72 states) | L3 guarded partial reads/casts unblock evaluation; L4 unchanged |
| splinter/AbstractMap | 0 | 0 | 0 | pass → pass | evaluation/config error → complete (3 states) | L3 guarded partial reads/casts unblock evaluation; L4 unchanged |
| splinter/AllocationBetree | compile error | compile error | compile error | not exported → not exported | no saved bounds → no saved bounds | Campaign Rust input does not compile; no lane unblocks it |
| splinter/AllocationBranchBetree | compile error | compile error | compile error | not exported → not exported | no saved bounds → no saved bounds | Campaign Rust input does not compile; no lane unblocks it |
| splinter/AllocationCrashAwareJournal | compile error | compile error | compile error | not exported → not exported | no saved bounds → no saved bounds | Campaign Rust input does not compile; no lane unblocks it |
| splinter/AllocationJournal | compile error | compile error | compile error | not exported → not exported | no saved bounds → no saved bounds | Campaign Rust input does not compile; no lane unblocks it |
| splinter/CoordinationSystem | 0 | 0 | 0 | pass → pass | timeout before progress → evaluation/config error | L3 guards/carriers; unchanged config lacks Dom_Key |
| splinter/CrashTolerantJournal | 0 | 0 | 0 | pass → pass | evaluation/config error → progress; timeout (at least 29 states reported) | L3 guarded partial reads/casts unblock evaluation; L4 unchanged |
| splinter/CrashTolerantMap | 0 | 0 | 0 | pass → pass | evaluation/config error → evaluation/config error | L3 guards/carriers; unchanged config lacks Dom_Key |
| splinter/FilteredBetree | compile error | compile error | compile error | not exported → not exported | no saved bounds → no saved bounds | Campaign Rust input does not compile; no lane unblocks it |
| splinter/LikesBetree | compile error | compile error | compile error | not exported → not exported | no saved bounds → no saved bounds | Campaign Rust input does not compile; no lane unblocks it |
| splinter/LikesJournal | compile error | compile error | compile error | not exported → not exported | no saved bounds → no saved bounds | Campaign Rust input does not compile; no lane unblocks it |
| splinter/LinkedBetreeVars | compile error | compile error | compile error | not exported → not exported | no saved bounds → no saved bounds | Campaign Rust input does not compile; no lane unblocks it |
| splinter/LinkedJournal | 0 | 0 | 0 | pass → pass | evaluation/config error → invariant CTI (4 states) | L3 guarded partial reads/casts unblock evaluation; L4 unchanged |
| splinter/PagedBetree | 0 | 0 | 0 | pass → pass | complete (25 states) → complete (25 states) | Existing bounded completion; L3 dependency declarations repaired |
| splinter/PagedJournal | 0 | 0 | 0 | pass → pass | complete (12 states) → complete (12 states) | Existing bounded completion preserved |
| splinter/PivotBetree | 0 | 0 | 0 | pass → pass | complete (25 states) → complete (25 states) | Existing bounded completion; L3 dependency declarations repaired |
| splinter/UnifiedCrashAwareJournal | compile error | compile error | compile error | not exported → not exported | no saved bounds → no saved bounds | Campaign Rust input does not compile; no lane unblocks it |

### Additional campaign adapters and controls

| Target | Before | L1–3 | After | SANY parent → after | TLC before → after (original campaign bounds) | Lane contribution |
|---|---:|---:|---:|---|---|---|
| anvil/sub_vrs_reconcile | 5 | 0 | 0 | pass → pass | no saved bounds → no saved bounds | L1 dispatch/tables removes refusals; L3 fixes Option projection through helper match arms (round-2 replay below) |
| nr/UnboundedLog-mono | 1 | 0 | 0 | pass → pass | evaluation/config error → evaluation/config error | L1 table + L3 guarded reads; unchanged config lacks table assignment |
| nr/CyclicBuffer | 6 | 6 | 6 | pass → pass | no saved bounds → no saved bounds | L1 dispatch/tables; see remaining located refusals |
| nr/FlatCombiner | 1 | 0 | 0 | pass → pass | complete (418 states) → evaluation/config error | L1 replaces uninterpreted refusal with table; original config lacks Table_arbitrary__tla_closed |
| nr/RwLockSpec | 0 | 0 | 0 | pass → pass | complete (207 states) → complete (207 states) | Existing bounded completion |

### Round-2 Anvil harnesses

These are additional bounded replays, separate from the original campaign counts above. Both use byte-identical saved `MC.tla`/`MC.cfg` files. Reproduce with `python3 audit/export-closures/cumulative.py round2-replay --round2 --verus source/target-verus/release/verus`. No TLC command was saved for these harnesses, so the replay uses lane 3’s 30-second cap, one worker, and `-continue`. A completed search with a counterexample is not a clean invariant pass.

| Machine | L1–3 refusals | L1–4 refusals | Parent TLC | Rebased stack TLC |
|---|---:|---:|---|---|
| anvil/sub_network | 2 | 0 | evaluation/config error | complete (9 states) |
| anvil/sub_vrs_reconcile | 0 | 0 | complete search with invariant CTI (7 states) | complete search with invariant CTI (7 states) |

Network: lane 4 removes both closure refusals and the unchanged transport harness completes with nine distinct states. Controller: the original-campaign export above confirms lane 4 removes all nine parent closure refusals; SANY passes. Its round-2 controller harness was marked preliminary/unvalidated by that campaign, so no bounded controller verdict is claimed.

VRS: lane 3’s saved clean `5e38e1ee` replay failed on an Option projection after two states. Both the current parent and rebased stack now finish the complete seven-state search. With `-continue`, TLC reports `not_error` violated along the source’s explicit `Init → AfterListPods → Error` path for an absent/invalid response. This is an expected behavior of the unconstrained-response harness, not a claimed controller defect. Lane 3 unblocks this execution; lane 4 preserves the fix. The full round-2 logs, violations, command provenance, and bound hashes are included in the machine-readable evidence.

### Validation and remaining blockers

**216 exporter tests passed**, with `TLA2TOOLS_JAR` set. All **28** example/Raft `.tla`/`.cfg` artifacts are byte-identical. The rebase preserves the lower lanes’ tests and both restriction and choice reporting; captured environments in partial-read analysis now use the same immutable `Arc<Env>` representation as closure reduction.

Every remaining refusal, including its exact source location and multiplicity, is listed in [BLOCKERS.md](BLOCKERS.md). That file also records compiler, SANY, TLC configuration/evaluation, and timeout failures. The machine-readable report retains each individual refusal. The lane-4 `sub_api_sm` SANY regression is fixed: definedness analysis follows consumed symbolic fields and keeps their guards under the reduction’s LET bindings. It no longer emits guards for unused record fields. Both a bound-parameter closure record and the former unbound `kind` reproducer are TLC-checked. Independent lower-lane limitations and repairs are reflected in the parent and cumulative columns; their exact remaining diagnostics are in the blocker report.

Exporter suite: `export PATH=$HOME/.cargo/bin:$PATH; export TMPDIR=$HOME/tmp; source tools/activate; cd source; TLA2TOOLS_JAR=$HOME/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar timeout 1800 vargo test --release --vstd-no-verify -p rust_verify_test --test tla_export -- --test-threads=4`. Fixture comparison uses the existing `toydb-pr-30/src/raft/safety.rs` because `base/toydb/src/raft/safety.rs` is absent.

Reproduce with `python3 audit/export-closures/cumulative.py before --original-deps --verus ../base/verus/source/target-verus/release/verus`, then `parent` with the lane-3 binary and `after` with `source/target-verus/release/verus`; run `summarize-cumulative.py --tests <passed-count>` after `regression.py regression-stacked source/target-verus/release/verus`. Raw commands/logs and modules are retained in ignored `cumulative-*` directories. Historical lane-4-only measurements in `results.json` are superseded by `cumulative-results.json`.
