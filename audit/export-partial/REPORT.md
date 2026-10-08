# Partial reads and finite carriers — lane 3

The six examples and toyDB Raft safety model re-export **byte-identically in all 28 `.tla`/`.cfg` files** against the parent lane. AbstractMap completes its unchanged bounded TLC run without the former cast assertion. The implementation is ready for review.

The branch is stacked on `kg/export-nrkernel`, currently `6fc818cad8e20a29dc50432c8b8a7b0a49b91253`. Both that lane's implementation and tests were retained during the rebase. No campaign source, adapter, constraint, or constant assignment was changed.

## Design and TLA+ rules

Spec conjunctions are order-independent in Verus, while TLC evaluates guards and projections in printed order. A stable ordering moves a later source guard before an earlier read when the guard does not read the post state. Init retains assignment order. Already ordered conjunctions retain their existing grouping. A preceding `n == seq.len()` equality plus `0 <= i` and `i < n` establishes the same sequence-domain fact, preserving the parent lane’s Raft Init bytes.

| Construct | Rendering |
| --- | --- |
| Map read before membership guard | `k \in DOMAIN m /\ P(m[k])` |
| Option/enum payload before variant guard | `o.tag = "Some" /\ P(o.v0)` |
| Sequence read before direct range guard | Put the source `0 <= i < Len(s)` guard before `s[i + 1]` |
| Partial read without a recognized preceding guard | `IF DefinedRead THEN conjunct ELSE FALSE` |
| Map read definedness | `k \in DOMAIN m` |
| Sequence read definedness | `(i + 1) \in DOMAIN s` |
| Enum projection definedness | `value.tag = "Variant"` |
| Value helper | Inspect its body with actual arguments, preserving the scope of local bindings |
| Recursive value helper | A recursive `Defined_f` operator checks the required reads through the base case; no bounded unrolling |
| Map constructor callback | `\A k \in domain : DefinedCallback(k)` before consuming the constructed map |
| `IMap::total(f)` | `[k \in Dom_K |-> f(k)]` |
| `ISet::full()` | `Dom_A` |
| `ISet::is_full()` | `set = Dom_A` |
| Unbounded `ISet::new(p)` / `IMap::new(p, f)` | Predicate comprehension over the explicit carrier; an existing finite source bound is retained |
| `ISet::mk_map(f)` | `[k \in set |-> f(k)]` |
| `ISet::finite()` | `set \subseteq Dom_A /\ IsFiniteSet(set)` |
| `ISet<ISet<A>>::flatten()` | `UNION sets` |

A carrier is a `CONSTANT Dom_<Type>` and a source-located hole. Its `ASSUME` requires a finite set of values of the key/element type, including numeric bounds and structural record/tuple/variant checks. A record whose fields themselves require holes does not count as an exact finite type domain. `is_full` is recognized directly so IronKV does not fall into the generic `ISet<A>` library body.

Carrier-relative finiteness and totality are approximations, not statements about an infinite source universe. Likewise, disabling a conjunct on an unspecified read restricts source behaviors: it is not justified by claiming that Verus itself disables the action. Each inserted restriction records `what`, `location`, and `in_function` in the JSON report's `restrictions` field and is warned of in the TLA header. The field is omitted when empty. Named-expression exports do not leak their restrictions into the main module.

Analysis rendering uses an isolated exporter snapshot so it cannot duplicate holes/refusals or alter assignment bookkeeping. Operator names are reserved during analysis, and dependencies of retained guards are emitted in the real exporter; unused speculative values cannot introduce table holes. Returned local expressions reserve their bound names before an enclosing destructuring binding is named. Recursive helper checks and captured `let` values preserve their lexical scopes. Unresolved type parameters and analysis expansion limits remain source-located refusals.

## Compatibility and cast fixes

The byte differences were inserted definedness wrappers, not finite carriers or a necessary change in conjunct order. The first implementation confused any boolean subexpression with an action predicate, including a boolean condition inside a lazy `LET` value and a predicate used only by an invariant/temporal property. It also forgot sufficient source bounds when analyzing a helper or a captured binding.

The action-disabling transformation is now scoped to Init/Next and their helpers. It does not rewrite separately exported assertions or temporal properties. LET initializers are rendered as values; their partial reads are analyzed when the binding is consumed, under the guards at that use. Conditional branches retain their conditions during definedness analysis. A bounded linear-integer implication check recognizes chained/transitive sequence bounds, shifted indices, and nonempty last-element reads; unsupported arithmetic and resource limits yield unknown. A model-wide length fact is used only when Init establishes it and every Next assignment preserves both participating fields. Unknown writes invalidate the fact. The analysis does not assume user invariants to prove those facts.

Conjunction ordering now tracks preceding source guards and moves a later guard only for a still-undefined read. A regression pins the original grouping when an earlier guard already protects a read and a redundant guard appears later.

AbstractMap's recursive helper formed `(seq_end - 1) as nat` before reading its map. The original partial-read analyzer recursed through the cast without recording its range requirement, so its own `Defined_...` operator could trigger the legacy cast assertion. Narrowing casts now contribute a range requirement before any dependent projection or recursive call. Proven in-range casts require no new wrapper; undefined casts disable the enclosing action and are reported with the other restrictions.

The compatibility test pins the complete Raft source and all four parent artifacts for all seven inputs. The parent binary generated these portable golden files under the same crate name as the test harness; only checkout-dependent source paths are normalized; the external before/after re-export comparison uses identical paths and compares raw bytes.

## Six-machine acceptance replay

The committed `measurements.json` records the final counts and binary hashes. `replay.py` reconstructs each export from the saved campaign command and copies the original `MC.tla` and `MC.cfg` without changing their bounds. Every export is bounded by 90 seconds; every TLC invocation uses the campaign's one worker, 1 GiB heap, and 30-second limit.

Here “usable TLC run” means completion, an invariant counterexample, or continued exploration at the time limit **without an exporter evaluation or semantic-analysis failure**. The old runs did visit states before failing, so this is not a claim that they generated no states.

| Machine | Refusals before → after | TLC before → after | Distinct states before → after |
| --- | --- | --- | --- |
| nr/UnboundedLog-mono | 1 → 0 | evaluation/configuration error → evaluation/configuration error | 70 → — |
| splinter/AbstractJournal | 0 → 0 | evaluation/configuration error → complete | 27 → 72 |
| splinter/AbstractMap | 0 → 0 | evaluation/configuration error → complete | 3 → 3 |
| splinter/CrashTolerantJournal | 0 → 0 | evaluation/configuration error → exploring at 30 s | 26 → 35 |
| splinter/CrashTolerantMap | 0 → 0 | evaluation/configuration error → evaluation/configuration error | 2 → — |
| splinter/LinkedJournal | 0 → 0 | evaluation/configuration error → invariant violation | 1 → 4 |

Timeout state counts are the last progress sample, not a completed search.

Zero-refusal exports improve **5/6 → 6/6** across the current stack. Usable bounded TLC runs improve **0/6 → 4/6**: two complete, one stops at an invariant violation, and one reaches the time limit while exploring. These counterexamples have not been promoted to source-system findings. They arise in the campaign's existing finite abstractions/adapters and now additionally carry the reported partial-read restrictions.

The NR replay uses the campaign's existing `UnboundedLog-mono` adapter on both sides. The lower trait lane now renders its former `vstd::pervasive::arbitrary` refusal as a typed table hole. The unchanged campaign configuration does not assign `Table_arbitrary__tla_closed2`, so NR does not start TLC on the final stack. The unspecialized `nr/UnboundedLog` export is measured separately; the adapter's result is not represented as a successful generic-trait export.

CrashTolerantMap now exposes the explicit `Dom_Key` carrier for `TotalKMMap::empty` at `TotalKMMap_t.rs:25`. The saved configuration supplies structural field domains but not this new carrier, so its unchanged TLC configuration cannot start. No carrier assignment was invented to count it as an exploration success.

AbstractMap now completes with **33 generated / 3 distinct states**, using the original sources, adapter, and bounds. The undefined cast at `MsgHistory_v.rs:189` disables the affected predicate instead of crashing TLC. A dedicated recursive-cast regression reproduces this boundary.

## Anvil Option projection through a value helper

The saved round-2 `sub_vrs_reconcile/MC.tla` reproduces `None.v0` in `extract_some_k_list_resp_view`: 1,138 generated / 2 distinct states, stopping after `Init -> AfterListPods`. The clean lane-3 binary at `5e38e1ee` reproduces the same failure with a fresh export and the identical configuration.

This was a misplaced restriction plus an analysis gap. Boolean conditions inside a value-returning helper were treated as action predicates. Wrapping the negated response test with `IF defined THEN condition ELSE FALSE` changed which branch `reconcile_core` selected on a missing response, sending execution into the branch that extracts its payload. The caller's definedness walk skipped `match` arms, so it missed those partial reads.

Value helpers now retain their condition/value semantics. Their enclosing predicate checks definedness through selected match arms, arm guards, and short-circuit logical operands before evaluating the call. A genuine off-domain value disables that predicate with a source-located report. Generated match fallbacks share LETs to avoid repeated expansion. Cached guards account for the receiving scope's bound names, nested matches reserve outer names first, and destructuring initializer guards use only their lexical LET prefix.

The regression tests cover the negated response condition inside a match helper, unguarded Option projections inside helper bodies and match-arm guards, nested matches, and a destructuring initializer whose helper-local name is reused by a later declaration.

The unchanged VRS model now finishes at **7,960 generated / 7 distinct states**, depth 4, with zero refusals and no projection/evaluation error. With TLC's `-continue`, the complete search also reports a `not_error` invariant violation: `Init -> AfterListPods -> Error`. This is the source's explicit error branch for an absent/invalid response in this unconstrained response harness, not a claimed controller defect. Three partial-read restrictions remain reported, including the guard at the outer `next` predicate.

All three Anvil machines were replayed on this lane. `sub_network` retains its two pre-existing closure-application refusals; `sub_controller` retains nine closure-related refusals. Their generated modules pass SANY, but lane-3 alone cannot run the network relation, and the saved controller harness references closure-specialized operators supplied by lane 4. Its prior campaign report also labels that harness preliminary/unvalidated. Neither is counted as a successful TLC run. No closure adapter, source, carrier assignment, or campaign constraint was changed. Dependencies were rebuilt from the saved commands into this worktree to match the verifier's crate identities.

Current Anvil/replay evidence, binary and source hashes, and unchanged bound checks are in `anvil-measurements.json`; the earlier twelve-machine measurements remain in `measurements.json`.

## Definedness regression repair

The lane-4 report was reproduced on clean `64f1c6e3`. There were two causes:

* `ensure_defined` registered a mutually recursive helper internally but appended its TLA `RECURSIVE` declaration only after walking its dependencies. In PagedBetree/PivotBetree, `Defined_replaced_children` therefore referenced `Defined_substitute` before SANY had seen its declaration. The declaration now precedes dependency traversal. A separate guard-only variant issue in nrkernel (`core_mem_rec`) came from rendering in a disposable exporter clone: its definition was discarded while its name survived in a guard. Retained guards now commit their operator dependencies. Speculative values that never become guards remain isolated, avoiding unused table holes such as `Table_spec_affirm`.
* Helper arguments were checked at the call and stored as symbolic source expressions in every formal. Each formal use re-analyzed those arguments, and repeated helper calls re-expanded their bodies. Deep copies of captured environments amplified this. Ordinary arguments are now checked once; closures retain symbolic substitution. Repeated helper applications are memoized within a guard context, keyed by instantiated function, printed arguments, post-state flags, and safety facts. Captured environments use shared immutable `Arc` snapshots. Analysis has a 65,536-visit / 1,024-depth limit with an explicit source-located refusal if exceeded; none of these campaign replays reaches it.

The new regressions cover PagedBetree-style mutual substitution through a map constructor, a guard-only record helper (without leaking an unused `spec_affirm` table), and forty shared helper layers with 2^40 call paths. The latter must export in under 30 seconds, with zero refusals and less than 40 KB of TLA; SANY checks all forty layers and TLC checks the same behavior at eight layers because TLC itself eagerly preprocesses the value graph.

| Machine | Original campaign | Clean `64f1c6e3` | Fixed replay |
| --- | --- | --- | --- |
| splinter/PagedBetree | TLC completes, 25 distinct | SANY: undefined `Defined_substitute` | TLC completes, 25 distinct / 173 generated |
| splinter/PivotBetree | TLC completes, 25 distinct | SANY: undefined `Defined_substitute` | TLC completes, 25 distinct / 133 generated |
| nrkernel/mmu_rl1 | 95 refusals, 8.4 s | 189 expansion refusals, 25.7 s | 0 refusals, 8.9 s; SANY passes |
| nrkernel/mmu_rl2 | 108 refusals, 9.1 s | export timeout at 90 s | 0 refusals, 8.6 s; SANY passes |
| nrkernel/mmu_rl3 | 101 refusals, 9.1 s | export timeout at 90 s | 0 refusals, 8.6 s; SANY passes |
| nrkernel/os | 135 refusals, 8.7 s | export timeout at 90 s | 7 refusals, 11.6 s; SANY passes |

The remaining OS refusals are `choose` and integer type bounds, not expansion limits. The four nrkernel modules have no saved campaign MC command; the result is successful export and SANY, not a claim of TLC exploration. The two trees use their unchanged campaign configurations. Export timings are wall-clock observations under a 90-second cap, with two concurrent regression replays.

The original six machines were replayed again: **6/6 zero-refusal exports and 4/6 usable TLC runs**, unchanged from the prior acceptance result. Together, the twelve replays yield **11/12 zero-refusal exports and 12/12 SANY passes**; the eight with saved TLC configurations yield six usable runs. This repair is a new commit followed by a plain push; lane 4 owns the subsequent rebase.

## Total-collection campaign exports

| Module | Before refusals/status | After refusals/status | Remaining issue |
| --- | --- | --- | --- |
| nr/UnboundedLog | 4 | 0 | explicit holes require assignments |
| ironkv/delegation_map_t | no transition triple | no transition triple | no transition triple |
| ironkv/host_protocol_t | 6 | 0 | explicit holes require assignments |
| ironkv/host_impl_t | no transition triple | no transition triple | no transition triple |
| nrkernel/hlspec | 4 | 1 | choose (TLC cannot evaluate it) |
| nrkernel/mmu_rl1 | 95 | 0 | explicit holes require assignments |
| nrkernel/mmu_rl2 | 108 | 0 | explicit holes require assignments |
| nrkernel/mmu_rl3 | 101 | 0 | explicit holes require assignments |
| nrkernel/os | 135 | 7 | choose and integer type bounds |

Zero-refusal supplemental exports: **0/9 → 5/9**. The four MMU/OS rows use this repair's replay; the other five retain the prior measurement recorded under `collections_after_64f1c6e3`.

The lower trait lane now represents `KeyTrait::cmp_spec` and other uninterpreted trait functions as explicit table holes; zero refusals does not eliminate the need to supply interpretations. General closure/generic-call specialization remains outside this lane; no adapter was changed to bypass it. In particular, a carrier over an unresolved type parameter stays a refusal. The broad nrkernel MMU/OS exports now finish within the campaign time limit and pass SANY; export success does not establish a TLC result.

The nine supplemental modules have no saved `MC-command.json` in this campaign, so these are export-only measurements, not claimed TLC successes. Two modules do not define a discoverable transition triple. The before column uses the original campaign binary; improvements include lower-lane changes, especially bit operations and trait tables.

## Validation and remaining work

**210 exporter tests passed, 0 failed**, with `TLA2TOOLS_JAR` set. The vstd rebuild verified 2,045 functions with no errors. All 28 generated fixture files and all 22 saved campaign bound/configuration files compare byte-identically. The full golden regression and the separate raw re-export check both pass.

Seventeen new TLC-backed tests cover partial reads, carriers, recursive helpers and casts, lazy conditional values, invalidation of inferred shape facts, redundant guards, recursive substitution declarations, guard-only dependencies, bounded shared-helper analysis, Option projections in value helpers, and lexical scope of their guards. A separate golden regression pins Raft and every example's four generated files.

Remaining campaign limitations (not hidden as successful exploration):

1. NR needs a function-table interpretation and CrashTolerantMap needs its explicit `Dom_Key` carrier assignment. Neither was invented or added to the campaign configuration.
2. `os` retains seven `choose` / integer-type-bound refusals; `hlspec` retains its `choose` refusal.
3. Zero refusals in the supplemental exports still requires assigning their explicit holes before meaningful TLC exploration.


The documented `base/toydb` checkout does not contain `src/raft/safety.rs` on this box. The byte comparison therefore uses the existing `trace-arm-eval/toydb/src/raft/safety.rs`, with the same input path and source on both sides. The parent comparison binary was built in the clean sibling worktree at `6fc818ca`.

## Reproduction

Run from this worktree in a login shell:

```bash
export PATH=$HOME/.cargo/bin:$PATH
export TMPDIR=$HOME/tmp
export TLA2TOOLS_JAR=$HOME/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar
(cd source && timeout 900 ../tools/vargo/target/release/vargo test --release -p rust_verify_test --test tla_export -- --test-threads=4)
python3 audit/export-partial/replay.py partial final-before --verus ../base/verus/source/target-verus/release/verus
python3 audit/export-partial/replay.py anvil anvil-acceptance --verus source/target-verus/release/verus --jobs 2
python3 audit/export-partial/replay.py regressions bounded-final --verus source/target-verus/release/verus --jobs 2
python3 audit/export-partial/replay.py partial bounded-final-partial --verus source/target-verus/release/verus
python3 audit/export-partial/replay.py collections collections-before --verus ../base/verus/source/target-verus/release/verus
python3 audit/export-partial/replay.py collections acceptance-collections --verus source/target-verus/release/verus
python3 audit/export-partial/replay.py fixtures final-parent --verus ../wt-export-nrkernel/source/target-verus/release/verus
python3 audit/export-partial/replay.py fixtures bounded-final-fixtures --verus source/target-verus/release/verus
```

The helper requires the existing `../campaign-real` sources/results tree. Raw commands, exports, reports, and logs are retained locally in its output directories; compact measurements are committed here. No Cove `report` tool was available.
