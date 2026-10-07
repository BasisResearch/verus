# Partial reads and finite carriers — lane 3

**Draft: the full acceptance contract is not met.** The exporter tests pass and the six-machine replay improves, but the main TLA modules for `mutex_liveness.rs` and toyDB's `safety.rs` are not byte-identical to the parent branch. Their configurations and trace modules are unchanged. These differences are added definedness checks, not merely formatting. The PR must remain a draft until this compatibility requirement is resolved.

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

Analysis rendering uses an isolated exporter snapshot so it cannot duplicate holes/refusals or alter assignment bookkeeping. Returned local expressions reserve their bound names before an enclosing destructuring binding is named. Recursive helper checks and captured `let` values preserve their lexical scopes. Unresolved type parameters and analysis expansion limits remain source-located refusals.

## Six-machine acceptance replay

The committed `measurements.json` records the final counts and binary hashes. `replay.py` reconstructs each export from the saved campaign command and copies the original `MC.tla` and `MC.cfg` without changing their bounds. Every export is bounded by 90 seconds; every TLC invocation uses the campaign's one worker, 1 GiB heap, and 30-second limit.

Here “usable TLC run” means completion, an invariant counterexample, or continued exploration at the time limit **without an exporter evaluation or semantic-analysis failure**. The old runs did visit states before failing, so this is not a claim that they generated no states.

| Machine | Refusals before → after | TLC before → after | Distinct states before → after |
| --- | --- | --- | --- |
| nr/UnboundedLog-mono | 1 → 0 | evaluation/configuration error → evaluation/configuration error | 70 → — |
| splinter/AbstractJournal | 0 → 0 | evaluation/configuration error → complete | 27 → 72 |
| splinter/AbstractMap | 0 → 0 | evaluation/configuration error → evaluation/configuration error | 3 → 3 |
| splinter/CrashTolerantJournal | 0 → 0 | evaluation/configuration error → exploring at 30 s | 26 → 35 |
| splinter/CrashTolerantMap | 0 → 0 | evaluation/configuration error → evaluation/configuration error | 2 → — |
| splinter/LinkedJournal | 0 → 0 | evaluation/configuration error → invariant violation | 1 → 4 |

Timeout state counts are the last progress sample, not a completed search.

Zero-refusal exports improve **5/6 → 6/6** across the current stack. Usable bounded TLC runs improve **0/6 → 3/6**: one completes, one stops at an invariant violation, and one reaches the time limit while exploring. These counterexamples have not been promoted to source-system findings. They arise in the campaign's existing finite abstractions/adapters and now additionally carry the reported partial-read restrictions.

The NR replay uses the campaign's existing `UnboundedLog-mono` adapter on both sides. The lower trait lane now renders its former `vstd::pervasive::arbitrary` refusal as a typed table hole. The unchanged campaign configuration does not assign `Table_arbitrary__tla_closed2`, so NR does not start TLC on the final stack. The earlier pre-rebase result (an invariant violation after 754 distinct states) is superseded and is not counted. The unspecialized `nr/UnboundedLog` export is measured separately; the adapter's result is not represented as a successful generic-trait export.

CrashTolerantMap now exposes the explicit `Dom_Key` carrier for `TotalKMMap::empty` at `TotalKMMap_t.rs:25`. The saved configuration supplies structural field domains but not this new carrier, so its unchanged TLC configuration cannot start. No carrier assignment was invented to count it as an exploration success.

AbstractMap gets past its map-domain failures but still stops at the existing checked cast `(seq_end - 1) as nat` in `MsgHistory_v.rs:189` for an invalid history admitted by the saved bounds. No source guard or campaign bound was added to hide that failure.

## Total-collection campaign exports

| Module | Before refusals/status | After refusals/status | Remaining issue |
| --- | --- | --- | --- |
| nr/UnboundedLog | 4 | 0 | explicit holes require assignments |
| ironkv/delegation_map_t | no transition triple | no transition triple | no transition triple |
| ironkv/host_protocol_t | 6 | 0 | explicit holes require assignments |
| ironkv/host_impl_t | no transition triple | no transition triple | no transition triple |
| nrkernel/hlspec | 4 | 1 | choose (TLC cannot evaluate it) |
| nrkernel/mmu_rl1 | 95 | 189 | partial-read analysis exceeds its expansion limit |
| nrkernel/mmu_rl2 | 108 | 90 s export timeout | 90 s export timeout |
| nrkernel/mmu_rl3 | 101 | 90 s export timeout | 90 s export timeout |
| nrkernel/os | 135 | 90 s export timeout | 90 s export timeout |

Zero-refusal supplemental exports: **0/9 → 2/9**.

The lower trait lane now represents `KeyTrait::cmp_spec` and other uninterpreted trait functions as explicit table holes; zero refusals does not eliminate the need to supply interpretations. General closure/generic-call specialization remains outside this lane; no adapter was changed to bypass it. In particular, a carrier over an unresolved type parameter stays a refusal. The broad nrkernel MMU/OS exports are also measured for analysis limits and timeouts; their unsuccessful results are not counted as successful models.

The nine supplemental modules have no saved `MC-command.json` in this campaign, so these are export-only measurements, not claimed TLC successes. Two modules do not define a discoverable transition triple. The before column uses the original campaign binary; improvements include lower-lane changes, especially bit operations and trait tables.

## Validation and remaining work

Exporter suite with `TLA2TOOLS_JAR` set: **199 passed, 0 failed** after the final rebase. The vstd rebuild verified 2,045 functions with no errors. All 12 replay bounds/configuration files are byte-identical to the saved campaign. Compatibility: 26/28 generated `.tla`/`.cfg` files match the clean parent, with only the two main-module differences called out above.

Seven new TLC-backed regression tests cover reordered membership/variant/sequence guards, unguarded reads including direct negation, recursive value helpers, partial map constructors, destructuring-local hygiene, total/infinite collection operations, and carrier type assumptions. The former `ISet::finite` refusal test now checks its explicit finite carrier.

Priority order for remaining work:

1. Restore byte-identical main-module output for toyDB and `mutex_liveness.rs`. The analysis adds checks wherever it does not establish safety from the surrounding guards; proving which are redundant requires additional invariant/caller reasoning. Five of the six example main modules are identical, and every compared `.cfg` and trace module is identical.
2. Resolve AbstractMap's remaining checked-cast boundary without changing the campaign's transition relation or bounds.
3. Supply and document interpretations for the new trait/function table holes in a separate campaign configuration update. The unchanged NR configuration cannot run with the new table, and CrashTolerantMap needs an explicit `Dom_Key` carrier assignment. Preserve the distinction between generic NR and its existing monomorphic adapter.
4. Address the large-model analysis limits/timeouts recorded in the collection table before claiming broad nrkernel coverage.

The documented `base/toydb` checkout does not contain `src/raft/safety.rs` on this box. The byte comparison therefore uses the existing `trace-arm-eval/toydb/src/raft/safety.rs`, with the same input path and source on both sides. The parent comparison binary was built in the clean sibling worktree at `6fc818ca`.

## Reproduction

Run from this worktree in a login shell:

```bash
export PATH=$HOME/.cargo/bin:$PATH
export TMPDIR=$HOME/tmp
export TLA2TOOLS_JAR=$HOME/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar
(cd source && timeout 900 ../tools/vargo/target/release/vargo test --release -p rust_verify_test --test tla_export -- --test-threads=4)
python3 audit/export-partial/replay.py partial final-before --verus ../base/verus/source/target-verus/release/verus
python3 audit/export-partial/replay.py partial final-after --verus source/target-verus/release/verus
python3 audit/export-partial/replay.py collections collections-before --verus ../base/verus/source/target-verus/release/verus
python3 audit/export-partial/replay.py collections final-collections-after --verus source/target-verus/release/verus
python3 audit/export-partial/replay.py fixtures final-parent --verus ../wt-export-nrkernel/source/target-verus/release/verus
python3 audit/export-partial/replay.py fixtures final-fixtures --verus source/target-verus/release/verus
```

The helper requires the existing `../campaign-real` sources/results tree. Raw commands, exports, reports, and logs are retained locally in its output directories; compact measurements are committed here. No Cove `report` tool was available.
