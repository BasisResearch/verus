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

## Reproduction

Run from this worktree, using the login-shell environment required by the task:

```sh
export PATH=$HOME/.cargo/bin:$PATH
export TMPDIR=$HOME/tmp
source tools/activate
cd source
TLA2TOOLS_JAR=$HOME/.verus-tools-mcp/tlc/basis-11305b4a05/tla2tools.jar \
  timeout 1800 vargo test --release --vstd-no-verify \
  -p rust_verify_test --test tla_export -- --test-threads=4
```

`build-deps.py` rebuilds the campaign's temporal library and Kubernetes stub
inside this worktree. `campaign.py` reuses the exact six campaign sources,
module selectors and adapter options, changing only the exporter and rebuilt
library paths. Each export has a 90-second timeout. `regression.py` exports all
six `examples/tla` fixtures and toydb's Raft safety model with both binaries.
The requested `base/toydb/src/raft/safety.rs` is absent on this box; the existing
`toydb-pr-30/src/raft/safety.rs` is used for both sides instead.

The campaign has no saved TLC bounds/configurations for these six refused
machines. `network-smoke.py` supplies a separately reported supplemental bound:
one valid message, optional receive, empty/singleton send, and multiplicity at
most two, with a 30-second timeout. It reproduces the baseline refusal and
checks the changed network export under exactly the same bound.

## Results

Final counts, base revision, regression hashes, and remaining refusals are
recorded in `results.json` after validation. Generated modules, complete logs,
and rebuilt dependencies remain in the ignored evidence directories beside
this report; the scripts reproduce them without changing campaign inputs.

| Campaign machine | Refusals before | Refusals after | Contribution of this lane / remaining blocker |
|---|---:|---:|---|
| Anvil Cluster adapter | 22 | 62 | Reduces reachable action/helper records; reveals further callbacks from model maps and choices over closure records, which remain refused. |
| Anvil API action | 14 | 64 | Reduces parameterized action and finite set choice; exposes callbacks selected from installed-type maps, uninterpreted functions and character ordering. |
| Anvil API state machine | 16 | 8 | Reduces helper receivers; actions chosen from a set of closure records remain unresolved. |
| Anvil controller | 9 | 8 | Reduces action records and ordinary model fields; trait/uninterpreted bodies and an unresolved model value remain. |
| Anvil network | 2 | **0** | Lane 4 alone removes both action-field closure refusals. Supplemental TLC: **11 generated / 3 distinct states**, no errors. |
| IronKV host protocol | 6 | 4 | Removes two closure-literal argument refusals. Infinite-map construction, a full infinite set, a trait comparator, and an unbounded generic comprehension remain. |

Zero-refusal campaign exports: **0/6 → 1/6**. Completed supplemental bounded
TLC explorations: **0 → 1**. There are no saved campaign TLC configurations for
these machines, so an exploration count under the original campaign bounds
cannot be claimed. Increased refusal counts in Cluster/API come from reaching
bodies that used to stop at an outer closure refusal, not from deleting checks.

Additional stack checks: nrkernel `hlspec` **4 → 3** refusals, `os` **135 → 134**;
each now reports the bounded `choose` at `hlspec.rs:80–88`. Neither is counted
as explored. The remaining constructs are outside this lane's reduction rules.

At measurement, `origin/kg/export-partial` was `9abf2c0e`, still the common
starting commit. No new commits from lanes 1–3 had reached this base, so these
are cumulative counts for the stack actually available, with lane 4's
contribution identified above; no unlanded sibling work is credited. The base
is fetched and rebased again before publishing the PR.

All **28** generated `.tla`/`.cfg` artifacts for the six example fixtures and
the located toydb safety model are byte-identical. Hashes are in `results.json`.
