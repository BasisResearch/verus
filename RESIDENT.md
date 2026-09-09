# Resident AIR query server (S2)

`--resident` retains every selected bucket's lowered AIR queries and cvc5
context. After the compiler driver returns, one server lists and dispatches
queries over newline-delimited JSON on stdin/stdout. Each bucket owns its
solver process; queries can be rechecked across buckets in any order.

From `source`, after the normal build:

```sh
cargo run --release -p rust_verify -- --mcp -V cvc5 --resident path/to/input.rs
```

The usual module/function filters select which buckets and queries to
retain. `--num-threads` controls initial verification as usual, including
parallel preparation. Requests are currently dispatched serially.
The MCP authorisation gate still applies. This driver is not yet wired to
an MCP tool.

## Protocol

The driver finishes preparing all selected buckets, returns from the
compiler pipeline, then emits `ready`. Diagnostics from the original
invocation go to stderr. Each response occupies one line.
For example, a file containing `proof fn passing() {}` produces a response
of this shape (session, process ID and spans vary):

```json
{"event":"ready","protocol":2,"session":"123-456","process_id":123,"invocation_succeeded":true,"buckets":[{"id":0,"name":"root module","queries":[{"id":0,"function":"input::passing","description":"function body check","kind":"body","span":"path/to/input.rs:2:10: 2:22 (#0)"}]}]}
```

Send the returned session token with every check and close request. It is
optional on `list`, and checked when supplied:

```json
{"command":"list"}
{"command":"check","session":"123-456","bucket":0,"query":0}
{"command":"close","session":"123-456"}
```

Their corresponding responses are:

```json
{"event":"queries","session":"123-456","buckets":[{"id":0,"name":"root module","queries":[{"id":0,"function":"input::passing","description":"function body check","kind":"body","span":"path/to/input.rs:2:10: 2:22 (#0)"}]}]}
{"event":"checked","session":"123-456","bucket":0,"query":0,"result":"valid","assert_id":null,"diagnostics":[],"elapsed_ms":0,"restore_ms":0}
{"event":"closed","session":"123-456"}
```

An obligation's address is `(session, bucket, query)`. Query ordinals are
local to their bucket; bucket ordinals are local to their session. Buckets
are sorted by verifier identity, so worker completion order does not affect
their ordinals. Protocol 2 requires an explicit bucket even for a single
bucket; it replaces the draft protocol 1. Function names and assertion IDs
alone are insufficient. `kind`
distinguishes termination, body, recommends, recommends follow-up, expanded
and API safety queries. A function can contribute several queries.

`result` is the AIR verdict: `valid`, `invalid`, or `resource_limit`.
`invalid` means the verifier did not establish the obligation; it is not
a promise that cvc5 returned `sat`. A failed assertion carries its
`assert_id` when available, plus diagnostics with message, severity,
source spans and labels. This slice reports the first failing assertion
from each recheck. It does not rerun Verus's diagnostic expansion loop.
`elapsed_ms` includes AIR checking/lowering and solver work, after context
restoration; it is not an end-to-end request timing. `restore_ms` covers the
restoration that preceded it, which is the cost of moving between prefixes
rather than of the obligation itself. Neither includes time the caller spends
holding the pipe.

Unknown buckets/queries, wrong sessions, malformed JSON and unknown fields produce
an `error` response without running a query. Requests are limited to 64 KiB
including the newline. Oversized frames and invalid UTF-8 close the worker.
EOF closes every bucket without a response. `closed` is acknowledged only
after all solver processes have exited. Requests run serially; there is
no in-band cancellation command. A caller must discard the session after
a process or protocol failure.

A caller must drain stderr for the lifetime of the session. Diagnostics from
the original invocation and any later warnings go there, and a full stderr
pipe blocks the worker mid-request.

## Context and result boundaries

Compiler workers return owned bucket state to the verifier. The main
process takes that state after compilation and constructs the server.
Compiler callbacks never read protocol input. Incomplete preparation
(for example, an unsupported prover in a later bucket) releases retained
contexts and exits without publishing a partial catalogue.

Each retained bucket owns a mutex containing its AIR context and query
journal. Restoration, solving and cleanup occur under that bucket's lock;
poisoned state cannot serve another request. AIR diagnostic interfaces and
log sinks have explicit thread-safety bounds so workers can transfer their
contexts without unsafe code. No declarations are shared between buckets.

Each query retains the declaration prefix and resource limit used during
initial verification. Declaration batches occupy AIR/SMT scopes, but a scope
opens only where a retained query can return to it: consecutive batches that
no query separates share one. Scope depth and replay cost therefore follow the
number of retained queries, not the number of declaration batches, which is
roughly the size of the pruned call graph. On a three-function file importing
`vstd`, grouping takes the retained scopes from 86 to 4. Moving backwards pops
those scopes; moving forwards replays the retained batches, re-running each
declaration through AIR typechecking and the solver, so a jump still costs the
declarations between the two prefixes. Each recheck also opens and closes its own query scope.
This preserves the logical context even when query order changes. Solver
search history can still affect resource-sensitive outcomes.

The session refers to one in-memory compilation. Requests do not reread
source files, accept replacement assertions, or validate filesystem
changes. Close and start a new process after editing inputs or dependencies.
Snapshot invalidation belongs to the next MCP lifecycle slice.

`ready` means every selected bucket's AIR queries are available. Its
`invocation_succeeded` field reports the original invocation's result.
Failed assertions can still be inspected in a prepared session. The final
process status remains the status of the original invocation; successful
rechecks do not erase initial verification errors. A query result alone
does not establish whole-crate correctness.

The server retains one solver per bucket that actually invokes cvc5; empty
contexts launch lazily. Memory therefore scales with retained buckets.

Separate function buckets created by `#[verifier::spinoff_prover]` are
supported alongside module buckets. This slice rejects specialised query
provers (bit-vector, nonlinear and Singular), spinoff-all,
custom SMT options, provenance, profiling, compilation, debugger, inline
AIR and conflicting stdout modes. Ordinary invocations are unchanged.
Solver export/replay, cross-edit retraction and MCP lifecycle management
remain separate work.

## Regression tests

```sh
cargo test --release -p rust_verify --lib resident::tests
cargo test --release -p rust_verify_test --test resident
```

These require the normal Verus build and configured cvc5. The subprocess
tests run on Unix. They check repeated passing/failing queries, one solver
per active bucket, serial/parallel preparation, stable bucket addresses,
filters, balanced scopes, request rejection, optional session tokens on
`list`, EOF and shutdown of every child.
Two AIR tests cover the journal: later axioms cannot prove an earlier query
after their context is removed, including repeated removal and redeclaration
of names; and grouped declaration batches stay on the pinned side of a scope
boundary while a batch recorded after a query does not.
