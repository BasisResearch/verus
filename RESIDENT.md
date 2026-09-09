# Resident AIR queries (S2, first slice)

`--resident` retains one bucket's lowered AIR queries and cvc5 process after
initial verification. A caller can list queries, recheck them in any order,
and close the session over newline-delimited JSON on stdin/stdout.

From `source`, after the normal build:

```sh
cargo run --release -p rust_verify -- --mcp -V cvc5 --resident path/to/input.rs
```

Select a single module or function with the usual verification filters if
the input contains multiple buckets. Resident mode defaults to one thread.
The MCP authorisation gate still applies. This driver is not yet wired to
an MCP tool.

## Protocol

The driver performs initial verification, then emits `ready`. Diagnostics
from initial verification go to stderr. Each response occupies one line.
For example, a file containing `proof fn passing() {}` produces a response
of this shape (session, process ID and spans vary):

```json
{"event":"ready","protocol":1,"session":"123-456","bucket":"root module","process_id":123,"queries":[{"id":0,"function":"input::passing","description":"function body check","kind":"body","span":"path/to/input.rs:2:10: 2:22 (#0)"}]}
```

Send the returned session token with every check and close request:

```json
{"command":"list"}
{"command":"check","session":"123-456","query":0}
{"command":"close","session":"123-456"}
```

Their corresponding responses are:

```json
{"event":"queries","session":"123-456","queries":[{"id":0,"function":"input::passing","description":"function body check","kind":"body","span":"path/to/input.rs:2:10: 2:22 (#0)"}]}
{"event":"checked","session":"123-456","query":0,"result":"valid","assert_id":null,"diagnostics":[],"elapsed_ms":0}
{"event":"closed","session":"123-456"}
```

`query` is a session-local ordinal. Identify an obligation by session and
ordinal; function names and assertion IDs alone are insufficient. `kind`
distinguishes termination, body, recommends, recommends follow-up, expanded
and API safety queries. A function can contribute several queries.

`result` is the AIR verdict: `valid`, `invalid`, or `resource_limit`.
`invalid` means the verifier did not establish the obligation; it is not
a promise that cvc5 returned `sat`. A failed assertion carries its
`assert_id` when available, plus diagnostics with message, severity,
source spans and labels. This slice reports the first failing assertion
from each recheck. It does not rerun Verus's diagnostic expansion loop.
`elapsed_ms` includes AIR checking/lowering and solver work, after context
restoration; it is not an end-to-end request timing.

Unknown queries, wrong sessions, malformed JSON and unknown fields produce
an `error` response without running a query. Requests are limited to 64 KiB
including the newline. Oversized frames and invalid UTF-8 close the worker.
EOF closes the session without a response. Requests run serially; there is
no in-band cancellation command. A caller must discard the session after
a process or protocol failure.

## Context and result boundaries

Each query retains the declaration prefix and resource limit used during
initial verification. Later declaration batches occupy separate AIR/SMT
scopes. Moving backwards pops those scopes; moving forwards replays the
retained batches. Each recheck also opens and closes its own query scope.
This preserves the logical context even when query order changes. Solver
search history can still affect resource-sensitive outcomes.

The session refers to one in-memory compilation. Requests do not reread
source files, accept replacement assertions, or validate filesystem
changes. Close and start a new process after editing inputs or dependencies.
Snapshot invalidation belongs to the next MCP lifecycle slice.

`ready` means AIR queries are available, not that the crate verified.
The remaining compiler pipeline runs after the loop closes. The final
process status remains the status of the original invocation; successful
rechecks do not erase initial verification errors. A query result alone
does not establish whole-crate correctness.

This slice rejects multiple buckets, specialised/spinoff prover queries,
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
tests run on Unix. They check repeated passing/failing queries, one verifier
process and one solver launch, balanced scopes, request rejection, EOF and
unsupported modes. An AIR test checks that later axioms cannot prove an
earlier query after their context is removed, including repeated removal
and redeclaration of names.
