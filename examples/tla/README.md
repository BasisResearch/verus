Three ways of writing a transition system in Verus, each exported to TLA+ by
`verus -V tla-export=<module> --log-dir <dir> <file>` (the flag is the Basis
fork's; see `vir/src/tla.rs`):

- `counter.rs`, hand-rolled: `init(s)`, `next(pre, post)` as an `exists` over
  a step enum, one relational spec fn per step, invariants as `(State) ->
  bool` spec fns. Module `counter`. The export model-checks under TLC with the
  same counts as a hand-written spec of the same counter (18 distinct states).
- `adder_sync.rs`, VerusSync: `state_machine!`. Module `adder_sync::Adder`.
  The step's `int` parameter is a hole the cfg bounds (`Dom_Step_add_v0`).
- `mutex_tla.rs`, verus-tla: `init()`/`next()` return closures and actions are
  `Action { precondition, transition }` records, reduced symbolically. Module
  `mutex_tla`. Its `init` is a predicate TLC cannot enumerate as written.
