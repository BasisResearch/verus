Three ways of writing a transition system in Verus, each exported to TLA+ by
`verus -V tla-export=<module> --log-dir <dir> <file>` (the flag is the Basis
fork's; see `vir/src/tla.rs`). The export is written under the log directory
as `<State>_tla.tla`, named after the module it declares so TLC can load it,
beside a `<State>_tla.cfg` skeleton and a `<State>_tla.tla.json` report of
what was recognised, refused and left unbounded.

- `counter.rs`, hand-rolled: `init(s)`, `next(pre, post)` as an `exists` over
  a step enum, one relational spec fn per step, invariants as `(State) ->
  bool` spec fns. Module `counter`. `Counter.tla`/`Counter.cfg` are the same
  system written by hand. Checked with `tlc2.TLC -deadlock -continue`, both
  give 28 states generated, 18 distinct, and the same six violations of
  `bounded` (`x` reaches 4); `sum_small` holds.
- `adder_sync.rs`, VerusSync: `state_machine!`. Module `adder_sync::Adder`.
  The step's `int` parameter is a hole: the `.cfg` lists `Dom_Step_add_v0`
  commented out, and TLC stops until it is given a finite set (and the model
  a `CONSTRAINT`, since `x` is unbounded).
- `toggle_sync.rs`, VerusSync with transitions that take no parameters. Module
  `toggle_sync::Toggle`. The macro generates `flip_enabled(pre)` and
  `reset_enabled(pre)`, which have an invariant's signature; the invariants
  are the conjuncts of the generated `State::invariant`, so only `n_nonneg`
  is checked, and the report lists the others as excluded candidates.
- `mutex_tla.rs`, verus-tla: `init()`/`next()` return closures and actions are
  `Action { precondition, transition }` records built by spec fns, reduced
  symbolically. Module `mutex_tla`. The export has no hole and no refusal and
  checks under TLC as written: 10 distinct states, both invariants hold.

The invariants are, by default, the `#[invariant]` methods for VerusSync,
every closure `() -> spec_fn(State) -> bool` for verus-tla, and every
`(State) -> bool` spec fn in the module for a hand-rolled model (one named
`invariant` included), except one that `init`/`next` read unprimed (a guard,
not an invariant). The report's `candidates` lists every candidate with
whether it was included and why. `-V tla-export=<module>:inv1,inv2` checks
exactly the named ones instead. When no invariant is checked, the `.cfg`
says so and lists the candidates with their reasons, since TLC with no
invariant reports "No error has been found".

A Verus state is always within its fields' types, so a step that would take
a `nat` below 0 or a `u8` past 255 is not a step at all. The export keeps
this with `TypeOK`: a range for every bounded integer the state holds,
directly or inside a record, an enum payload, a tuple or a `Seq`/`Set`/`Map`,
conjoined to `Init` and, primed, to `Next`. The report's `typed_variables`
lists the variables it constrains. TLC's integers are 32-bit, so a bound
beyond them (`u32`'s upper, `i32`'s, `u64`'s) is left out; TLC stops with an
overflow before reaching it.

Whatever the export cannot express is printed as `Assert(FALSE, "...")`, so
TLC stops with the reason wherever it is evaluated. An invariant that reaches
one is left out of the `.cfg` and listed in the report's
`skipped_invariants`.

A cast to a bounded type (`as u8`, `as nat`, ...) that widens (the operand's
own type lies in the target's, as `u8` in `u16` or `nat`) is the identity. A
narrowing one gives an out-of-range value some unspecified value of the
type in Verus, which TLC cannot express, so it is printed as a value check:
`LET c == e IN IF <c in range> THEN c ELSE Assert(FALSE, "... value out of
range of u8 in a cast at <location>")`. TLC stops only in a reached state
where the value leaves the type; `(pre.x - 1) as nat` behind `pre.x > 0`
never does. It is not a refusal and taints nothing. The check sits where the
cast is evaluated, so a guard written after the cast (TLC evaluates conjuncts
in order) does not protect it. A literal is decided at export: kept when in
range, refused when not.

An enum value's record carries its variant in the label `tag`, so a field
named `tag` (or `tag` followed by underscores) is labelled with one more
underscore (`tag_`), in a variant as in the state (whose variable is then
`tag_`).

A trait method call that Verus resolved to an impl (`s.view()` with `impl
View for State`) is exported as the impl's function.

A transition that constrains only some of the fields (`post.x == pre.x + 1`
and nothing about `y`) leaves the others unconstrained in Verus, but TLC
cannot build the successor and stops with "successor state not completely
specified". Likewise an `init` that constrains only some fields: TLC cannot
compute the initial states ("current state is not a legal state"). The
report's `init_unassigned` lists the variables `Init` never assigns (`x = e`
or `e = x` at conjunct level, followed through calls passing the state) and
the `.cfg` names them. The report's `transitions` lists each transition `Next` reaches
with the variables it never assigns (`unassigned`), and the `.cfg` names any
that leaves one unassigned. A transition is `Next` itself or an operator
called at conjunct level in a branch (a disjunct, an `IF` or `match` arm, an
`exists` body), together with the operators it conjoins. A variable counts as
assigned only by a conjunct-level `v' = e` (or `post == e` or `post =~= e`
for all of them), by a conjunct-level call to an operator that assigns it, or
by an `IF`, `match` or disjunction every branch of which assigns it (a
branch that is the literal `false` never holds and counts as assigning
everything, as VerusSync's `dummy_to_use_type_params => false` arm); a guard
reading `v'`, a predicate applied to the post state, or a negated equality
does not assign. A transition also counts what its callers assign around it,
so a frame condition factored out of a disjunction (`(a || b) && post.z ==
pre.z`) assigns `z` in both `a` and `b`. An operator that branches is
reported only for a variable none of its called branches is reported for. TLC assigns only a primed variable on the left, so
`pre.y == post.y` is printed as `y' = y`. With a primed field on both sides
(`post.x == post.y`), the one assigned earlier in the operator goes on the
right and the other is assigned; when neither is, nothing is, and the
transition is reported. What the check can miss: it does not look at
conjunct order, so a `v'` read before the conjunct that assigns it (which
stops TLC) is not reported; and it does not count `v' \in S`, so a
transition assigning that way is reported although TLC can enumerate it.

`rust_verify_test/tests/tla_export.rs` exports the four fixtures (as crate
`test_crate`, so the modules are `test_crate`, `test_crate::Adder`,
`test_crate::Toggle` and `test_crate`) and checks the reports. With `TLA2TOOLS_JAR` naming a
`tla2tools.jar` it also parses every export with SANY and model-checks the
counter against `Counter.tla`:

    TLA2TOOLS_JAR=/path/to/tla2tools.jar vargo test -p rust_verify_test --test tla_export
