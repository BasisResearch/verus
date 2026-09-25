Three ways of writing a transition system in Verus, each exported to TLA+ by
`verus -V tla-export=<module> --log-dir <dir> <file>` (the flag is the Basis
fork's; see `vir/src/tla.rs`). The export is written under the log directory
as `<State>_tla.tla`, named after the module it declares so TLC can load it,
beside a `<State>_tla.cfg` skeleton and a `<State>_tla.tla.json` report of
what was recognised, refused and left unbounded. The export reads the
crate before verification, so with `--no-verify` it is written and nothing
is verified.

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
- `assert_sync.rs`, VerusSync with an `assert` in a transition. Module
  `assert_sync::Guarded`. The macro lowers the assert to `tmp_assert =>
  (update ...)`; Verus proves the assertion wherever the transition is
  taken, so the updates count as assigning and the transition is not
  reported. TLC checks it as written: 4 distinct states, `n_small` holds.
- `mutex_tla.rs`, verus-tla: `init()`/`next()` return closures and actions are
  `Action { precondition, transition }` records built by spec fns, reduced
  symbolically. Module `mutex_tla`. The export has no hole and no refusal and
  checks under TLC as written: 10 distinct states, both invariants hold.

The invariants are, by default, the `#[invariant]` methods for VerusSync,
every closure `() -> spec_fn(State) -> bool` over the state type for
verus-tla (a `() -> spec_fn(int) -> bool` helper is not one), and every
`(State) -> bool` spec fn in the module for a hand-rolled model (one named
`invariant` included), except one that `init`/`next` read, unprimed or
primed (a guard such as `busy(post) == false`, not an invariant), and
except one another selected invariant calls (`big` and `marked` in `inv(s)
= big(s) ==> !marked(s)` are checked inside `inv`; alone, `big` need not
hold). The report's `candidates` lists every candidate with
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

A quantifier's binder is bounded from its guard: membership in a set, a
map's domain or a sequence, or integer comparisons, chained ones included
and through binders bound later (`0 <= a < b < s.len()` bounds `a` by
`s.len() - 2`); a `#[trigger]` on a guard is looked through, and an
`exists` body that is a single guard (`exists|k| m.dom().contains(k)`) is
read as one. An integer binder's domain is intersected with its type's
range (`x < 300` over a `u8` is `0..255`), and the type closes a side the
guard leaves open (`x < 5` over an `i8` starts at -128). An unguarded
binder is bounded by its type alone only when that domain has at most 2^10
values: a `bool` or a `u8`/`i8` takes its whole range (`0..255`), a
datatype the union of its variants, and a tuple the tuples of its
elements' domains. A larger or unbounded one is a hole, a
`CONSTANT Dom_<type>` named after its type (`Dom_u16`, `Dom_u32`,
`Dom_int`, `Dom_Option_int_Some_v0`, a tuple's after its element types,
`Dom_tuple2_u8_u8_v0`), so TLC never tries to enumerate
65536 values per state. In a datatype, a variant whose fields together
take more than 2^10 values (`Step::Put(u16, u16)`, or `Step::Pair(u8, u8)`
with its 65536) has a hole for each field of more than one value
(`Dom_Step_Pair_v0`, `Dom_Step_Pair_v1`), which the `.cfg` supplies as
small sets; a small variant (`Step::Nudge(u8)`) is still enumerated whole.
The cap holds for the variants together too: when their union would take
more (five variants `A(u8, bool)` ... `E(u8, bool)`, 2560 values), every
variant of more than one value has a hole per field.

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

A recursive spec fn (one with `decreases`) has one operator only, its record
variant, which takes every parameter explicitly and the state as a record:
`sum(s, i)` called on the post state is `sum_rec([v |-> v', n |-> n'], i)`.
SANY gives every operator of a RECURSIVE group the highest level among them,
so an operator reading `v'` declared RECURSIVE makes the rest actions (and
the module is rejected). A recursive root, such as an invariant `cnt(s)`, is
a wrapper `cnt == cnt_rec([n |-> n, m |-> m])`, and only operators in a call
cycle are declared RECURSIVE. A spec fn given such a record, or any state
value other than the pre or post state (`k_le(State { k: 0, ..s }, 0)`), is
called in its record variant too (`ok_at_rec(s, i)`), so a recursive walk
can call a per-index predicate. A call that swaps the pre and post states is
a refusal as a whole.

A sequence literal `seq![a, b]` (an array literal viewed as a `Seq`) is the
tuple `<<a, b>>`.

A literal match pattern is an equality with the scrutinee (`0 => ...` is
`IF m = 0 THEN ...`) and a range pattern its comparisons (`1..=3` is `1 <=
m /\ m <= 3`).

A closure bound by `let` (or a closure parameter) is only ever applied; passed
to a function, compared or returned, it is a refusal.

A trait method call that Verus resolved to an impl (`s.view()` with `impl
View for State`) is exported as the impl's function.

A transition that constrains only some of the fields (`post.x == pre.x + 1`
and nothing about `y`) leaves the others unconstrained in Verus, but TLC
cannot build the successor and stops with "successor state not completely
specified". Likewise an `init` that constrains only some fields: TLC cannot
compute the initial states ("current state is not a legal state"). The
report's `init_unassigned` lists the variables `Init` never assigns (`x = e`
or `e = x` at conjunct level, followed through calls passing the state; `s.x
== s.y` assigns whichever of the two an earlier conjunct left unassigned,
and is printed with that one on the left; `s.o is None` and
`s.o.is_none()` are printed `o = [tag |-> "None"]` and assign `o`, and a
bare or negated bool field `s.done`, `!s.done` is printed `done = TRUE`,
`done = FALSE` and assigns `done`, as do the same on `post` in a
transition) and
the `.cfg` names them. The report's `transitions` lists each transition `Next` reaches
with the variables it never assigns (`unassigned`), and the `.cfg` names any
that leaves one unassigned. A transition is `Next` itself or an operator
called at conjunct level in a branch (a disjunct, an `IF` or `match` arm, an
`exists` body), together with the operators it conjoins. A variable counts as
assigned only by a conjunct-level `v' = e` (or `post == e` or `post =~= e`
for all of them), by a conjunct-level call to an operator that assigns it, or
by an `IF`, `match` or disjunction every branch of which assigns it (a
branch that is the literal `false` never holds and counts as assigning
everything, as VerusSync's `dummy_to_use_type_params => false` arm), or by
two conjunct-level implications of complementary guards whose consequents
both assign it (`pre.f ==> post.x == 1` beside `!pre.f ==> post.x == 2`, or
`x < 1`/`x >= 1`, `x == y`/`x != y`; TLC assigns in a consequent when its
guard holds, so one implication alone leaves the variable unassigned when
the guard fails), in Init as in Next; a guard
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

`rust_verify_test/tests/tla_export.rs` exports the five fixtures (as crate
`test_crate`, so the modules are `test_crate`, `test_crate::Adder`,
`test_crate::Toggle`, `test_crate::Guarded` and `test_crate`) and checks the reports. With `TLA2TOOLS_JAR` naming a
`tla2tools.jar` it also parses every export with SANY and model-checks the
counter against `Counter.tla`:

    TLA2TOOLS_JAR=/path/to/tla2tools.jar vargo test -p rust_verify_test --test tla_export
