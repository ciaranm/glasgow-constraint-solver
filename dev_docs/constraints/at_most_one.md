# `AtMostOne`: at most one variable of an array takes a given value

> **Maturity** production ·
> **Audited** 2026-09-30 at `c9ceea25`; re-audited 2026-10-08 at `0a5b4ec6`
> for #1121 ·
> **Open issues** none filed by this audit yet; see [Next steps](#next-steps)
> for what it would file. Already open and touching this family: #833 (the
> large-domain policy, which names this family's walk over the value variable),
> and #1128 (`SmartTable`'s per-call copies, which `AtMostOneSmartTable` pays).
> **Fixed since the audit**: #1121 (`AtMostOneSmartTable`'s child named no
> constraint in its hints), by #1182; see [Re-audit,
> 2026-10-08](#re-audit-2026-10-08). Tracked under #871.

### Re-audit, 2026-10-08

One fix touching this family has merged since the audit. This pass brings
the text into line with it at `0a5b4ec6`.

| Issue | Fixed by | What changed here |
|---|---|---|
| #1121, `AtMostOneSmartTable`'s child names no constraint (the `smart_table` audit's) | #1182 | `AtMostOneSmartTable::prepare` passes its ID to the child `SmartTable` (`at_most_one.cc:195`), so the child's hints name the posted constraint; the assertion-level paragraph under [Proof performance](#proof-performance), and [Tests](#tests) |

The native `AtMostOne` is unchanged: since `c9ceea25`, `at_most_one.cc`
differs by that one line only. #1213 (`SmartTable` entries outside the scope)
changes nothing for `AtMostOneSmartTable`, whose entries all name its own
scope.

**What was measured again.** Only the `smart` shape of the assertion-level
probe, at `AssertionLevel::Inferences` and `Off`, at `0a5b4ec6` on
fataepyc-10 (`tmp/fd871-comments-1008/tables/probes/am1_fam.cc`, a copy of
`tmp/fd-small/at_most_one/fam.cc`). Every other figure is from `c9ceea25`.

Two classes. `AtMostOne(vars, val)` is a native propagator with a
`Count`-shaped encoding: a flag per position meaning `vars[i] = val`, and one
row saying at most one flag holds. `AtMostOneSmartTable(vars, val)` is the
same constraint as a [`SmartTable`](smart_table.md), kept as a benchmarking
baseline; everything about its engine is that document's.

Five things to know before touching it.

- **It is generalised arc consistent on distinct variables, and not even
  `bounds(Z)` on repeated ones.** Two rules, both reading only which variables
  are fixed, reach GAC at every search node of 4,064 random instances with two
  or more positions, holes, views and constants included. `AtMostOne{{x, x}, y}`
  means `x ≠ y`, but the propagator waits for `x` to be fixed, and on repeated
  variables a bound can be left without a support. The answers are right either
  way.
- **It walks the value variable's whole domain on every call while that
  variable is unfixed**, scanning the array for each value. A call costs about
  `W · n` steps for a value variable of width `W`: 2.0 s to a first solution at
  `W = 10⁷` with three variables. Only a value that two variables are fixed to
  can ever be removed, so collecting the fixed values does the same job in
  `O(n log n)`; a tested patch is in [Next steps](#next-steps).
- **Only the C++ API and the `.scp` reader reach it.** MiniZinc's `at_most(1,
  x, v)` and `count(x, y) ≤ 1`, and XCSP3's `atMost`, all post `Count` with a
  counter in `0..1`. On an identical search tree that takes 1.5 to 1.8 times
  `AtMostOne`'s time and writes 1.8 times its proof lines, 4.2 times its
  bytes.
- **Every inference's reason is the whole scope**, every variable's domain,
  where two literals suffice.
- **Its encoding is `Count`'s from before #354**, strict `gt`/`lt` flags and
  an unlabelled row, where `cake_pb_cp`'s is today's `Count` encoding. The
  verified chain still passes; `opbdiff` cannot match a row.

## What it is

### Semantics

`AtMostOne(vars, val)` holds when at most one position `i` has
`vars[i] = val`. `val` is a variable, a view or a constant; so is each
position.

- **Empty array, or one variable:** trivially true. `prepare()` returns false,
  so nothing is installed and no OPB row is written. Both classes, tested.
- **`val` outside every domain:** true for every assignment. Tested
  (`{1..3}³`, `val = 5`).
- **All constants:** a count check at the root, both ways tested per #254.
- **A repeated variable** is accepted: `AtMostOne{{x, x}, y}` means `x ≠ y`,
  and `AtMostOne{{x, y, x}, z}` means `x ≠ z`. So is **`val` among the
  positions**: `AtMostOne{{x, y, z}, x}` means `y ≠ x` and `z ≠ x`, since `x`
  always equals itself. The native class enumerates the right solutions for
  all of these; see [Robustness](#robustness-and-limits) for their strength,
  and for the shapes `AtMostOneSmartTable` refuses.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `AtMostOne` | `decompose`: posts `Count`[^mzn] | `decompose`: `atMost` posts `Count`[^xcsp] | ?[^gcspy] | ✓ `at_most_one` | |
| `AtMostOneSmartTable` | n/a | n/a | — | ✓ `at_most_one_smart_table` | benchmarking baseline; see [`smart_table.md`](smart_table.md) |

[^mzn]: `minizinc/mznlib/fzn_at_most_int.mzn` is `glasgow_count_eq(x, v, z) ∧ z
    ≤ n` with `z ∈ 0..length(x)`. Flattening `at_most(1, x, 2)` (deprecated
    since 2.4.0, and warned about), `count(x, y) <= 1` and `count_geq(x, y, 1)`
    (MiniZinc's `count_geq(x, y, c)` is `c ≥ count`) with `build/glasgow.msc` on
    2.9.7 and 2.10.1 gives one `glasgow_count_eq` each, with the counter in
    `0..1`, and no other constraint (`tmp/fd-small/at_most_one/mzn/`; the
    `count_geq` flattening is the fact-check's,
    `tmp/fd-small/factcheck/at_most_one/mzn/`). That is `Count`, not a
    decomposition into primitives, but the cell vocabulary has nothing closer. A
    route to `AtMostOne` would be a front-end rewrite of `Count`, which the
    project does not do; see [Next steps](#next-steps).

[^xcsp]: `buildConstraintAtMost(value, k)` posts
    `Count{vars, constant(value), how_many}` with `how_many ∈ 0..k`.

[^gcspy]: `gcspy` binds neither class. Not checked further.

The `.scp` reader takes `(label at_most_one (vars...) val)` and
`(label at_most_one_smart_table (vars...) val)`, where `val` is a variable or
an integer, and rebuilds the matching class, so each term round-trips.
`scp_reader_test` enumerates one instance and round-trips another.

Positions are all that matter here: no value is an index, so an array indexed
from something other than 1 cannot be mistranslated the way #987's were.

### Options

`None.` There is no consistency tag and no algorithm switch. The choice between
the two classes is the caller's.

### Variable kinds and views

Plain variables, constants and views of either sign are accepted in every
position and as `val`, by both classes. The native propagator reads only
`optional_single_value()` and `each_value_immutable(val)`, which see through
views, and infers `≠` literals, which a view translates. The proof model's
flags are defined over the positions as written, so a view's offset lands in
the flag's defining row, not in a new auxiliary. Checked: the random sweep
below includes `x + c`, `c − x` and constants in every position and as `val`,
and the `views` probe (`{x0, x1 + 1, 3 − x2, x3}` against `y − 1`) enumerates
850 solutions with a verifying proof.

`AtMostOneSmartTable` gets views from `SmartTable`, whose view handling #238
fixed (8196bb11), and the test has run it under the view sweep since.

### Reification

`None.` No front end reaches either class, let alone a reified form.

### Relation to other families

- **Decomposes into it:** nothing. No front end, presolver or other constraint
  posts `AtMostOne`.
- **Child constraints:** `AtMostOneSmartTable` builds a `SmartTable` in
  `prepare()` and installs it; see [`smart_table.md`](smart_table.md), which
  documents its rows, rules and findings, and its benchmarks against this
  family. The native class has none.
- **Shares code:** none. The native propagator includes no helper from another
  family. Its encoding is `Count`'s old one (see [OPB encoding](#opb-encoding)),
  but copied, not shared.
- **Presolvers:** none reads it.
- **The merge question with `counting`:** separate, as the family list already
  has it. `AtMostOne` is `Count(vars, val, z)` with `z ≤ 1`, and every front end
  posts it that way, but the classes share no code, and `AtMostOne` exists to
  be the cheaper special case: on the benchmark below it is 1.5 to 1.8 times
  faster than `Count` on the same tree.
- **Not to be confused with** the at-most-one *lines* the proof layer recovers
  (`recover_am1`, `recover_am1_from_pairs`), which are derived facts inside
  other families' proofs, not this constraint.

## The proof model

### OPB encoding

For each position `i`, over the position and `val` as written:

```
g_i  ⇔  BinEnc(vars[i]) − BinEnc(val) ≥ 1        flag f[k][am1g]
l_i  ⇔  BinEnc(vars[i]) − BinEnc(val) ≤ −1       flag f[k][am1l]
e_i  ⇔  ¬g_i + ¬l_i ≥ 2                          flag f[k][am1eq]
Σ_i e_i ≤ 1                                      unlabelled
```

Each flag is written with both halves, so that is `6n + 1` rows and `3n`
flags, independent of any domain. **It is definitional:** `e_i` is exactly
`vars[i] = val`, and the last row is the constraint. It is the same whether or
not `val` is a constant; with a constant, the three flags restate what the
`vars[i] = c` atom already says, as they do for `Count`.

This is `Count`'s encoding as it was before `Count` was conformed to
`cake_pb_cp` under #354 (the aux-naming primitive for verified encodings); this
family was not conformed with it. The header still calls the model
"Count-style".

### Labels

`None.` The flags carry the proof model's generated names (`f[k][am1g]` and so
on), the row carries no label, and no rule cites a row: every inference is a
plain RUP.

### Cake conformity

`cake_pb_cp` has an `at_most_one` rule, and encodes it as Encoding Procedure
3.7 of McIlree's thesis, `Count`'s encoding exactly: flags
`x[id][i][ge] ⇔ vars[i] − val ≥ 0` and `x[id][i][le] ⇔ vars[i] − val ≤ 0`,
`x[id][i][eq] ⇔ ge + le ≥ 2`, and `Σ eq ≤ 1` labelled `@c[id][am1]`. Ours is
the same meaning with each flag negated (`g_i = ¬le_i`, `l_i = ¬ge_i`), so none
of the 19 rows the constraint writes matches: on `at_most_one_sat`, `opbdiff`'s
6 matches of 25 are the variables' bound rows, and ignoring auxiliary names
adds one more.

- `at_most_one_sat` (`{A, B, C} ⊆ 0..2`, `val = 1`, 20 solutions) and
  `at_most_one_unsat` are registered as `none`, and both chain-verify at
  `c9ceea25`.
- A variable `val` also chain-verifies (`(at_most_one (A B C) V)`, 60
  solutions, `tmp/fd-small/at_most_one/chain/varval.scp`), though no case
  registers one.
- `at_most_one_smart_table` does not chain. With a variable `val`, cake
  refuses the `.scp` (`expected integer, got: V`). With a constant, VeriPB
  rejects the solver's proof against cake's OPB at its first tuple step,
  `rup 1 ~f[0][t0] 1 ~i[C][eq1] >= 1`, which cites `SmartTable`'s own tuple
  flag `f[0][t0]`; cake's OPB, about the same size, names its tuple flags
  `x[_1][i]` under `@c[_1][al1]` and never defines `f[0][t0]`. The `.scp`
  reader's comment gives the OPB's size as the reason, which is not it.

The registration's comment groups this case with `all_different_except` and
`among` as diverging because "their per-value / per-pair encodings reference
the variables' eq/ge literals". That is not this family's reason: its rows
reference no order or equality literal, and the divergence is only polarity
and labels. Writing `Count`'s three flags and labelling the row `am1`, as
[Next steps](#next-steps) describes, makes a variable-`val` case `strict`. The
two registered cases use a constant `val`, and would still differ from cake in
one coefficient of two rows per position, exactly as `Count` with a constant
value of interest does today.

### Proof-time state

Nothing is emitted at the root, and there is no proof-only auxiliary beyond
the flags in the OPB. The family writes no scaffolding and deletes nothing
itself; its inference lines are written at the current search level, and the
shared backtrack machinery deletes them. The only other things its proofs
mention are the variables' order and equality literals, which the shared
literal layer introduces lazily when a reason or conclusion names them.

## The implementation

### Initialisation and global data

`prepare()` declines to install anything for fewer than two positions. There is
no initialiser. `install_propagators()` builds the whole-scope reason once,
`generic_reason(vars + val)`, and captures it; the domain walk it implies is
deferred until a proof-logging tracker materialises it.

`AtMostOneSmartTable::prepare()` builds `n` rows, row `i` saying every
position but `i` differs from `val`, installs the `SmartTable`, and returns
false.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| the at-most-one propagator | `on_change`, every position and `val` | derived: every variable; **really nothing** | 1, 2 | always, for two or more positions | never claims; is on distinct variables, and not when `val` is among the positions | never |

**The triggers overstate the holes.** Both rules read only which variables are
fixed, and to what. A hole in a position cannot fix it, and a hole in `val`
cannot fix `val` and only removes a value rule 1 might have removed, so no
removal strictly inside anyone's bounds can give this propagator an inference
it could not already make. But
`on_change` derives "affected" for every variable, so an `AtMostOne` keeps
every other constraint's optional interior pruning live on all of its
variables (see [Interior values](#interior-values-and-optional-pruning)). The
same fact makes every non-fixing domain change a wasted wake. `on_instantiated`
on every variable is exact; a tested patch is in [Next steps](#next-steps).

**Idempotence.** Not claimed, and not true of every shape. On distinct
variables one call is a fixpoint of both rules: rule 1 runs first and can only
fix `val`, which rule 2 then reads in the same call, since the tracker writes
each inference into the state at once; rule 2's removals are of `val`'s one
value from the other positions, which cannot fix a position to a value still
in `val`'s domain. **When `val` is (a view of) one of the positions it fails**,
because fixing `val` also fixes that position, after rule 1 has passed the
value it lands on. `AtMostOne{{x, y, w, z}, x}` with `x ∈ {0, 1}`, `y = 0` and
`w = z = 1`: rule 1 at 1 removes 1 from `val = x`, fixing `x = 0`, and now `x`
and `y` both equal `val`, which only a second call's rule 1 notices (2
propagations, unsatisfiable, the proof verifies;
`tmp/fd-small/at_most_one/idem.cc`, from the fact-check). Measured with an
instrumented build of `c9ceea25` that re-checks both rules at the end of every
call (`tmp/fd-small/at_most_one/patches/I.patch`): of 4.8 million calls in the
four per-node sweeps below and 1.6 million in the two orders of the
`n = d = 6` benchmark, none would have changed anything on a second call; this
audit's `val`-among-positions sweep happened never to produce the pattern. The
fact-check's sweeps (`tmp/fd-small/factcheck/at_most_one/gac.cc`) with `val`
among the positions find it in 8 of 21,816 calls (1,500 instances, seed 1), 82
of 281,188 (20,000 instances, seed 7), and 2 of 30,157 with views (1,500
instances, seed 1); none with repeated positions and `val` distinct (16,738
calls over 1,500 instances, 228,414 over 20,000). The engine already ignores idempotence
claims when positions alias, so a claim restricted to distinct variables would
be safe.

**Self-disabling.** Never. The propagator returns `Enable` on every call, even
when `val` is fixed, one position holds it and rule 2 has removed it from the
others, at which point the constraint is entailed. Each further call repeats
rule 2's scan and re-asserts its inferences, which are no-ops.

### Mutable state and incrementality

`None.` Nothing persists between calls. Every call walks `val`'s domain (rule 1)
and scans the array for each value; see [Interval
efficiency](#interval-efficiency) for what that costs.

### Interior values and optional pruning

**Offers.** `None.` The rules only remove a fixed value, and at their fixpoint
the constraint is already generalised arc consistent on distinct variables.

**Observes.** **Nothing, on any variable, but it declares everything.** Both
rules read fixedness only, so no hole affects this family's propagation, in the
sense of [`optional-interior-pruning.md`](../optional-interior-pruning.md). The
`on_change` triggers derive the opposite, and nothing sets
`Triggers::holes_affect_propagation`, so an `AtMostOne` over a variable is a
reason for somebody else's optional interior pruning on that variable to stay
on. That is the direction that is never unsound, only weaker. Switching the
triggers to `on_instantiated` fixes it.

### Robustness and limits

**Unbounded domains.** Correct at any width, and slow at wide `val`: see
[Interval efficiency](#interval-efficiency). The positions' widths do not
matter.

**Negative values and zero.** Tested: `at_most_one_test` runs `{−2..2}³` with
`val = 0`, and its random shapes reach from −2 to 8.

**Degenerate shapes.**

- *Empty, singleton, all constant, `val` outside every domain:* covered by the
  test.
- ***A repeated variable, or `val` among the positions***, is sound and not
  even `bounds(Z)`. `AtMostOne{{x, x}, y}` with `y = 0` fixed leaves
  `x ∈ 0..2`, though `x = 0` has no support; `AtMostOne{{x, y}, x}` with
  `y = 0` fixed does the same to `x`. The propagator sees a repeated position
  only once it is fixed, when rule 1 counts it twice. The per-node sweep below
  finds a node failing GAC in 816 of the 1,864 instances with a repeated
  variable, and `bounds(Z)` in 734; with `val` among the positions, 664 and
  629 of 996. **Aliases through different views are not `bounds(Z)`
  either**, though they fail far less often: `AtMostOne{{x, y}, 2 − x}` with
  `y = 1`, and `AtMostOne{{x, 2 − x}, y}` with `y = 1`, both leave `x ∈ 1..2`
  at the root though `x = 1` has no support
  (`tmp/fd-small/at_most_one/viewalias.cc`, from the fact-check). In the sweep
  mixing views, constants and aliases (`am1check.cc`, shape `all`, seed 1), GAC
  fails in 718 of the 1,699 instances with two or more positions and an alias,
  and `bounds(Z)` in 547; of the 518 whose only aliases are through different
  views, GAC fails in 27 and `bounds(Z)` in 6 (the split is the re-check's
  `tmp/fd-small/at_most_one/am1check_v.cc`). Many such aliases can never
  coincide: `{x, x + 1}` against `y` never has both equal to `y`. No instance
  without an alias fails, and no instance has a wrong or missing solution. The
  duplicate runs in the test check solutions only.
- *`AtMostOneSmartTable`* is GAC on exact repeats too (937 instances with a
  repeated variable, every node), because `SmartTable` is. It **refuses**
  three shapes the native class accepts, each with an exception from
  `solve_with`, not from `post`:
  - `val` among the positions, and a constant position equal to a constant
    `val` (`AtMostOneSmartTable{{2, x, y}, 2}`): a row entry `≠` over one
    underlying variable, which `SmartTable` rejects as a binary entry with
    aliased endpoints. So does `AtMostOneSmartTable{{x, x}, x}`, which is
    simply unsatisfiable;
  - a variable repeated under two different views, with three or more
    positions (`{x, x + 1, z}` or `{x, 2 − x, z}` against `y`): the row for
    `z` holds both `x ≠ y` and `x + 1 ≠ y`, two entries joining `x` to the
    same `val`, and `SmartTable` rejects a tuple whose binary entries form a
    cycle. It does so when `val` or the third position is a constant too
    (`{x, x + 1, z}` against 2, `{x, x + 1, 2}` against `y`). With two
    positions each row has one such entry, and an exact repeat is allowed (`tmp/fd-small/at_most_one/smartshapes.cc`, from the
    fact-check).

**Overflow.** None. The propagator does no arithmetic, and the encoding's rows
are `vars[i] − val` over bit sums, which the proof model writes like any
two-term linear row.

### Interval efficiency

**Not fine at width, on one site, and the fix is simple.**

1. **The propagation side.** Rule 1 is `for (v : each_value_immutable(val))`,
   and for each value a scan of the array, stopping at two matches. With `val`
   unfixed that is `Θ(|dom(val)| · n)` per call, whatever the positions look
   like; it is a per-value loop with no interval structure being exploited, and
   none needed, since only a value two positions are fixed to can be removed,
   and there are at most `n/2` of those. Measured with proofs off on the
   Release build of `c9ceea25`, fataepyc-10, pinned, one run each,
   2026-09-30 (`tmp/fd-small/at_most_one/wide.cc`): three positions and `val`
   over `0..W`, branching on the positions and then `val`, to the first
   solution. Of the six propagator calls, five find `val` unfixed and walk
   (counted by the instrumented build), so at `W = 10⁷` a walking call costs
   about 0.4 s:

   | W | Time to first solution | Recursions | Propagations |
   |---|---|---|---|
   | 10⁵ | 0.021 s | 5 | 6 |
   | 10⁶ | 0.205 s | 5 | 6 |
   | 10⁷ | 2.04 s | 5 | 6 |

   With ten positions at `W = 10⁷` it is 13.1 s for 13 propagations. The same
   model posted as `Count` takes 3.66 s at 10⁷, and branching on `val` first
   takes the native class 0.27 s, since only the root call walks. Rule 2 is an
   `O(n)` scan, and nothing else walks a domain.
2. **The reason side.** Every inference's reason is `generic_reason` over the
   whole scope, materialised per run, not per value (#935), and only by a
   proof-logging tracker, so it costs nothing with proofs off. With proofs on it
   is `O(n + runs)` literals per inference, including the runs of `val`'s own
   holes, which rule 1 creates; the minimal reason is two literals.
3. **The proof side.** One RUP line per inference, no second form, so nothing
   for a width gate to choose. The encoding is logarithmic in width.
4. **The audit lane.** Two rows, both `KnownTrip`: `AtMostOne{wide(3),
   wide_var}` and the same for `AtMostOneSmartTable`, three positions and `val`
   over `wide_lo..probe_width`. On the guard build of `c9ceea25` the native row
   trips in rule 1's generator, at 100,001 values yielded. The rows do not vary
   holes, views, a constant or fixed `val`, or repeats, and never reach rule 2.
   The native row's comment says an aliased `val` "is rejected at post time";
   neither class rejects one at post, and only `AtMostOneSmartTable` rejects
   it at all, from `solve_with`.
   With the fix in [Next steps](#next-steps), on a guard build of `c9ceea25`,
   the native row survives: it reports a mismatch against its `KnownTrip` pin,
   the lane's only failure, and the SmartTable row still trips.

## Inference catalogue

Two rules. A conflict is not a third: rule 1 removing `val`'s last value, or
rule 2 removing a position's last value, is an ordinary inference of a literal
that is already false, and the tracker asserts it with its reason, closed by
the backtrack.

Four facts hold for both rules.

**Each is a bare RUP, and the procedure is ours, resting on Theorem 2.8.**
McIlree's thesis covers at-most-one (Encoding Procedure 4.3) only as a smart
table, the decomposition `AtMostOneSmartTable` builds, justified by the smart
table procedure; it has no procedure for this direct flag encoding. The argument
here is JP 3.1's with the encoding's flags in the middle. The negated conclusion
is an equality literal (`val = v` for rule 1, `vars[j] = v` for rule 2), and two
literals of the reason are equalities with the same value (`vars[i] = v` and
`vars[j] = v`, or `val = v` and `vars[k] = v`). Theorem 3.3 takes each equality
literal to its two bounds, and Theorem 2.8 then fixes every bit of the three bit
sums. Each flag row `g ⇔ vars[i] − val ≥ 1` and `l ⇔ vars[i] − val ≤ −1` is then
over fully assigned sums, so both halves propagate: `¬g` and `¬l` for the two
positions that equal `v`. The `e` rows force both `e` flags, and `Σ e ≤ 1`
conflicts. The reason comes along by Theorem 2.6. See
[`justification-techniques.md`](../justification-techniques.md). A justifier
replays it by unit propagation alone, so **Offline reconstructibility** is
`offline` for both rules, and **Proof size** is one line.

**The reason is the whole scope, and not minimal.** It is every variable's
domain, lower and upper bound plus one literal per run of holes, or the one
equality for a fixed variable. Only two of those literals are needed. The
extra ones are true, so they do not weaken the clause's validity, but they
lengthen every assertion a justifier must trim: a 4-position rule-1 assertion
measured at `Inferences` carries nine literals where three would do. See
[Next steps](#next-steps).

**There is one wire form.** `hints::AtMostOne`, `(constraint_id <id>)`, no
subhint and no payload.

**No justification reads `state`,** and there is no `JustifyExplicitly`.

### Rule: value-used-twice

- **Infers** — `val ≠ v`, for each `v` in `val`'s domain that two or more
  positions are fixed to.
- **Fires when** — any variable's domain changes; first in each call of the
  propagator.
- **Strength** — `GAC` on distinct variables, together with rule 2. A value
  `w` of `val` has a support unless two positions are fixed to `w` (each
  unfixed position can move off `w`), which is exactly this rule. A value `a`
  of a position `i` is unsupported only if every `w` in `val`'s domain is
  matched by two positions once `i` takes `a`; after this rule every remaining
  `w` has at most one fixed position, so that needs `val`'s domain to be `{a}`
  and another position fixed to `a`, which is rule 2. Checked by brute force at
  every search node (`tmp/fd-small/at_most_one/am1check.cc`, seed 1, domains in
  `−1..3` with holes, up to five positions): no GAC failure in 3,000 instances
  over plain variables (437,732 nodes) or 3,000 with views and constants
  (381,285 nodes), of which 2,006 and 2,058 have the two or more positions that
  install anything. On repeated variables, or `val` among the positions, not
  even `bounds(Z)`; see [Robustness](#robustness-and-limits).
  `at_most_one_test` also checks GAC at every node. Its initial domains are
  intervals, but its brancher, `reject_random_interval`, rejects interior
  intervals, so later nodes see holes: a probe with the same branching pair
  (`variable_order::random(p, s)`, `value_order::reject_random_interval(s +
  1)`) on three positions and `val`, all in `0..3`, has a hole at 156 to 177
  of its 215 trace callbacks for seeds 1 to 5
  (`tmp/fd-codex-1005/small/probes/holes.cc`; a probe of the brancher, not a
  count inside the test).
- **Algorithm** — a walk over `val`'s domain, and for each value an array scan
  stopping at the second match: `Θ(|dom(val)| · n)` per call, **in values**.
  See [Interval efficiency](#interval-efficiency).
- **Why it is true** — if `val = v` and two positions equal `v`, two positions
  equal `val`.
- **Proof technique** — `RUP`. **No published procedure for this encoding**
  (the thesis's Encoding Procedure 4.3 is the smart-table one); ours, through
  **Theorem 2.8**, as in the preamble: the negated conclusion `val = v` and the
  reason's `vars[i] = v`, `vars[j] = v`.
- **Reason** — the whole scope, as the preamble says. Minimal would be
  `{vars[i] = v, vars[j] = v}`. Not guarded on `want_reasons()`, but lazy: the
  captured `GenericReasonOver` is materialised only by a proof-logging
  tracker.
- **Assertion** — `val ≠ v ∨ ¬reason`. Measured at `Inferences` on the `var`
  probe (four positions over `0..3`, `y ∈ 0..3`):
  ```
  a 1 ~i[y][eq0] 1 ~i[x[0]][eq0] 1 ~i[x[1]][eq0] 1 ~i[x[2]][ge0] 1 i[x[2]][ge4] 1 ~i[x[3]][ge0] 1 i[x[3]][ge4] 1 ~i[y][ge0] 1 i[y][ge4] >= 1::at_most_one:((constraint_id _1));
  ```
  The first three literals are the clause; the other six are unfixed
  variables' bounds.
- **Hint** — `hints::AtMostOne`: `originator`, the `ConstraintID`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per inference, whatever the width; the line has
  `O(n + runs)` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` No mutation lane exists for this family. The
  corruption to try is dropping one of the two fixed positions from the
  reason.

### Rule: only-holder

- **Infers** — `vars[j] ≠ v` for every position `j` other than the one fixed to
  `v`, when `val` is fixed to `v` and exactly one position is fixed to `v`.
- **Fires when** — any variable's domain changes; after rule 1, in the same
  call, so it sees a `val` that rule 1 has just fixed.
- **Strength** — `GAC` on distinct variables, with rule 1; see there.
- **Algorithm** — one scan to count and locate the fixed positions, then one
  `infer` per other position: `O(n)` per call. It re-infers on every call once
  it has fired, since the propagator never disables; the repeats are no-ops.
- **Why it is true** — `val = v` and `vars[k] = v`, so any other position equal
  to `v` would be a second.
- **Proof technique** — `RUP`. **No published procedure for this encoding**
  (the thesis's Encoding Procedure 4.3 is the smart-table one); ours, through
  **Theorem 2.8**: the negated conclusion `vars[j] = v` and the reason's
  `val = v`, `vars[k] = v`.
- **Reason** — the whole scope. Minimal would be `{val = v, vars[k] = v}`.
- **Assertion** — `vars[j] ≠ v ∨ ¬reason`. Measured at `Inferences`:
  ```
  a 1 ~i[x[3]][eq1] 1 ~i[x[0]][eq0] 1 ~i[x[1]][eq0] 1 ~i[x[2]][eq1] 1 ~i[x[3]][ge0] 1 i[x[3]][ge4] 1 ~i[y][eq1] >= 1::at_most_one:((constraint_id _1));
  ```
  Here `x[2] = 1` and `y = 1` are the reason; `x[0] = 0` and `x[1] = 0` are
  fixed positions that do not matter, and `x[3]`'s own bounds are in it too.
- **Hint** — `hints::AtMostOne`: `originator`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per inference.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

- **`at_most_one_test`** (`at_most_one_constraint`, plus
  `at_most_one_constraint_view_mixed`): for both classes, a fixed list of
  shapes (empty, singleton, two positions, three and four with fixed and
  variable `val`, `val` outside every domain, a negative range, forced
  propagation, an unsatisfiable pair, all-constant shapes per #254) and ten
  random shapes of two to five positions, each a range from `−2..4` up to four
  wider, with a `val` range drawn the same way. Each runs with and without
  proofs under `solve_for_tests_checking_gac`, so every value left at every
  node is checked against the solution set. VeriPB runs when it is on the path.
  Seeded (`--seed`).
- **Duplicate-variable runs**, both classes, bare lanes only: `{x, x}`,
  `{x, x, y}` and `{x, y, x}` over `1..3`, under plain `solve_for_tests`, so
  solutions and the proof but no consistency check.
- **`smart_table_dup`** (`smart_table_dup_test`), since #1182: posts
  `AtMostOneSmartTable` as a problem's only constraint, solves it at
  `AssertionLevel::Inferences`, and requires `smart_table` hints that name
  the posted constraint and none that says `unnamed`
  (`smart_table_dup_test.cc:162-168`).
- **`scp_chain_at_most_one_{sat,unsat}`**, and `scp_reader_test`'s enumeration
  and round trip: see [Cake conformity](#cake-conformity).
- **Audit lane:** the two rows; see [Interval efficiency](#interval-efficiency).

**Runtime caps.** No lane sets or clears one, and the default caps fire on two
runs per lane: in the bare lane, 2 of 132 runs are truncated, and in
`view_mixed` 2 of 120 (`GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500
at_most_one_test --seed=1`, and the same with `--view-position=mixed`, at
`c9ceea25`). Both are random shapes with proofs on: a native one with 345
solutions and a SmartTable one with 1,304, each stopped at 300 and checked for
soundness only. Every fixed shape runs complete.

**Tightness:** no mutation lane, and no refusal shown by hand.

**What the tests do not cover.**

- **Holey initial domains.** Every tested domain starts as an interval. The
  per-node GAC check does see holes, cut by the brancher (see rule 1's
  Strength), and the per-node sweep above starts from holey domains. No test
  posts another constraint that makes holes during search; since no hole
  affects this family's propagation, that matters only for wake counts (see
  "The triggers overstate the holes" under [Propagator
  inventory](#propagator-inventory)).
- **A wide `val`**, which is the family's one width hazard; only the audit
  lane's root probe reaches it.
- **The consistency of the repeated shapes**, deliberately: the duplicate runs
  check no level, and they never put `val` among the positions.
- **Real instances:** none; no front end posts the family.

### Benchmarks and examples

- **In the repository:** `smart_table_am1` (`--n`, default 3) posts
  `AtMostOneSmartTable`, as a `SmartTable` smoke test. Nothing posts
  `AtMostOne`.
- **Corpus:** none can reach it, since MiniZinc and XCSP3 post `Count`.
- **For CPU:** the enumeration below, which reaches both rules and has a
  closed-form solution count. With `val` branched first neither solver
  fails, and both enumerate the same solutions; the trees differ, because the
  branching schemes do (below).
- **For proof verification:** the same enumeration at `n = d = 4` or 5.
  Its size tracks the solution count.

### CPU performance

*Release build of `c9ceea25` (GCC 15.2.0, `-O3 -march=native`); Gecode 6.3.0,
built locally; fataepyc-10, boost off, pinned with `taskset -c 17`,
`GLIBC_TUNABLES` fixing the malloc thresholds; median of five runs, each within
5% of the others except one `Count` run 16% above its median; wall time of the
whole solve, proofs off; 2026-09-30.*

Enumerating every assignment of `x[0..n−1]` and `y` over `0..d` with at most
one `x[i] = y`, branching in input order on the smallest value, either `y`
first or `y` last (`am1_gcs.cc`, `am1_gecode.cc` in
`tmp/fd-small/at_most_one/bench/`). There are `(d + 1)(dⁿ + n·dⁿ⁻¹)`
solutions. GCS posts `AtMostOne`, or `Count{x, y, z}` with `z ∈ 0..1`, which is
what MiniZinc would give it; Gecode posts `count(x, y, IRT_LQ, 1)`.

| n | d | order | Solutions | GCS `AtMostOne` | GCS `Count` | Gecode `count` |
|---|---|---|---|---|---|---|
| 6 | 6 | `y` first | 653,184 | 0.770 s | 1.231 s | 0.213 s |
| 6 | 6 | `y` last | 653,184 | 0.898 s | 1.605 s | 0.339 s |
| 7 | 6 | `y` first | 4,245,696 | 5.440 s | 8.293 s | 1.436 s |
| 7 | 6 | `y` last | 4,245,696 | 6.473 s | 11.200 s | 2.529 s |

| n | d | order | GCS recursions | GCS failures | propagations, `AtMostOne` / `Count` | Gecode nodes | Gecode failures |
|---|---|---|---|---|---|---|---|
| 6 | 6 | `y` first | 770,757 | 0 | 781,642 / 1,162,666 | 1,306,367 | 0 |
| 6 | 6 | `y` last | 790,441 | 0 | 842,696 / 1,478,835 | 1,647,085 | 170,359 |
| 7 | 6 | `y` first | 5,016,453 | 0 | 5,081,770 / 7,367,914 | 8,491,391 | 0 |
| 7 | 6 | `y` last | 5,206,496 | 0 | 5,585,343 / 9,712,354 | 11,529,601 | 1,519,105 |

- **With `y` first none of the three searches fails**, and all three
  enumerate the same solutions. Gecode's tree is not GCS's: `smallest_first`
  gives a variable one child per value, where Gecode's `INT_VAL_MIN` branches
  in two, so the internal nodes, the intermediate domains and the propagation
  work all differ (770,757 GCS recursions against 1,306,367 Gecode nodes at
  `n = d = 6`). The two GCS models do share one tree. **GCS takes 3.6 and 3.8
  times Gecode's time** for the whole enumeration. As for
  [`increasing`](increasing.md), a whole-solve comparison on a benchmark with
  no failures measures the search loop and the solution callback as much as
  the propagator.
- **With `y` last Gecode prunes less**: it fails 170,359 and 1,519,105 times
  where GCS never does, and is still 2.6 times faster.
- **`Count` on the same tree takes 1.60 and 1.52 times `AtMostOne`'s time with
  `y` first, 1.79 and 1.73 with `y` last**, with 1.45 to 1.75 times the
  propagations. That is the price every MiniZinc and XCSP3 at-most-one pays
  today; it belongs to [`counting`](counting.md) (#1029 measures `Count`
  against a one-value `GlobalCardinality` on a constant value of interest),
  not to a front-end rewrite.
- `AtMostOneSmartTable`, on the same trees at `n = d = 6`, takes 17.1 s with
  `y` first and 25.2 s with `y` last, 22 and 28 times `AtMostOne`'s 0.771 s
  and 0.901 s (medians of three, same setup, `tmp/fd-small/at_most_one/bench/smartbench.txt`).
  [`smart_table.md`](smart_table.md#cpu-performance)'s 17 to 23 times is a
  different series, with `y` fixed.
- **What the benchmark does not exercise:** conflicts (there are none), wide
  domains, holes, views, repeats.

### Proof performance

*Same build and machine. `am1_gcs native ylast n d p`: the enumeration above
with `y` last, VeriPB 3.0.2 with `--force-checked-deletion`; one run each.*

| n = d | Solutions | Lines, `Off` | Bytes, `Off` | This family's lines | VeriPB, `Off` | Lines, `Inferences` | VeriPB, `Inferences` |
|---|---|---|---|---|---|---|---|
| 3 | 216 | 2,114 | 58.2 KB | 28 | 0.03 s | 1,611 | 0.02 s |
| 4 | 2,560 | 21,930 | 684 KB | 285 | 0.27 s | 18,277 | 0.17 s |
| 5 | 37,500 | 307,306 | 10.9 MB | 3,516 | 5.1 s | 260,029 | 40.2 s |

"This family's lines" is the count of `a` lines carrying the `at_most_one` hint
at `Inferences`, one-for-one with the rule firings. **The family is about 1% of
its own enumeration proof** (3,516 of 307,306 lines at `n = 5`). The rest is
87,846 `del`, 84,331 comment lines (27%), the remaining 46,844 `rup` of the
backtracking, 47,054 `core`, 37,500 `solx`, and the shared literal layer's 156
`red` and 55 `pol`. Its rows add `6n + 1` to the OPB.

- **`Count` writes 1.8 times the proof lines on the same tree, and 4.2 times
  the bytes**: 547,251 lines and 45.2 MB at `n = 5`, against 307,306 and
  10.9 MB, and 12.1 s to check at `Off` against 5.1 s.
- **Checking at `Inferences` is slower than at `Off` here, and it is not this
  family's doing.** At `n = 5` it is 40.2 s against 5.1 s, and `Count`'s proof
  of the same tree goes from 12.1 s to 50.8 s. At `Inferences` the search's
  own backtracking and solution-blocking steps are assertions as well (84,331
  of the 87,847 `a` lines; the family's 3,516 are 4%), and the proof has
  50,346 `del` lines against `Off`'s 87,846. What makes VeriPB slower on it was
  not isolated.

**Assertion levels.** At `Off` every probe proof verifies (`var`, `const`,
`views`, `xx`, `valalias` and `smart` in `tmp/fd-small/at_most_one/fam.cc`).
At `Definitions` and `Inferences` VeriPB accepts each with `s UNDER
ASSERTIONS`: every one of this family's inferences is an `a` line there (136 of
136 at `Definitions` on `var`). At `Links` none is accepted: each fails at a
`solx` step, which is generic, as the other families' probes show. Of the
`Inferences` assertions on `var`, 136 of 1,945 carry this family's hint.
`AtMostOneSmartTable`'s carry `smart_table:((constraint_id _1))`, the posted
constraint's ID, since #1182: on `smart` at `0a5b4ec6`, 136 of the 1,945 `a`
lines carry it, and none says `unnamed`; before #1182 every `smart_table`
hint did (#1121). The other `a` lines are the search's own (`backtrack` and
`solx_block` hints), which never named a constraint.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is justified at `Off`, and the propagator is the same
with proofs on or off.

### Known limitations

- **A wide value variable makes every call slow.** While `val` is unfixed each
  call costs time proportional to its domain's width times the array's length:
  about 0.4 s per call at `10⁷` values and three positions.
- **A repeated variable, or `val` among the positions, is propagated late.**
  `AtMostOne{{x, x}, y}` does not remove `y`'s value from `x` until `x` is
  fixed, and fails then. The answers are right.
- **No front end posts it.** MiniZinc's and XCSP3's at-most-one go to `Count`,
  which is slower on the same tree.
- **`AtMostOneSmartTable` throws** when `val` is among the positions, when a
  constant position equals a constant `val`, and when a variable is repeated
  under two different views with three or more positions.

### Next steps

The first four are independent in effect, and were each tested as a patch against
`c9ceea25`, alone and together (`tmp/fd-small/at_most_one/patches/`, one
`.patch` per letter; `ABCD2.patch` is the four together). Each passes
`at_most_one_test` uncapped (`GCS_TEST_MAX_SOLUTIONS= GCS_TEST_MAX_RECURSIONS=`,
bare and `view_mixed` lanes, 126 of 126 proofs `VERIFIED`), gives exactly the
same nodes and verdicts as the unpatched build in all four per-node sweeps,
and verifies the probe proofs of every shape at `Off`. Timings are medians of
five pinned runs of the `n = d = 6` benchmark, as in [CPU
performance](#cpu-performance), against an unpatched build of the same tree
(0.767 s with `y` first, 0.886 s with `y` last).

1. **Collect the fixed values instead of walking `val`'s domain** (patch A).
   Rule 1 can only remove a value two positions are fixed to, so gather the
   positions' fixed values, sort them, and test each repeated one against
   `val`'s domain: `O(n log n)` per call, independent of width, and the same
   inferences in the same order. The first solution at `W = 10⁷` goes from 2.04
   s to under 0.1 ms with three positions, and from 13.1 s to about 0.1 ms with
   ten. The benchmark is 0.750 s with `y` first and 0.755 s with `y` last (−2%
   and −15%: with `y` last, the 189,512 calls that find `y` unfixed each walked
   up to seven values; the other 653,184 are solution leaves). The audit row
   should then be pinned `Clean`, and gain a sibling with `val` fixed and one
   with holes. Small, and the one that matters. Filed as #1155, under #833.
2. **Trigger on instantiation** (patch B). `on_instantiated` on every position
   and on `val` is exact, as [the inventory](#propagator-inventory) argues, and
   derives "holes affect nothing" for every variable, which is the truth. It
   saves the wakes on non-fixing changes: propagations fall from 781,642 to
   770,757 with `y` first and from 842,696 to 790,441 with `y` last, one call
   per search node in both, and time to 0.754 s and 0.853 s (−2%, −4%). Trivial.
   Filed as #1156.
3. **Give two-literal reasons, built only when wanted** (patch C2). Rule 1's
   reason is the first two positions fixed to `v`, rule 2's is `val = v` and
   the position fixed to it. **They must be guarded on `want_reasons()`:**
   built unconditionally as an `ExplicitReason` (patch C), they made the
   benchmark 14% and 11% slower with proofs off (0.877 s and 0.982 s). The
   cost is not a heap allocation: `ReasonLiterals` holds two literals inline,
   and a counting `operator new` sees the same allocations under patch C as
   without it while rule 2 makes 999 inferences
   (`tmp/fd-small/at_most_one/alloc/`). Its cause was not isolated. Guarded,
   the benchmark is unchanged (0.762 s and 0.880 s, against 0.767 s and
   0.881 s in the same batch). With proofs on, the `n = d = 5` enumeration's
   3,516 family assertions shrink from 584,580 bytes to 305,892 at
   `Inferences`, and its `Off` proof from 10.86 MB to 10.58 MB,
   verifying in about the same time. Small. Filed as #1157.
4. **Conform the encoding to `cake_pb_cp`'s** (patch D). Write `Count`'s three
   flags, `ge`, `le` and `eq`, named by position under the constraint ID, and
   label the row `am1`, as `Count` was conformed under #354. With a variable
   `val` the chain then passes `strict` (`varval.scp`, 60 solutions). **With a
   constant `val` it still does not**: two rows per position differ in one
   coefficient each, the flag's multiplier (over `0..2`, `ge`'s forward half has
   4 against cake's 3 and `le`'s reverse half 3 against 2), and `Count` with a
   constant value of interest differs from cake in exactly the same way today
   (`(count (A B) 1 N)`, `tmp/fd-small/at_most_one/chain/count_const.scp`). Both
   registered cases use `val = 1`, so they stay `none` until that shared
   difference is settled; register the variable case as `strict` meanwhile.
   Timing unchanged (0.768 s and 0.882 s). Small. Filed as #1158.

   **All four together** (`ABCD2.patch`): 0.739 s and 0.746 s on the
   benchmark (−4%, −15%), the propagations of patch B, the proofs of patch C2,
   the rows of patch D, and the audit row surviving the guard.

5. **Decide aliased positions at install.** Two cases are simple. A position
   repeated with the same view is a fixed disequality: `{x, x}` against `y` is
   `x ≠ y`. A position that is exactly `val`'s view always equals it, so every
   other position must differ from `val`. Posting those as `NotEquals` at
   install covers the exact repeats and exact `val` aliases. **It does not
   cover aliases through different views**, which are not a fixed
   disequality: `x` and `2 − x` both equal `y` only when `x = y = 1`, and a
   position `x` against `val = 2 − x` equals it only at `x = 1`. Those need the
   propagator to reason about the pair, or remain `bounds(Z)`-weak. Not
   tested. No front end produces any of these shapes, so this is robustness
   only. Small for the exact cases. Filed as #1159.
6. **Disable once entailed.** When `val` is fixed and rule 2 has fired, or no
   position can take any of `val`'s values, the constraint holds for the rest
   of the subtree. Trivial; not worth an issue on its own.
7. **Front ends.** Routing MiniZinc's `count(x, y) ≤ 1` or XCSP3's
   `atMost(…, 1)` here would be a front-end rewrite, which the project does
   not do; the cost it would recover is `Count`'s to remove. Recorded, not
   proposed.

## Prior art

McIlree's thesis names the constraint, `AtMostOne(X1, …, Xn, Y)`, and gives
it as Encoding Procedure 4.3, a smart table (its equation 4.34, row `i` saying
every other position differs from `Y`), which is exactly what
`AtMostOneSmartTable` builds; the thesis counts it among the constraints whose
efficient proof logging the smart-table procedure settles. There is no
published dedicated propagator for it as such. It is `count(x, y) ≤ 1`, and a
solver either propagates it through its `count`
(Gecode's `count(home, x, y, IRT_LQ, 1)` with a variable `y`, which the
benchmark above shows prunes less) or, for a constant value, as a cardinality
or clause at-most-one. The native class's encoding is Encoding Procedure 3.7,
`Count`'s, with the flags' polarity reversed and the count bounded by one;
`cake_pb_cp`'s `at_most_one` is 3.7 exactly. The native propagator came from
#174, which asked for one in place of the `SmartTable` decomposition and kept
that as a baseline. What is new here is the justification, not the encoding:
one RUP step per inference through `Count`'s flags, whose argument is JP
3.1's. The thesis has no justification procedure for `Count`'s encoding; it
covers `AtMostOne` only through Encoding Procedure 4.3's smart-table
decomposition, justified by `SmartTable`'s procedure.

## Further reading

- [`counting.md`](counting.md): `Count`, whose pre-#354 encoding this one
  still uses, and which the front ends post in its place.
- [`smart_table.md`](smart_table.md): the engine under `AtMostOneSmartTable`,
  and its benchmarks against this family.
- [`optional-interior-pruning.md`](../optional-interior-pruning.md): why the
  triggers' overstatement matters to other constraints.
