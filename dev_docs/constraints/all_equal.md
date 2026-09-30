# `AllEqual`: every variable in an array takes the same value

> **Maturity** production ·
> **Audited** 2026-09-30 at `c9ceea25` ·
> **Open issues** none filed by this audit yet; see [Next steps](#next-steps)
> for what it would file, the first of them a wrong-answer bug. Already open
> and touching this family: #833 (the large-domain policy), #868
> (cross-solver comparisons; this document gives one, by hand). Tracked under
> #871.

`AllEqual(vars)` says every variable in `vars` takes the same value. It is one
class with one propagator. The encoding is the chain of `n − 1` consecutive-pair
equalities. The propagator intersects every domain in one call: first the
bounds, then, if any domain has a hole, the values themselves.

Four things to know before touching it.

- **It gives wrong answers.** At the end of each call the propagator disables
  itself if `vars[0]` is single-valued. That test comes *after* its own pruning,
  but the bounds pass only intersects with the bounds the variables had at
  entry. `vars[0]` can become single-valued during the call while another
  position is left unequal to it: holding a different value, or still more
  than one. The constraint is then switched off with its variables unequal.
  On distinct variables, or plain repeats, that needs a hole in `vars[0]`
  inside the entry bounds and no hole left after the bounds pass (otherwise
  the hole pass would equalise everything). `AllEqual{x, y}` with
  `x ∈ {1, 3}` and `y ∈ {2, 4}` has no solution, and the solver reports
  `x = 3, y = 2`. A repeat through an offset or an opposite-sign view needs
  neither condition: either pass can fix `vars[0]` through its other
  occurrence, as in `{x, y, x + 1}` or `{x, y, 2 − x}` over intervals. The bug
  is reachable from the C++ API, the `.scp` reader, XCSP3 and, under search,
  from MiniZinc. A proof-logged run catches it, because VeriPB rejects the
  `solx` line. The fix is one line, tested; see
  [Known limitations](#known-limitations).
- **Apart from that bug, it is generalised arc consistent on distinct
  variables**, including views, constants and holes, and on a same-sign
  repeat. The one exception is an opposite-sign repeat, `{x, c − x}`, which
  is not even `bounds(Z)`. A same-sign repeat with different offsets, as in
  `{x, x + 1}`, loses no strength but is slow: it is unsatisfiable, and the
  propagator takes W/2 calls to notice.
- **Its holes matter, and it says so.** It triggers `on_change` on every
  variable and reads every hole, so it keeps other constraints' interior
  pruning alive on its variables.
- **It is no faster than `n − 1` `Equals`.** On an identical enumeration
  (holey domains, the same tree, no failures) it makes 4.0 to 15.0 times fewer
  propagator calls than the pairwise chain, yet takes from about the same time
  to 7% *longer*. The class comment's "strictly stronger per pass" is true of
  propagator calls, not of time. Gecode's `rel(x, IRT_EQ)` is 4.6 to 10.5
  times faster.

## What it is

### Semantics

`AllEqual(vars)` holds exactly when `vars[i] = vars[0]` for every `i`.

- **Empty array, or one variable:** trivially true. `prepare()` returns false
  (`all_equal.cc:53`), so nothing is installed and no OPB row is written.
  MiniZinc's standard library drops such a call before the solver sees it: an
  `all_equal` over one variable and over an empty array flattens to nothing
  (`tmp/fd-small/all_equal/mzn/aeone.mzn`).
- **All constants:** a true/false check, handled by the ordinary propagator:
  unequal constants make the bounds pass contradict. `all_equal_test` covers
  equal and unequal constants, and a mix of constants and a variable (#254).
- **A repeated variable** is accepted. `{x, x}` is vacuous, `{x, y, x}` is
  `x = y`, and `{x, x + 1}` is unsatisfiable. See [Robustness and
  limits](#robustness-and-limits) for what each costs.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `AllEqual` | ✓ `fzn_all_equal_int`, for `var int`, enum and (via `bool2int`) `var bool` arrays[^mzn] | ✓ `allEqual` over a list of variables; over expressions `frontend gap`[^xtree] | ?[^gcspy] | ✓ `all_equal` | |
| reified | `decompose`: the stdlib's `fzn_all_equal_int_reif`[^reif] | n/a | — | — | no class exists |

[^mzn]: `minizinc/mznlib/fzn_all_equal_int.mzn` routes the stdlib's
    `fzn_all_equal_int` to `glasgow_all_equal_int` (`fzn_glasgow.cc:882`). On
    both 2.9.7 and 2.10.1, with `build/glasgow.msc`, int, enum and bool arrays
    flatten to one `glasgow_all_equal_int`, the bool array through three
    `bool2int`, with no warning. An array indexed from 3 flattens the same, and
    positions are all that matter: no value is an index
    (`tmp/fd-small/all_equal/mzn/`). The stdlib's set overload
    (`fzn_all_equal_set`) is `n/a`: the solver has no set variables.

[^xtree]: `buildConstraintAllEqual(string, vector<XVariable *>)`
    (`xcsp_glasgow_constraint_solver.cc:280`) posts `AllEqual`. The parser's
    other overload, over expression trees (`<allEqual> add(x,1) y </allEqual>`),
    is not overridden, so such an instance answers `s UNSUPPORTED`
    (`tmp/fd-small/all_equal/xcsp/tree.xml`).

[^gcspy]: `gcspy` binds nothing from this family, so CPMpy can reach it only
    through a decomposition of its own, if at all. Not checked.

[^reif]: `b <-> forall (i, j in index_set(x) where i < j) (x[i] = x[j])`: all
    `n(n − 1)/2` pairs, not a chain. Flattened, that is three `int_eq_reif` and
    an `array_bool_and` for `n = 3`, on both versions.

### Options

`None.` There is no consistency tag and no algorithm switch.

### Variable kinds and views

Plain variables, constants and views of either sign are all accepted, and the
propagator reads them all the same way, through `State`.

**The proof handles views too.** A view position gets its own bit-sum proof
variable with channel rows (see
[`view-proof-logging.md`](../view-proof-logging.md)), and the chain equality is
written over that variable. So every row keeps the form `a − b = 0` whatever
the view's sign or offset. Checked:
- `AllEqual{x, y + 1, −z + 5}` over `0..6` enumerates its 5 solutions with a
  verifying proof (`tmp/fd-small/all_equal/probes/fam.cc`, mode `views`);
- 300 random instances with `±1` views, chains of 2 to 8 and holey domains up
  to 121 wide all verify (`probes/proofz.cc`, on the fix build below);
- the test's `view_mixed` lane runs every interval shape with views mixed in.

### Reification

`None.` MiniZinc's `all_equal_reif` reaches the solver as the standard
library's pairwise decomposition (above). Two challenge models reify it:
`speck-optimisation` 2023 writes `all_equal(...) -> all_equal(...)` and counts
`not all_equal(...)` (`SPECK-Optimisation.mzn`, lines 51 and 53), and its
`easy_1` instance flattens to 300 `int_eq_reif` and 90 `array_bool_and`;
`harmony` 2024 writes `not all_equal(...)` (`harmony.mzn:141`). Speck's
arrays have 3, 4 and 5 elements, which the pairwise decomposition turns into
10 distinct reified equalities per bit position once common subexpressions are
shared; harmony's have 3, three reified equalities each. Whether that
justifies a class is open
(`tmp/fd-small/factcheck/all_equal/corpus/`).

### Relation to other families

- **Decomposes into it:** MiniZinc's `all_equal` over `var bool`, through
  `bool2int`. Nothing in the solver posts an `AllEqual` of its own.
- **Child constraints:** none.
- **Shares code:** `justify_not_in_range_across_equality`
  (`innards/justify_not_in_range.hh:59`), which `equals`, `in` and `min_max`
  also call. It emits the two bound lemmas of [rule
  4](#rule-range-removal). A change to it is a change to all four families.
- **Presolvers:** none reads it. Its rows are difference constraints with a
  zero offset, but the difference-logic presolver finds its donors by class,
  and this is not one of them.
- **The merge question with `equals`:** separate, and not a listed candidate.
  `Equals` is the binary case, with the same row and the same helper, but the
  two share no propagation code. [CPU performance](#cpu-performance) measures
  the chain of `Equals` this class replaces.

## The proof model

### OPB encoding

For the array `v`, in the user's order:

```
for i in 0 .. n-2:    BinEnc(v[i]) − BinEnc(v[i+1]) = 0      (rows @c[id][<i>le], @c[id][<i>ge])
```

That is the whole encoding (`all_equal.cc:64`). **It is definitional**: the rows
state the constraint and nothing more. It is `2(n − 1)` rows over bit sums, so
it is logarithmic in domain width. For four variables:

```
* constraint all_equal _1
@c[_1][0le] -1 i[x][b0] -2 i[x][b1] -4 i[x][b2] 1 i[y][b0] 2 i[y][b1] 4 i[y][b2] >= 0;
@c[_1][0ge] 1 i[x][b0] 2 i[x][b1] 4 i[x][b2] -1 i[y][b0] -2 i[y][b1] -4 i[y][b2] >= 0;
...
```

### Labels

The rows are labelled `@c[id][<i>le]` and `@c[id][<i>ge]`, to match
`cake_pb_cp`. **No rule cites a label.** Every inference is a RUP, or a RUP
sequence, so unit propagation finds its own rows. The labels exist only for
cake conformity.

### Cake conformity

**Strict.** `cake_pb_cp` encodes the family as the same chain with the same
labels. `scp_chain_all_equal_sat` (three variables over `0..3`) and
`scp_chain_all_equal_unsat` (`0..2` against `3..5`) pass the full workflow-2
chain, with `opbdiff` matching every row
(`verified_encodings/scp_cases/CMakeLists.txt:94–103`, run at `c9ceea25`).

Neither case has a hole, so neither reaches the wrong-answer bug. On
`tmp/fd-small/all_equal/scp/wrong.scp` (`x ∈ {1, 5}` through an `in`,
`y ∈ 0..3`) the chain fails at its step 3: VeriPB rejects the solver's proof
against cake's OPB. With the fix, it passes.

### Proof-time state

Nothing is emitted at the root, and there is no proof-only auxiliary.

A range removal (rule 4) writes two bound lemmas, then its conclusion, then
`del range -3 -1`, which deletes the two lemmas and keeps the conclusion.
Nothing later needs the lemmas: their conclusions name only order literals,
which any later step can re-derive. Everything else the family writes is
ordinary inference lines at the current level, deleted by the shared
backtrack machinery.

Besides the chain rows, the proof mentions only the variables' order, equality
and range literals, which the shared literal layer introduces lazily the first
time an inference names them.

## The implementation

### Initialisation and global data

`prepare()` declines to install anything for fewer than two variables. There is
no initialiser, and nothing is computed once.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| the intersection pass | `on_change`, every variable | derived: **every variable** | 1, 2, 3, 4 | always, for two or more variables | never claims; is a fixpoint on intervals, not over holes | yes, when `vars[0]` is single-valued after the call; **wrongly**, see below |

**`on_change` is the honest trigger.** The hole pass reads every domain's holes
and removes each hole from every other variable, so a hole anywhere can give it
an inference. Nothing sets `Triggers::holes_affect_propagation`.

**Idempotence.** Not claimed, and a claim would be wrong over holes. The
bounds pass intersects with the bounds the variables had at entry, not the
bounds they land on. With `x ∈ {0, 2, 3}` and `y ∈ 1..3`, the first call
pushes `x ≥ 1`. That lands on 2, but `y` keeps `1..3`: neither domain has a
hole now, so the hole pass does not run. A second call pushes `y ≥ 2`
(`probes/disable.cc`, case `f`; the `a` lines show the two pushes). Over
interval domains, on distinct variables, one call does reach the fixpoint:
every variable ends at `[lo, hi]`. The engine calls it again anyway, since
its own changes wake it. That is 1.38 to 1.45 of its calls per search node
on the benchmark below.

**Self-disabling, and the bug.** The pass ends with
`if (state.has_single_value(vars[0])) return DisableUntilBacktrack`
(`all_equal.cc:242`). Its comment says the chain equalities "will have
propagated that value to every other var". They have not, when `vars[0]`
became single-valued during this call. See [Known
limitations](#known-limitations).

### Mutable state and incrementality

`None.` Nothing persists between calls. Every call does four things:
- reads every variable's bounds;
- asks every variable whether it has holes;
- if any does, **copies every domain**, intersects the copies, and walks each
  variable's difference from the intersection;
- infers.

That is `O(n)` without holes and `O(Σ intervals)` with them, whatever changed
since the last call. On the benchmark below, a node whose decision removed one
value from one variable still copies all `m` domains of its group. Keeping the
intersection between calls would cost a backtrackable `IntervalSet`. Whether
it would pay is untested; see [Next steps](#next-steps).

### Interior values and optional pruning

**Offers.** `None.` The hole pass is the constraint's generalised arc
consistency, and there is no weaker arm to fall back to.

**Observes.** **Every variable's holes.** A hole in any variable is removed from
all the others, so an `AllEqual` in a model is a reason for another
constraint's interior pruning on these variables to stay on. The `derived`
answer from `on_change` is exact here, not an overstatement.

### Robustness and limits

**Unbounded domains.** Fine on distinct variables: nothing walks values. Two
repeated-variable shapes cost their width; see below.

**Negative values and zero.** Tested: the random shapes in `all_equal_test`
start anywhere in `−3..5`, and the root probe's domains span `−3..4`.

**Degenerate shapes.**

- *Empty, singleton, all constant:* covered by the test (#254).
- *A plain repeat* (`{x, y, x}`) is harmless. With the fix below, the root
  probe (`probes/aecheck.cc`, mode `alias`) finds GAC on all 6,000 random
  aliased instances, seeds 1 and 2. On the current code, 1 and 8 of them stop
  short of GAC, because of the bug.
- ***A same-sign repeat with different offsets costs its width.*** `{x, x + 1}`
  is unsatisfiable, and nothing notices at once. Each call moves both of `x`'s
  bounds in by one, until the domain empties.
  - With the fix, over `x ∈ 0..W`, `{x, x + 1}` and `{x, y, x + 1}` take
    W/2 + 1 propagations to fail (50,001 at W = 10⁵), and `{x, x + 2}` takes
    W/4 + 1 (25,001) (`probes/aliaswide.cc`).
  - **On the current code it is worse: at even W it gives wrong answers.**
    After W/2 calls, `x` is fixed at W/2 mid-call. The propagator disables
    itself, and `{x, x + 1}` reports every value of the free `y` as a
    solution: 100,001 of them at W = 10⁵. At odd W the domain empties first,
    and the answer is right.
  - The root probe's `aliasoffs` mode (repeats with `+1` views and offsets
    in `−2..2`) finds the fix GAC on all 6,000 instances, with every
    unsatisfiable one failed at the root.
- ***An opposite-sign repeat is not `bounds(Z)`.*** `{x, c − x}` forces
  `2x = c`, but the bounds pass sees two variables with the same bounds and
  the hole pass sees two images of one domain.
  - With `x ∈ 0..W`, `{x, W − x}` prunes nothing at the root, although only
    W/2 is supported. Search then tries every value: 1,002 recursions at
    W = 1,000 (2,003 in `probes/aliaswide.cc`, which also enumerates a free
    `y`).
  - The unsatisfiable `{x, W + 1 − x}` takes 100,001 recursions to refute at
    W = 10⁵.
  - With the fix, the root probe's `aliasviews` mode (`±1` views over
    repeated variables) finds `bounds(Z)` failing on 455 and 446 of 3,000
    instances (seeds 1 and 2), and 293 and 318 unsatisfiable instances not
    failed at the root. On the current code, with the bug on top, it is 871
    and 842, and 679 and 694.
  - With the fix it stays sound: once `x` is fixed, `lo > hi` and the pass
    contradicts. On the current code the two-position `{x, c − x}` is sound
    too, but add a third position and it gives wrong answers: `{x, y, 2 − x}`
    over `x ∈ 0..3`, `y ∈ 1..5` reports `(1, 1)` and `(1, 2)`, where only the
    first is a solution (see [Known limitations](#known-limitations)).
- *Front ends:* MiniZinc cannot produce a view, so `all_equal([x, x + 1])`
  arrives with an auxiliary variable and an `int_lin_eq`. It fails correctly,
  in 1,001 propagations over `0..1000`, as the two constraints hand the bound
  back and forth (`mzn/rep1.mzn`). XCSP3's `allEqual` and the `.scp` reader
  take plain variables and constants only: the reader rejects a view argument
  such as `(x0 + 1)` with `expected an atom, found a list`. So views, and with
  them offset and opposite-sign repeats, reach the family only from the C++
  API. A plain repeat also comes from `.scp` and XCSP3, and from MiniZinc
  after aliasing.

**Overflow.** `hi + 1_i` in the upper-bound push goes through
`Integer::operator+`, which throws `IntegerOverflow` rather than wrap. A bound
at `±2⁶¹` plus one is still in range. Nothing else here does arithmetic.

### Interval efficiency

**Fine at any width on distinct variables.** Nothing reaches for `State`'s
per-value iterators.

1. **The propagation side.**
   - The bounds pass is `O(n)` bounds reads.
   - The hole pass uses `copy_of_values`, `IntervalSet::intersect_with` and
     `each_interval_minus`, so it is per interval.
   - A removed interval one value wide takes the equality form (rule 3). Its
     witness scan is `n` `in_domain` calls.
   - A wider one looks for a single covering witness with `contains_any_of`,
     `n` merge-walks. Otherwise it splits by witness with `each_interval_minus`
     against each variable in turn.

   The width hazard is not a walk but a call count: a same-sign repeat with
   offsets makes about W/2 calls (above).
2. **The reason side.** One literal per inference: an order literal, an
   equality literal or a range literal, never one per value. The witness search
   is per interval (above). Reasons are `ExplicitReason`s built at the
   inference site, so only when an inference is made, and not guarded on
   `want_reasons()`. That costs no heap allocation: `ReasonLiterals` is a
   `small_vector` with room for two literals inline. Counting `operator new`
   up to the first solution with proofs off, 20,000 bound inferences over
   10,000 variables add 632 allocations to 20,482, which the fact-check puts
   down to container growth without measuring it
   (`tmp/fd-small/factcheck/all_equal/probes/allocs.cc`).
3. **The proof side.** One line per bound or value inference, and three lines
   plus a `del` per removed interval, whatever its width. The form is chosen by
   the interval's width, one value against more, which is a width test, not a
   test on the variable's kind. Over narrow holey domains most removed
   intervals are single values. [`large-domains.md`](../large-domains.md)
   records that routing those through the interval path cost 2%.
4. **The audit lane.** Two rows, both pinned `Clean`
   (`large_domain_audit_test.cc:436–453`):
   - `AllEqual`: three plain variables over `0..10⁹`;
   - `AllEqual/holes`: a two-value domain at the extremes against a full one,
     so one range removal of the whole middle.

   Neither varies the number of variables past three, a view, a mixed witness
   (the split path) or a repeat. The width-proportional repeat is invisible to
   the per-call guard, which counts values walked per call, as it is for
   `increasing`.

   The `AllEqual/holes` row's comment is stale. It says the pass "then walks
   each interval a value at a time" and that the row "still trips", and it
   cites `all_equal.cc:114`; but the row is pinned `Clean`, the per-value
   loop is gone, and the hole pass is at line 116.

## Inference catalogue

Four rules. A conflict is not a fifth rule. It arises in two ways:
- when `lo > hi`, a bounds push fails on some variable;
- when the intersection is empty, the removals empty a domain.

Either way the tracker asserts the attempted literal with its reason, exactly
as for a successful inference. Measured at `Inferences` on `x ∈ 0..2`,
`y ∈ 3..5`: `a 1 i[x][ge3] 1 ~i[y][ge3] >= 1`, then the contradiction's own
two lines: a plain `a >= 1;` under `% asserting contradiction`, and
`a >= 1::backtrack:;` under `% backtracking`.

Three facts hold for every rule.

**One wire form.** `hints::AllEqual`, `(constraint_id <id>)`, with no subhint
and no payload. Every `a` line from the family in every probe has that form.

**The reason is one literal, and minimal.** It names one witness variable that
lacks what is being removed. The witness is chosen by position (the first to
qualify), so it is often not adjacent to the variable being pruned.

**How far a RUP reaches.** For an adjacent pair, each rule is a published
procedure: JP 3.2 on Thm 2.9 for a bound, JP 3.12 on Thm 2.8 for a value. For
a witness further along the chain, the RUP must cross positions that no
literal in the clause names.
- For values, Thm 2.8 carries the fixed bits across each hop, so the argument
  extends.
- For bounds, no result in
  [`justification-techniques.md`](../justification-techniques.md) covers more
  than one row, so **this is checked, not argued**:
  - chains of 3, 8 and 16 over `0..10⁴`, with the witness at the far end,
    all verify, for the lower-bound rule and for the range rule, the latter
    also with alternate positions negated (`probes/chainrup.cc`);
  - so do 300 random instances with chains up to 8 (`probes/proofz.cc`,
    fix build);
  - so do the fact-check's 900 chains of 3 to 8 positions, widths up to about
    4·10⁶, negative values, `±1` views with offsets up to ±1,000, and far
    witnesses in both directions across bit widths
    (`tmp/fd-small/factcheck/all_equal/chainfuzz/`, fix build).

### Rule: lower-bound-to-max

- **Infers** — `v[i] ≥ lo` for every `v[i]` below it, where `lo` is the
  largest lower bound at entry.
- **Fires when** — any variable changes, in the bounds pass.
- **Strength** — `GAC` on distinct variables, together with rules 2 to 4,
  **once the entailment test is fixed**. With the fix, the root probe
  (`probes/aecheck.cc`) finds GAC on every instance:
  - 6,000 each (seeds 1 and 2) with distinct plain variables, with constant
    positions, with plain repeats, with `±1` views and with same-sign
    offset repeats;
  - holes in every mode.

  On the current code the same probe finds GAC failing on 9 and 12
  distinct-variable instances and on 97 and 96 with views, every one
  through the bug. An opposite-sign repeat is not `bounds(Z)`; see
  [Robustness](#robustness-and-limits). `all_equal_test` also checks GAC at
  every node, but on interval domains, apart from two fixed holey shapes.
- **Algorithm** — one pass, `O(n)` bounds reads. The bound is the entry
  maximum, not the landed one, which is why it is not a fixpoint over holes.
- **Why it is true** — every variable equals the witness, and the witness is
  at least `lo`.
- **Proof technique** — `RUP`. For an adjacent witness, **JP 3.2** licensed by
  **Theorem 2.9** with `B = 0`, over one half of the equality. For a further
  witness, the RUP crosses the intermediate rows without a theorem: checked,
  as the preamble says.
- **Reason** — `{witness ≥ lo}`, where the witness is the first variable whose
  lower bound is `lo`. One literal.
- **Assertion** — `v[i] ≥ lo ∨ ¬(witness ≥ lo)`. Measured at `Inferences`:
  ```
  a 1 i[w][ge2] 1 ~i[z][ge2] >= 1::all_equal:((constraint_id _1));
  a 1 i[x][ge1] 1 ~p[0_view_of_y_plus_1][ge1] >= 1::all_equal:((constraint_id _1));
  ```
- **Hint** — `hints::AllEqual`: `originator`, the `ConstraintID`.
- **Offline reconstructibility** — `offline`. A plain RUP naming both
  variables; the chain between them is the model's.
- **Proof size** — one line per inference, whatever the width.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` No mutation lane exists for this family.

### Rule: upper-bound-to-min

- **Infers** — `v[i] < hi + 1` for every `v[i]` above it, where `hi` is the
  smallest upper bound at entry.
- **Fires when** — as rule 1, in the same pass.
- **Strength** — `GAC` on distinct variables, with rules 1, 3 and 4; see
  rule 1.
- **Algorithm** — as rule 1.
- **Why it is true** — every variable equals the witness, which is at most
  `hi`.
- **Proof technique** — `RUP`, as rule 1, with the bounds exchanged.
- **Reason** — `{witness ≤ hi}`, the first variable whose upper bound is `hi`.
- **Assertion** — `v[i] < hi + 1 ∨ ¬(witness < hi + 1)`. Measured:
  ```
  a 1 ~i[w][ge6] 1 i[x][ge6] >= 1::all_equal:((constraint_id _1));
  a 1 ~i[x][ge6] 1 p[1_neg_view_of_z_plus_5][ge6] >= 1::all_equal:((constraint_id _1));
  ```
- **Hint** — `hints::AllEqual`: `originator`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per inference.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: value-removal

- **Infers** — `v[i] ≠ a`, for a value `a` of `v[i]` that is missing from some
  other variable, when the run of `v[i]`'s domain outside the intersection
  containing `a` is one value wide.
- **Fires when** — any variable still has a hole after the bounds pass.
- **Strength** — `GAC`, with rules 1, 2 and 4; see rule 1.
- **Algorithm** — the removal set is `v[i]`'s domain minus the intersection of
  every domain, all taken from snapshots at the start of the hole pass, walked
  as intervals (`each_interval_minus`). For a one-value interval, the witness
  is the first variable not holding `a`, found by `n` `in_domain` calls on the
  live state.
- **Why it is true** — `v[i] = a` would force the witness to `a`, which it
  cannot take.
- **Proof technique** — `RUP`, by **JP 3.12** applied hop by hop along the
  chain, licensed by **Theorem 2.8** at each hop. The negated conclusion fixes
  `v[i]`'s bits, and each equality row then fixes the next variable's bits,
  until the witness's `≠ a` conflicts. A view hop passes through its channel
  rows the same way.
- **Reason** — `{witness ≠ a}`, one literal.
- **Assertion** — `v[i] ≠ a ∨ ¬(witness ≠ a)`. Measured:
  ```
  a 1 ~i[x][eq7] 1 i[y][eq7] >= 1::all_equal:((constraint_id _4));
  ```
- **Hint** — `hints::AllEqual`: `originator`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per removed value that forms a one-value run.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: range-removal

- **Infers** — `v[i] ∉ [l, u]`, for each run `[l, u]` of `v[i]`'s domain
  outside the intersection that is two or more values wide, or for each
  witnessed part of one.
- **Fires when** — as rule 3.
- **Strength** — `GAC`, with rules 1 to 3; see rule 1.
- **Algorithm** — first a scan for one variable (other than `v[i]`) whose
  snapshot holds none of `[l, u]`: `n` merge-walks, no allocation. If there is
  none, the run is split. For each other variable `j` in turn, the part of
  what is left that `j` lacks is removed with `j` as its witness and struck
  off, so each part is removed once. Every part of the run is missing from
  some variable, since the run lies outside the intersection. This split path
  is what `all_equal_test`'s `run_mixed_witness_test` reaches.
- **Why it is true** — each variable in the witnessed part would force the
  witness into a range it holds no value of.
- **Proof technique** — `RUP sequence`, through
  `justify_not_in_range_across_equality`, then `del range -3 -1`. The
  sequence:
  - `v[i] ≥ l → witness ≥ l`;
  - `witness ≥ u + 1 → v[i] ≥ u + 1`;
  - the conclusion, by RUP once those two are in place.

  Each lemma is written under the reason, and each is **Theorem 2.9** across
  one equality half, as JP 3.2. That holds for an adjacent witness; further,
  it is checked, as the preamble says.
- **Reason** — `{witness ∉ [l, u]}`, one range literal per part.
- **Assertion** — `v[i] ∉ [l, u] ∨ ¬(witness ∉ [l, u])`. Measured, from the
  split path, where `x`'s run `5..14` is witnessed by `y` for `5..9` and by `z`
  for `10..14`:
  ```
  a 1 ~i[x][in5_9] 1 i[y][in5_9] >= 1::all_equal:((constraint_id _3));
  a 1 ~i[x][in10_14] 1 i[z][in10_14] >= 1::all_equal:((constraint_id _3));
  ```
- **Hint** — `hints::AllEqual`: `originator`.
- **Offline reconstructibility** — `offline`. The lemmas are determined by the
  asserted clause's two variables and endpoints.
- **Proof size** — four lines per part, whatever its width: three RUPs and a
  `del`. The shared layer's cost is separate. At W = 10⁵, going from 10 to 100
  removed runs adds about 51 lines per run (14 `red`, 5 `pol`, 7 `rup` and
  25 `core`), for the range and order literals the rule names on its two
  variables (`probes/runs.cc`).
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

- **`all_equal_test`** (`all_equal_constraint`, plus
  `all_equal_constraint_view_mixed`), each run without and with proofs:
  - six fixed interval shapes of two to four variables, three shapes of
    singleton domains (#254), and thirteen random interval shapes whose lower
    bound is in `−3..5` and which are up to five wider. All run under
    `solve_for_tests_checking_gac`, so every value left at every node is
    checked against the solution set;
  - `run_holes_test` (three holey variables, carved by `In`) and
    `run_mixed_witness_test` (the split path), both also GAC-checked, bare
    lane only;
  - the #254 collections (empty, single, constant) and five duplicate shapes,
    under plain `solve_for_tests`, so enumeration and the proof but no
    consistency check.

  VeriPB runs when it is on the path: 35 proofs in the bare lane and 22 in
  `view_mixed` at `--seed=1`. The search is the tests' random brancher,
  seeded (`--seed`).
- **`scp_chain_all_equal_{sat,unsat}`:** see [Cake
  conformity](#cake-conformity).
- **MiniZinc:** `allequaltest.mzn`, three variables over `1..3`, compared
  against the reference solver.
- **XCSP3:** `all_equal.xml`, three variables over `0..2`.
- **Audit lane:** the two rows above.

**Runtime caps.** No lane sets or clears one, and the default caps **cannot
fire**: the largest expected solution count is 11, and no run gets anywhere near
1,500 recursions (`GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500
all_equal_test --seed=1`, and the same with `--view-position=mixed`, at
`c9ceea25`: 70 and 44 runs). So the capped and uncapped runs check the same
thing.

**Tightness:** no mutation lane, and no refusal shown by hand.

**What the tests do not cover.**

- **The wrong-answer shape.** On distinct variables or plain repeats it needs
  `vars[0]` holey, and every domain hole-free once the bounds pass is done.
  Otherwise it needs a repeat through an offset or an opposite-sign view,
  which no test posts: the duplicate shapes are plain repeats over intervals.
  Every random shape is an interval. In `run_holes_test` all three variables
  are still holey after the bounds pass, so the hole pass runs. In
  `run_mixed_witness_test`, `vars[0]` is the full interval. The fact-check
  instrumented the one branch where the current test and the fix differ:
  nothing in the full suite (962 tests, caps off), the 90 view-wrap lanes or
  four more seeds reaches it (`tmp/fd-small/factcheck/all_equal/instr/`). The
  bug has been there since the propagator was written (d8c74724, 2026-05-08).
- **Holes made during search by other constraints.** No test posts anything
  beside `AllEqual`, apart from `In` at the root.
- **A far witness over a wide domain,** which is where a multi-hop RUP would
  fail if it were going to. The test's chains are at most four variables
  long, and its widest domain is 21 values (`run_mixed_witness_test`).
- **Repeats with offsets or through views,** and any repeat over a wide
  domain. The duplicate shapes are plain variables over `1..7`.
- **The consistency of the repeated shapes**, deliberately: the duplicate runs
  check no level.
- **Real instances:** none ported.

### Benchmarks and examples

- **In the repository:** no example or benchmark posts this family.
- **Corpus:** 24 `glasgow_all_equal_int` posts, in three of the 285 flattened
  MiniZinc Challenge models in the corpus (`yumi-static` 2022 and 2023, and
  `yumi-dynamic` 2024; eight each, one instance per model), over 2 to 7
  variables with domains of two or three values
  (`tmp/fd-small/all_equal/scan_corpus.py`). That corpus is not the whole
  challenge. It lacks `generalized-peacable-queens` 2022, whose `n8_q3`
  instance flattens to one `glasgow_all_equal_int` over three variables in
  `0..21`, and `yumi-dynamic` 2021, which does not flatten on 2.9.7
  (`maximum of empty set`), and it has no 2026 models (`workforce-alloc` 2026
  uses `all_equal` too, with no data here). Two further models reify it; see
  [Reification](#reification).
  - It is never a meaningful share of a solve. In 10 s of `yumi-static` 2022
    it makes 17 calls taking about 10 µs (`GCS_PROPAGATOR_STATS=time`; 16 µs
    and 9 µs in two runs). In both runs `ArrayMax` takes 9.7 s of the 10.
  - The original and fixed builds give the same solution sequence on all
    three `yumi` models over 60 s, and the fact-check found the diverging
    branch unreached on those and on `generalized-peacable-queens`, so the
    bug does not fire there.
- **For CPU:** the enumeration below. It reaches all four rules, has a
  checkable solution count, and gives GCS and Gecode identical trees.
- **For proof verification:** the same enumeration with two or three groups
  (below). VeriPB time grows fast with the group size, so start small.

### CPU performance

*Release build of `c9ceea25` (GCC 15.2.0, `-O3 -march=native`), and the same
plus the entailment fix (`tmp/fd-small/all_equal/fix-entailment.patch`);
Gecode 6.3.0, built locally; fataepyc-10, boost off, `numactl` on node 0,
`taskset -c 9`, `setarch -R`, `GLIBC_TUNABLES` fixing the malloc thresholds;
median of five runs; wall time of the whole solve, proofs off; 2026-09-30.*

`G` independent groups of `m` variables over `0..D−1`. Each value is dropped
with probability ¼ by a fixed generator shared by both programs, and each
group is all-equal. Every solution is enumerated, branching in input order on
Gecode's median (the greatest value not above the median), `=` then `≠`
(`bench/ae_gcs.cc`, `bench/ae_gecode.cc`).

In GCS the holes are carved by `NotEquals` with constants, which run once at
the root. `create_integer_variable` from a value list posts an `In` instead,
and that `In` would have been called 1.6 million times on the first row
without ever pruning. Gecode posts `rel(x, IRT_EQ, IPL_DOM)`, its `NaryEqDom`.

Every arm is generalised arc consistent, so all four explore the same tree:
the same solutions, recursions equal to Gecode's nodes, and no failures. The
`=` branch fixes a group through rules 1 and 2. The `≠` branch removes one
value from one variable, usually an interior one, which rule 3 carries to the
rest of the group; with two values left, the median is the lower bound, and
rule 1 carries it instead.

| G, m, D | Solutions | GCS `AllEqual` | GCS, fixed | GCS, `m − 1` `Equals` | Gecode |
|---|---|---|---|---|---|
| 5, 5, 40 | 162,000 | 0.909 s | 0.914 s | 0.864 s | 0.196 s |
| 5, 8, 100 | 60,060 | 0.500 s | 0.499 s | 0.498 s | 0.088 s |
| 5, 16, 1000 | 183,040 | 6.23 s | 6.26 s | 5.82 s | 0.596 s |

| G, m, D | Recursions = Gecode nodes | `AllEqual` calls | `Equals` calls | GCS propagations, all, `AllEqual` arm | GCS propagations, all, `Equals` arm | Gecode propagations |
|---|---|---|---|---|---|---|
| 5, 5, 40 | 323,999 | 467,846 | 1,871,414 | 468,041 | 1,871,609 | 428,016 |
| 5, 8, 100 | 120,119 | 166,289 | 1,164,128 | 167,240 | 1,165,079 | 164,326 |
| 5, 16, 1000 | 366,079 | 529,227 | 7,938,930 | 549,263 | 7,958,966 | 487,427 |

The first two call columns are the family's own (`GCS_PROPAGATOR_STATS=calls`);
the "all" columns add the root `NotEquals` calls that carve the holes (195,
951 and 20,036).

- **The class is no faster than the pairwise chain it replaces.** It makes 4.0
  to 15.0 times fewer calls of its own, and takes from about the same time to
  7% more: +5.2%, +0.4% and +7.0% here, and +4.6%, −0.9% and +7.0% in the
  fact-check's rerun with the same recipe. On the middle row `perf stat` gives
  2.85 billion instructions against the chain's 3.17 billion, but the cycles
  are within 4% of each other.
  - A profile of that row puts 14% of cycles in the propagator's own body,
    7% in `each_interval_minus`, 4% in `intersect_with`, and a good share of
    the 13% in `malloc` and `free`. That fits the copy of every domain per call
    described under [Mutable state](#mutable-state-and-incrementality). It is
    a profile, not a measured saving.
- **GCS is 4.6 to 10.5 times Gecode's time.** At `m = 16`, `D = 1000`, the
  propagator accounts for 2.1 s of a 6.3 s solve (`GCS_PROPAGATOR_STATS=time`).
  The rest is search over 80 wide holey domains.
- **The fix costs nothing measurable.** The two builds' trees and call counts
  are identical, and their times are within 1%. That is expected: here the
  bug's shape never arises, because every group's domains stay equal.
- **What the benchmark does not exercise:** conflicts (there are none), range
  removals under search (the decisions remove single values), views, repeats
  and holes made by other constraints.

### Proof performance

*Same build and machine. `ae_gcs allequal G m D 1`, all solutions, VeriPB 3.0.2
with `--force-checked-deletion`; VeriPB time is wall clock, single run; solve
time with proofs is the median of three, with the proof files on `/dev/shm`
(tmpfs; `bench/solve_with_proof_tmpfs.txt`). With them on NFS the fact-check
measured ratios of about 40, 186 and 516.*

| G, m, D | Solutions | Lines, `Off` | Bytes, `Off` | Solve, with proof | VeriPB, `Off` | VeriPB ÷ solve | This family's lines | Share | Lines, `Inferences` |
|---|---|---|---|---|---|---|---|---|---|
| 2, 5, 40 | 150 | 10,694 | 447 KB | 0.012 s | 0.84 s | 70 | 1,988 | 19% | 3,632 |
| 3, 5, 40 | 1,800 | 53,420 | 2.84 MB | 0.047 s | 10.6 s | 225 | 21,302 | 40% | 41,111 |
| 3, 8, 100 | 1,716 | 98,711 | 4.96 MB | 0.098 s | 56.8 s | 580 | 36,752 | 37% | 55,535 |

"This family's lines" counts the `all_equal`-hinted `a` lines at
`Inferences`, split by the literal they assert: bounds and values count one
line each at `Off`, and range removals four. The rows split as follows.

| G, m, D | Bounds | Values | Ranges |
|---|---|---|---|
| 2, 5, 40 | 1,203 | 673 | 28 |
| 3, 5, 40 | 14,410 | 6,748 | 36 |
| 3, 8, 100 | 24,045 | 11,871 | 209 |

Unlike `increasing`, the family is a large share of its own benchmark's proof,
since every decision propagates to the whole group. The rest is the shared
literal layer, the `NotEquals` holes and the enumeration's backtracking. Of the
`Inferences` assertions, 1,904 of 2,431, 21,194 of 26,710 and 36,125 of 41,806
carry this family's hint; the rest are the search's and `NotEquals`'s.

**Assertion levels.** At `Off` every probe proof verifies (`probes/fam.cc`,
`probes/runfam.sh`, modes `bounds`, `holes`, `mixed`, `views`, `wide`). At
`Definitions` and `Inferences`, VeriPB accepts each proof with
`s UNDER ASSERTIONS`, not `VERIFIED`. Every inference of this family is an `a`
line there, so only `Off` checks the family.

At `Links`, the two probes over interval domains (`bounds` and `views`) fail
at a `solx` step. That failure is generic rather than this family's, as for
the other families. The three probes whose variables were made from value
lists (`holes`, `mixed` and `wide`) are accepted `UNDER ASSERTIONS`.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is justified at `Off`, and the propagator is the same
with proofs on or off.

The wrong-answer bug is a propagation bug, not a proof gap: the inferences
it makes are all justified. What it misses is a constraint violation, and a
proof-logged run exposes that at the `solx` line, where VeriPB answers `The
given solution is conflicting with constraint …`.

### Known limitations

- **Wrong answers: solutions that violate the constraint.** This happens when
  `vars[0]` becomes single-valued during a call while some other position is
  left unequal to it, holding a different value or still more than one. The
  propagator then disables itself until backtrack, and those variables are
  never compared again below that node. On distinct variables, or plain
  repeats, it needs a hole in `vars[0]` inside the entry bounds `[lo, hi]` and
  no hole left after the bounds pass. A repeat through an offset or an
  opposite-sign view needs neither: the bounds pass, or the hole pass, can fix
  `vars[0]` through the other occurrence. The fact-check's simulation of one
  call over 300,000 random shapes per seed agrees, and 60 of the shapes it
  flagged are wrong on `c9ceea25` and right with the fix
  (`tmp/fd-small/factcheck2/all_equal/probes/`).
  - **Shapes:**
    - `AllEqual{x, y}` with `x ∈ {1, 3}`, `y ∈ {2, 4}` reports `(3, 2)`:
      `x` ends at `{3}` and `y` at `{2}`;
    - `x ∈ {1, 5}`, `y ∈ 0..3` reports three solutions, where there is one;
    - `{x, y, x + 1}` with `x ∈ 0..2`, `y ∈ 0..5`, all intervals: `x + 1 ≤ 2`
      fixes `x` mid-pass while `y ∈ 1..2`, and it reports two solutions where
      there are none;
    - the same shape with `x ∈ {−1, 0, 1, 2, 4, 5}`: the bounds pass leaves
      `x` holey, so the hole pass runs, and its removals from `x + 1` fix `x`
      while `y ∈ 1..2`; two solutions where there are none;
    - `{x, y, 2 − x}` with `x ∈ 0..3`, `y ∈ 1..5`, all intervals: `2 − x ≥ 1`
      fixes `x` mid-pass, and it reports `(1, 1)` and `(1, 2)` where only the
      first is a solution;
    - `{x, x + 1}` over an odd-sized domain reports every value of anything
      else (`probes/disable.cc`, cases `e`, `c`, `h`, `i` and `j`, output in
      `probes/disable.txt`; `probes/aliaswide.cc`).
  - **How often,** on random models with side constraints (`probes/searchfuzz.cc`,
    seeds 1 and 2, 3,000 models each):
    - interval domains, with holes made during search by `NotEquals` and
      bound moves by `x + z ≤ c`: 6 and 7 wrong solution counts under
      in-order smallest-value-first branching; none under the default search;
    - holey starting domains: 94 and 90 wrong counts, and 91 and 84 under the
      default search.
  - **Front ends:**
    - XCSP3 with `--all` reports `x = 1, y = 2` and `x = 1, y = 3` alongside
      the right `x = 1, y = 1` for `xcsp/wrong.xml`; in its default
      first-solution mode it reports `(3, 2)` for the headline shape;
    - the `.scp` reader does the same for `scp/wrong.scp`;
    - MiniZinc, with `int_search(..., indomain)`, which maps to
      `smallest_first`. `mzn/small3.mzn`, three variables with a `≠` and two
      sums, has 8 solutions, and the solver gives 9, including `[2, 2, 1]`,
      on both 2.9.7 and 2.10.1. It was found by the fact-check's MiniZinc
      fuzz, in which 11 of 3,000 random models give wrong counts
      (`tmp/fd-small/factcheck/all_equal/mzn/fuzz_indomain.py`). A six-variable
      model found by the C++ fuzz and translated by hand gives 360 where there
      are 252 (`mzn/t437i.mzn`). With `indomain_min` (`smallest_in`, `=` then
      `≠`) both are right, and a 300-model fuzz with it found nothing
      (`mzn/fuzz.py`).
  - **The fix,** tested: disable only when the entry bounds met, `lo == hi`.
    At that point the bounds pass has pinned every variable to `lo`. On
    `c9ceea25` plus the one-line change, every probe above gives the right
    answer:
    - the search fuzz: none wrong in 12,000 (in-order search, interval and
      holey starting domains);
    - the root probe: GAC on distinct variables;
    - 300 random proofs verify;
    - the MiniZinc models give 8 and 252;
    - `all_equal_test` passes in both lanes, and so do both chain cases and
      `scp/wrong.scp`'s chain.

    Gecode's `NaryEqDom` has the same shortcut (`x[0].assigned()` →
    subsumed), and is right because its bounds loops restart on every landed
    bound.
- **A repeated variable through offsets or an opposite-sign view** is either
  slow to fail (`{x, x + 1}`: W/2 calls) or not `bounds(Z)` (`{x, c − x}`: no
  root pruning, and W search nodes to refute when unsatisfiable). Only the C++
  API can post one.
- **No faster than `n − 1` `Equals`** on the one benchmark measured, despite
  far fewer calls.
- **A reified `all_equal` from MiniZinc** is decomposed pairwise by the
  standard library, `n(n − 1)/2` reified equalities.
- **XCSP3's `allEqual` over expressions** answers `s UNSUPPORTED`.

### Next steps

1. **Fix the entailment test.** Replace
   `if (state.has_single_value(vars[0]))` with `if (lo == hi)`, which
   guarantees that the bounds pass has just pinned every variable or
   contradicted. Tested as above (`fix-entailment.patch`). The fix needs
   regression tests, since the suite misses the bug:
   - the two-variable shapes, with `vars[0]` holey;
   - `{x, y, x + 1}` over intervals and with `x ∈ {−1, 0, 1, 2, 4, 5}`,
     `{x, y, 2 − x}` over intervals, and `{x, x + 1}` at an even and an odd
     width;
   - a few seeded models with holes made during search, and `mzn/small3.mzn`
     as a MiniZinc test.

   Also correct the class comment's "achieves GAC in a single propagator
   pass" (not over holes, and not on repeats) and the code comment on the
   test. Trivial. Filed as #1153 (bug, wrong answers).
2. **Decide repeated variables at install.** Every position is `s·u + c` for
   an underlying `u`, and two positions over one `u` fix everything between
   them:
   - with the same sign, the offsets must agree, or the constraint is
     unsatisfiable, so contradict at once; if they agree, drop the duplicate;
   - with opposite signs, `2u = c₂ − c₁` fixes `u`, or is unsatisfiable when
     odd, so post the unary constraint.

   After that, every position is a distinct variable, and the propagator is
   GAC. This is the same fix `increasing` needs (#1144), and simpler here
   because equality decides every repeat outright. Untested. Small; it buys
   robustness on shapes only the C++ API reaches. Filed as #1154.
3. **Find out why the class is not faster than the chain.** The profile points
   at copying and intersecting every domain on every call once any has a hole,
   even when one value changed. Maintaining the intersection, or skipping the
   hole pass when the change was a bound, might recover the advantage the
   call counts suggest. This is empirical, and small to try. Not worth an issue
   until it has been tried.
4. **Correct the stale text elsewhere.** Trivial, and can ride with step 1:
   - `large_domain_audit_test.cc:438–449`: the `AllEqual/holes` row's comment,
     including its stale `all_equal.cc:114`;
   - [`large-domains.md`](../large-domains.md), line 664: `all_equal.cc` is
     listed as carrying a per-value loop counter, but it has no per-value loop;
   - [`large-domains.md`](../large-domains.md), lines 920–923: says the middle
     is removed "one value at a time", and cites `all_equal.cc:95` for the
     bounds pass.
5. **Widen the audit lane.** Add rows with more than three variables, a mixed
   witness, a view, and a same-sign repeat over the full width. The repeat
   would pass, since the guard counts values walked per call; it wants a
   propagation-count check instead, which `increasing`'s row would want too.
6. **XCSP3 `allEqual` over expressions.** Post each tree through the existing
   intension path to an auxiliary or a view, then `AllEqual`. Small; no corpus
   evidence that it is needed.

## Prior art

Nobody publishes a propagation algorithm for n-ary equality as such. Domain
consistency is the intersection of the domains, which is what this family
computes. Gecode's `rel(home, x, IRT_EQ)` posts `Rel::NaryEqDom` at `IPL_DOM`
or the default, and `Rel::NaryEqBnd` at `IPL_BND` (`gecode/int/rel.cpp`,
`gecode/int/rel/eq.hpp`). `NaryEqDom` handles a bound event with restarting
bound loops, subsuming once `x[0]` is assigned, and a domain event with an
n-ary range intersection.

The proof side is the equality's: JP 3.2 and JP 3.12 in Matthew McIlree's
thesis, applied along the chain. What is not in the thesis is the multi-hop
bound transfer, which this family relies on and which is checked here rather
than proved.

## Further reading

- [`equals.md`](equals.md): the binary case, the same equality row, and the
  `justify_not_in_range_across_equality` helper this family's range rule
  uses.
- [`justification-techniques.md`](../justification-techniques.md): Theorems
  2.8 and 2.9, JP 3.2 and JP 3.12, and where 2.9 stops.
- [`large-domains.md`](../large-domains.md): the interval rewrite of the hole
  pass (#833), and the two lessons it records about keeping the one-value form
  and checking for a single witness before splitting.
- [`view-proof-logging.md`](../view-proof-logging.md): why a view's offset and
  sign do not change the chain rows.
