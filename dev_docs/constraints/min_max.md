# `min_max`: a variable is the minimum or the maximum of an array

> **Maturity** production ·
> **Audited** 2026-09-30 at `c9ceea25` ·
> **Open issues** none filed by this audit yet; see [Next steps](#next-steps)
> for what it would file. Already open and touching this family: #833 (the
> large-domain policy; this family's audit row is `KnownTrip`), #868
> (cross-solver comparisons; this document gives one, by hand). Tracked under
> #871.

Four posted classes, `ArrayMin`, `ArrayMax`, `Min` and `Max`, over one class,
`ArrayMinMax`, and one propagator. `Min` and `Max` are the two-entry case.
The encoding says "the result is at most (or at least) every entry, and equal
to one of them", with a selector flag per entry. The propagator:
- pushes bounds both ways;
- cuts the result to the union of the entries;
- makes the last entry that can still reach the result equal to it;
- then makes a per-value pass over the array.

Five things to know before touching it.

- **It is generalised arc consistent on distinct variables, holes included.**
  But the last pass is what buys that, and it costs the width of the domains
  on every call, whether or not it removes anything.
  - **Without the pass,** the other rules are already GAC on interval domains,
    and `bounds(D)` with holes. Gecode's domain-consistent maximum stops
    almost exactly there: its binary propagator also equates an entry that
    dominates the other with the result, which rules 1 to 4 do not.
  - **What the pass costs.** On three MiniZinc Challenge models with wide
    domains, calls average 1 to 6 s, and one call on `2022_tower` takes about
    a minute. The search makes one to seven nodes in a minute and finds no
    solution, and the time limit overshoots by up to 44 s. With the pass
    switched off, the same models find 3 to 58 solutions.
  - **Why the audit row trips.** This pass is why the family's large-domain
    audit row is still `KnownTrip`.
- **A result that shares a variable with an entry through a view breaks
  it.** `Min{z, y, z − 1}` and `ArrayMin{{z + 1}, z}` are examples.
  - **A crash.** The propagator can throw `UnexpectedException` ("missing
    support") where it should fail, which ends the search. That happens on
    unsatisfiable models, and on satisfiable ones mid-search, before the last
    solution.
  - **Rejected proofs.** The per-value pass and the single-support rule both
    occasionally write a proof VeriPB rejects, in both directions, because
    their justifications read `state` after the inference has already changed
    it.
  - **Who can reach it.** The C++ API and `gcspy` can post the shape. CPMpy
    can post it over Booleans (`min([b, 1 − b]) == b`), where it is harmless.
    The three fixes are small, and tested together.
- **Plainly repeated variables are sound but weaker.** `ArrayMin{x, x} = y`
  does not even reach `bounds(Z)`.
- **The encoding matches `cake_pb_cp`'s row for row, but it is unlabelled and
  in a different order.** So the three SCP chain cases can only be `none`.
  The comment giving #358 as the reason is stale.
- **Its single-support rule's reason and proof are per value of the result.**
  The reason names `x ≠ r` for every value `r`, where a bound would do.

## What it is

### Semantics

`ArrayMinMax(vars, result, min)` holds exactly when `result` equals the
smallest value in `vars` (for `min`) or the largest (for `max`).
- **The four classes:** `ArrayMin` and `ArrayMax` fix the flag. `Min{a, b, r}`
  and `Max{a, b, r}` are the same with `vars = {a, b}`.

The degenerate cases:
- **Empty array:** rejected. `prepare()` throws
  `InvalidProblemDefinitionException` ("not sure how min and max are defined
  over an empty array"), at install, so from inside `solve`. `min_max_test`
  checks this for both directions (#254).
- **One entry:** `result = x`, propagated as the general case. MiniZinc never
  posts it: `max([x])` flattens to an alias.
- **Constants,** in the array or as the result, are accepted. The test covers
  all-constant arrays with a constant result, true and false (#254).
- **A repeated variable** is accepted anywhere. With a plain repeat (no view)
  it stays sound and loses strength. The result sharing a variable with an
  entry through a view is the broken case. See [Robustness and
  limits](#robustness-and-limits).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `ArrayMin` | ✓ `array_int_minimum`[^mzn] | ✓ `minimum` over a list of variables, with a condition[^xcsp]; `min` inside `intension` | ✓ `min(…) == y`, through `gcspy`'s `post_min`[^cpmpy] | ✓ `array_min` | |
| `ArrayMax` | ✓ `array_int_maximum`[^mzn] | ✓ `maximum`, and `max` inside `intension`[^xcsp] | ✓ `max(…) == y`, through `post_max`[^cpmpy] | ✓ `array_max` | |
| `Min` | ✓ `int_min` | through `ArrayMin` | through `ArrayMin` | written as a two-entry `array_min` | |
| `Max` | ✓ `int_max` | through `ArrayMax` | through `ArrayMax` | written as a two-entry `array_max` | |
| `arg_min`, `arg_max` | `decompose`: the standard library's, which posts an `array_int_minimum` or `array_int_maximum` and reified comparisons | `unsupported`: `minimumArg`, `maximumArg` | ? | — | no class exists |
| indexed or tree-list `minimum` / `maximum` | n/a | `unsupported`[^xcsp] | — | — | |

[^mzn]: `fzn_glasgow.cc` posts `array_int_minimum` / `array_int_maximum` at
    line 551, and `int_max` / `int_min` at lines 724 and 730. The mznlib
    declares the two array builtins in `redefinitions-2.0.mzn`. Flattening
    fourteen shapes with `build/glasgow.msc` on 2.9.7 and 2.10.1
    (`tmp/fd-small/min_max/mzn/shapes.sh`) gives the same builtins on both:
    - `max([x])` flattens to nothing, an alias;
    - `max` over two entries flattens to `int_max`;
    - three or more give `array_int_maximum`, which keeps a constant entry
      (`max([x1, x2, x3, 4])`) and takes expressions through `int_lin_eq`
      helpers;
    - a Boolean `max` goes through `bool2int` to `array_int_maximum`;
    - `b <-> (max(x) = 3)` is the functional `array_int_maximum` plus an
      `int_eq_reif`, so no reified form is needed;
    - an optional-variable array and `arg_max` reach `array_int_maximum` inside
      the standard library's decomposition.

    The twelve satisfaction shapes that post the family (all but `max([x])`
    and a `minimize max(x)` objective) give the same number of solutions as
    Gecode on both versions.

[^xcsp]: `build_min_max_common` (`xcsp_glasgow_constraint_solver.cc`, line
    1198) creates an auxiliary result over the entries' hull, posts
    `ArrayMin`/`ArrayMax`, and applies the condition to the result.
    `intension`'s `min` and `max` (line 1447) also make a fresh result, with
    tighter bounds than the hull: the minimum's upper bound is the smallest
    upper bound, and the maximum's lower bound the largest lower bound.
    The indexed, tree-list and `*Arg` forms fall through to the parser's
    defaults, which throw. The solver reports `s UNSUPPORTED`, checked for the
    indexed `minimum` (`tmp/fd-small/min_max/xcsp/minargs.xml`). Since the
    result is always fresh, XCSP3 cannot reach the aliased-view defect.

[^cpmpy]: CPMpy's upstream GCS interface, checked 2026-09-30, lists `min` and
    `max` among its supported globals and posts `min(args) == rhs` as
    `post_min(args, rhs)`. The one view its variable translation makes is
    `1 − b`, for a negated Boolean; its other `negate` calls build the
    arguments of linear constraints. All 672 min/max shapes over two
    Booleans and their negations, up to three entries, give the right answer
    and verifying proofs (each run with `tmp/fd-small/min_max/one.cc`; the
    fact-check's `boolshapes.cc` driver agrees). `min([b, 1 − b]) == b` is the
    aliased shape, so CPMpy can post it, but over `{0, 1}` no instance goes
    wrong. `gcspy` can post the harmful integer shapes.
    - **A binding bug.** `gcspy.hh` defines `WRITE_API_CALLS` unconditionally,
      and `post_min`'s logging loop runs to `var_ids.size() − 1` and reads
      `var_ids.back()`, both undefined on an empty list. So an empty
      `post_min` has undefined behaviour rather than the clean exception.
    - **A logging bug.** `post_max` logs only the string `post_max`.

Positions are all that matter here: no value is an index, so an array indexed
from something other than 1 cannot be mistranslated the way #987's were.

### Options

`None.` There is no `with_consistency()` and no algorithm switch.

### Variable kinds and views

Any `IntegerVariableID`, in any position. The propagator reads domains through
`State`, so a view is propagated like a variable.

**The proof handles views** on distinct variables. Since #904 a registered
view has its own range literals over its own encoded variable, and the model
states its rows in that same representation. So the bound lemmas cross the
rows directly (see [`large-domains.md`](../large-domains.md), "Getting a range
removal past the checker"). The `view_mixed` lane runs every test shape with
views wrapped around distinct variables. So do 3,000 random enumerations per
direction, each position a `±` view with offset `−1..1` of its own variable,
under the idempotence checker (`tmp/fd-small/min_max/idemv.cc`).

**The exception** is a result that shares a variable with an entry through a
different view. That is the defect under [Robustness and
limits](#robustness-and-limits).

### Reification

`None.` Minimum and maximum are functional and total, so a reified use is the
functional constraint plus a reified equality on its result. That is how
MiniZinc flattens `b <-> (max(x) = 3)`. No class is wanted.

### Relation to other families

- **Decomposes into it:**
  - MiniZinc's `int_min`, `int_max`, `array_int_minimum` and
    `array_int_maximum`, and the standard library's `arg_min` / `arg_max` and
    optional-variable decompositions;
  - XCSP3's `minimum`, `maximum`, and `min` / `max` inside `intension`.
- **Child constraints:** none.
- **Shares code:** the single-support rule calls
  `justify_not_in_range_across_equality` (`innards/justify_not_in_range`),
  without a guard. `equals`, `all_equal`, `in` and `element` also call it. The
  result-in-union rule writes the same lemmas with a selector guard inline, not
  through the helper's `under` argument.
- **Presolvers:** none recognises it. `AutoTable` tabulates whatever the
  variables it is given carry; see [`table.md`](table.md).
- **Reachable directly:** yes, from every front end.

## The proof model

### OPB encoding

For `min` (for `max`, negate both sides of every row). One selector flag
`f_i` per entry, named `x[<id>][i]`:

```
for each i:   x_i − result ≥ 0                   the result is at most every entry
for each i:   f_i ⇒ x_i − result ≤ 0             a selected entry equals it
for each i:  ¬f_i ⇒ x_i − result ≥ 1             an unselected entry is strictly above it
              Σ_i f_i ≥ 1                         some entry is selected
```

- **It is definitional:** `result = min(x)` exactly when some `f` assignment
  satisfies the rows, and a solution fixes each `f_i` to `[x_i = result]`.
- **Its size:** `3n + 1` rows and `n` flags. The rows are over bit sums, so
  the encoding is logarithmic in width.
- **Why the third line is there.** The `¬f_i` half makes the selector
  fully reified. That is what lets an enumeration proof pin `f_i` at a
  solution, as `cake_pb_cp`'s encoding needs.

### Labels

`None.` No row is labelled, and no rule cites one. Every step is a RUP that
finds its rows by propagation, and the selectors are named proof flags,
`x[<constraint id>][<position>]`.

### Cake conformity

`cake_pb_cp`'s `array_min` / `array_max` is the same `3n + 1` rows:
- `@x[id][i][f]` and `@x[id][i][r]` for the two halves of each selector;
- `@c[id][<i>ge]` for the unconditional rows;
- `@c[id][al1]` for the at-least-one.

**`opbdiff --unordered` finds the two OPBs semantically equivalent**, 18
constraints each, for all three chain cases (`array_min_sat`, `array_max_sat`,
`array_min_unsat`; `tmp/fd-small/min_max/chain/`). The solver writes the rows
unlabelled and in a different order. So `--match-labels` falls back to
position and fails, and the cases are registered as `none`. All three
chain-verify.

`verified_encodings/scp_cases/CMakeLists.txt` (line 282) gives the eq/ge
literal divergence of #358 as the reason they stay `none`. #358 is closed, and
these OPBs carry no eq/ge literal definitions to diverge; the reason now is
only the labels and the order.

### Proof-time state

- **The selectors** are the only auxiliaries. They are **in the OPB**,
  introduced by `define_proof_model`, and each is fixed by unit propagation on
  a solution: the value of `x_i − result` decides which half-row can hold.
- **Nothing is emitted at the root** as scaffolding.
  - Every lemma is written at `ProofLevel::Temporary` and deleted with its
    inference.
  - Every conclusion is written at the current search level, and the shared
    backtrack machinery deletes it.
  - Nothing a later step needs is deleted.
- **Naming.** An external tool finds a selector by name, `x[<constraint
  id>][<position>]`, and the rows by the selectors and variables they mention.
- **Proofs off.** `_selectors` stays empty when proofs are off, since
  `define_proof_model` is not called. Only the justifications index it, and
  they run only with a logger.

## The implementation

### Initialisation and global data

- **`prepare()`** throws on an empty array and otherwise does nothing.
- **Initialiser:** none.
- **`define_proof_model`** writes the `3n + 1` rows.
- **Nothing is precomputed.**

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| the min/max propagator | `on_change`, the result and every entry | derived: **every variable**, and truly | 1–5 | always | never claims; one call is a fixpoint on distinct variables | never |

**Holes affect: the derived answer is the true one.** The result-in-union rule
reads every entry's interior and the result's. The entry pass reads both
through `in_domain` and the per-value walks. So a hole anywhere can change what
is inferred.

**Idempotence.** Not claimed, since the propagator always returns `Enable`. A
claim would be true on distinct variables:
- **How it was checked.** A build patched to return `EnableButIdempotent`, run
  under `GCS_CHECK_IDEMPOTENT_CLAIMS`, refutes no claim in full enumerations of
  3,000 random instances per direction, both over domains with holes and over
  intervals. It refutes none in 3,000 per direction over distinct variables
  behind views either.
- **The control.** The same build with `Increasing` patched the same way throws
  "claimed idempotence, but re-running it did more" on `increasing.md`'s
  two-call shape (`tmp/fd-small/min_max/idem.cc`, `idemv.cc`, `idemctl.cc`).
- **Aliasing.** The machinery ignores a claim when trigger positions alias, so
  a claim would also be safe on repeated variables. The fix for the
  aliased-view throw relies on the propagator being woken again by its own
  removals, which holds there either way.

**Self-disabling.** Never, even once everything is fixed.

### Mutable state and incrementality

`None.` Nothing persists between calls.
- **What each call copies:** the result's domain, and each entry's in turn,
  for the union; the support's and the result's domains again when the
  single-support rule fires; and `vector scope = vars` for the entry pass, a
  heap allocation on every call.
- **What each call recomputes:** the other entries' limit and the extreme
  value any other entry can supply, for every position.
- **What maintaining them would buy:** the pass's `n²` factor. That is minor
  next to its width factor ([Interval efficiency](#interval-efficiency)).

### Interior values and optional pruning

**Offers.** `None.` The per-value entry pass is the natural candidate:
- **What it would buy.** Measured at the root, the rules without it stay
  `bounds(D)` on every instance, so the pass removes only interior values.
- **Why it does not qualify as it stands.** The second promise fails: the
  result-in-union rule reads the entries' interiors, so an interior value the
  pass removes can change what the union rule removes from the result.
- **What would make it qualify.** A pair would have to take the result as a
  target as well as the array. See [Next steps](#next-steps).

**Observes.** **Every variable, result and array alike.** A min or max in a
model keeps any other constraint's optional interior pruning alive on all of
its variables. That is correct, since both the union rule and the pass read
interiors.

### Robustness and limits

**Unbounded domains.** Every call walks the result's domain once per entry,
and each entry's domain once, in the entry pass. See [Interval
efficiency](#interval-efficiency). One call over three entries and a result,
all `0..10⁸`, takes 12.4 s.

**Negative values and zero.** Tested: the fixed shapes reach from −8 to 12,
and the random ones from −5 to 13.

**Degenerate shapes.**
- *Empty:* throws, as [above](#semantics).
- *One entry, constants, all-constant:* covered by the test.
- ***A plain repeated variable*** is sound, but weaker than `bounds(Z)`.
  - **Measured.** At the root, over 3,000 random instances per direction with
    holes, where positions draw from fewer variables and there are no views
    (`tmp/fd-small/min_max/mmcheck.cc`, mode `alias`, seed 1):
    - GAC fails on 133 (min) and 133 (max);
    - `bounds(D)` and `bounds(Z)` fail on 41 and 39.
  - **An example.** `ArrayMin{x, x} = y`, with `x ∈ {−3, 0, 1, 2, 3}` and
    `y ∈ {−3, −2, −1, 0, 1, 2}`, keeps `x = 3`, which has no support.
  - **Why.** The rules take the two positions for two variables. Each counts
    the other as a possible support, so the single-support rule never fires.
  - **Proofs.** 150 random instances per direction verify, as do the test's
    duplicate runs.
- ***A result sharing a variable with an entry through a different view***
  (`Min{z, y, z − 1}`, `ArrayMin{{z + 1}, z}`, `ArrayMin{{y + 1, 1 − x, y + 1},
  −x}`) breaks two things. Entries sharing a variable with each other through
  views, the result having its own, are only weaker: 1,500 enumerations per
  direction all give verifying proofs with no throw, and the root probe finds
  `bounds(Z)` failing on 1,289 (min) and 1,277 (max) of 3,000 (`mmcheck.cc`,
  mode `entryviews`).
  - **The support scan throws.** The union rule removes result values no entry
    holds. Those removals also shrink the entry the result shares a variable
    with, so the support scan straight after can find no entry meeting the
    result, and it throws `UnexpectedException: missing support, bug in
    MinMaxArray propagator` (`min_max.cc`, line 199).
    - **The failure it replaces.** It throws where the node should fail. On an
      unsatisfiable model that is the only answer (`ArrayMin{{z + 1}, z}`).
    - **On satisfiable models.** It also ends a search early. Over 20,000
      random instances per direction whose positions are `±` views of shared
      variables (about 14,000 of them with the result sharing a variable with
      an entry through a different view), it threw on 44 satisfiable (min) and
      32 (max), 38 and 28 of them before the last solution (`satthrow.cc`, seed
      2).
  - **Two justifications read `state` after their own inference.** The
    tracker applies an inference before running its justification
    (`inference_tracker.hh`: rule 5's `infer_not_equal` around line 306,
    rule 4's `infer_not_in_range` at lines 533–540). So when the variable an
    inference is on shares a variable with the result, result values the
    lemmas walk are already gone, their lemmas are never written, and VeriPB
    rejects the proof. Both directions are affected.
    - **The entry pass (rule 5).** `ArrayMin{{y + 1, 1 − x, y + 1}, −x}` with
      `x ∈ {1, 3, 4}` and `y ∈ {−2, 4}` is rejected at its conclusion.
      `ArrayMax{{−y, 1 − w, y + 1, −1 − w}, y + 2}` with `y ∈ {0, 3, 4}` and
      `w ∈ {−3, −1, 4}` is rejected too.
    - **The single-support rule (rule 4).** `rule_out_other_selectors` walks
      `state` after `infer_not_in_range` on the support, and then the bridge
      lemma fails. `ArrayMin{{v1 − 2, −v2, 1 − v0}, −v0 − 2}` with `v0 ∈ −3..3`,
      `v1 ∈ {−3, −2, −1, 4}`, `v2 ∈ {−2, 4}`, and `ArrayMax{{x, y − 2, y},
      y + 2}` with `x ∈ {−2, 3, 4}`, `y ∈ {−3, −2, 0, 1, 2}`, are rejected.
      The rule-4 failures found need two views whose offsets differ by at
      least 2; none has been seen at 1. `ArrayMin{{−x − 1, −y − 4}, −x − 3}`,
      with `x ∈ 1..5` and `y ∈ {−2, 3, 4}`, is a difference of 2.
    - **How often.** Rare. Over the random view-aliased sweeps (`mmcheck.cc`,
      views mode, positions `±v + b`):
      - `b ∈ −1..1`, seeds 11 and 21: min rejected 3 of 1,922 and 1 of 1,939;
        max none of 1,949 and 1,957;
      - `b ∈ −2..2`, seed 31: min none of 1,919, max 1 of 1,939;
      - `b ∈ −3..3`, seed 31: none of 1,914 and 1,932.

      Every one of these is rule 5's.
  - **Fixes, three.** Replace the throw by a return, so that the propagator is
    woken again by its own removals. Capture the result's values before
    inferring, in rule 5. Walk the pre-inference `result_set` rather than
    `state` in `rule_out_other_selectors` (rule 4). With all three
    (`fix-aliased-views.patch`):
    - the four instances above verify;
    - 8,000 of 8,000 random proofs verify with view offsets up to 2 and up to
      3 (seed 31, both directions), with no throw;
    - the fact-check's own sweep verifies 16,000 of 16,000.

    With only the first two, the rule-4 instances are still rejected.
  - **Who can reach it.** The C++ API and `gcspy`:
    - FlatZinc hands min and max only plain variables and constants.
      `fzn_glasgow.cc` does make views, but not into min and max: it recovers a
      two-term equality (around line 649) as an `Equals` between a variable
      and a view, and it shifts zero-based arrays for other families;
    - XCSP3's result is always fresh;
    - the `.scp` reader takes only atoms as operands, so a `.scp` file cannot
      post a view, although the writer emits one.

**Overflow.** Every `+ 1` is on a bound (`ub + 1`, `hi + 1`) and goes through
`Integer`, which throws `IntegerOverflow` rather than wrapping. A bound at
`±2⁶¹` plus one is in range.

**Time limits.** A call is not interruptible: the abort flag is checked
between propagators. On `2022_tower`, 77 calls take 104 s against a 60 s
limit, and one of them takes 59.8 s on its own (the fact-check's per-call
timer; the next slowest take 7.4, 2.6 and 2.5 s). See [CPU
performance](#cpu-performance).

### Interval efficiency

**Not width-independent: the entry pass is per value, on every call.** The
rest of the propagation is interval-level.

1. **The propagation side.**
   - **The two bound rules:** `O(n)` bounds reads.
   - **Result in union:** `IntervalSet::erase_range` over each entry's
     intervals, and `infer_not_in_range` per remaining run (#815). Per
     interval.
   - **Single support:** `domains_intersect` to find the supports, and
     `each_interval_minus` for the runs to remove. Per interval.
   - **The entry pass (lines 278–325) is per value.** For each position `i`,
     it walks the result's domain (line 291), with an `in_domain` scan over
     the other entries per value. It then walks `x_i`'s domain (line 303).
   - **Cost per call:** `Θ(Σ_i |D(x_i)|)`, plus between `n·|D(result)|` and
     `n²·|D(result)|` steps, whatever it removes.
   - **Measured.** One root call of `ArrayMax` over three entries and a
     result, all `0..W` (`wprobe.cc`): 0.013–0.025 s at `W = 10⁵`,
     0.124–0.130 s at 10⁶, 1.29–1.75 s at 10⁷ (three runs each), and 12.4 s
     at 10⁸ (one run). At `W = 10⁶`: 0.086 s with two entries, 0.249 s
     with six.
   - **The guard.** A guard build of `c9ceea25` trips at line 291, or at line
     303 when the result is narrow (`wprobe.cc`, modes `root` and `single`).
   - **What the pass buys.** It removes nothing on interval domains. Without
     it, the root fixpoint is GAC on all 6,000 random interval instances
     (1,702 of which fail at the root, trivially) and `bounds(D)` on all
     6,000 with holes, with GAC failing on 114 (min) and 99
     (max) (`mmcheck.cc`, modes `plainiv` and `plain`, against a build with
     the pass switched off).
2. **The reason side.**
   - **The bound rules:** one literal, built as an `ExplicitReason` for every
     entry on every call, including when nothing changes, unguarded.
     `ReasonLiterals` holds two literals inline, so these do not allocate;
     they cost `2n` variant constructions and resets per call.
   - **Result in union:** one `x_i ∉ [lo, hi]` per entry and run, built per
     run, unguarded.
   - **Single support: per value.** The reason names `x_k ≠ r` for every
     other entry and **every value `r` of the result**. It is guarded on
     `want_reasons()`, so it costs nothing with proofs off.
   - **The entry pass:** `generic_reason` over the whole scope. It is
     snapshotted before each inference, and so materialised eagerly, only with
     proofs on, once per removed value. Its hole literals are per run.
3. **The proof side.**
   - **Result in union:** `3n + 1` lines per run, whatever its width.
   - **Single support:** one lemma per other entry and per value of the
     result, repeated for every run removed, plus the across-equality bridge
     per run. At the root of `Max{x, y, r}` with `x ∈ 0..5`, `y ∈ 0..W` and
     `r ∈ W/2..W`: 61 `rup` lines at `W = 100` and 511 at `W = 1,000`
     (`psize.cc`, mode `single`).
   - **The entry pass: per removed value**, `(n + 1)` lemmas for every result
     value beyond it. That is **quadratic in width** on a holey result:
     `max(x, 0) = r`, with `x ∈ 0..W` and `r` over the even values, writes 674,
     2,544 and 9,884 `rup` lines at `W = 40`, 80 and 160 (mode `quad`).
   - **No width gate** picks between forms anywhere.
4. **The audit lane.** One row, `ArrayMinMax`, pinned `KnownTrip`: `ArrayMax`
   over three wide distinct variables into a fourth (`large_domain_audit_test.cc`,
   line 601).
   - **Its comment is stale.** It blames "H1b (a missing hull bound) and H1a
     (the union scan)". The union scan has been interval-level since #815, and
     the trip is the entry pass.
   - **What it does not vary:** holes, views, `min`, a narrow result (which
     reaches line 303 rather than 291), a single-support shape, or proofs. So
     the reason and proof sides above are outside it.
   - **The proof-size case:** no row in `"Large domain proof sizes"`.

## Inference catalogue

Five rules. Three facts hold for all of them.

**There is one wire form.** `hints::MinMax`, `(constraint_id <id>)`, with no
subhint and no payload. The clause's shape tells the rules apart, and fixes
the procedure. Rules 1 and 2 share a shape, and a procedure.

**No rule has a published procedure.** McIlree's thesis has none for minimum
or maximum. The rules rest on its general results, which
[`justification-techniques.md`](../justification-techniques.md) collects:
- Theorem 2.9 for a bound crossing a row with `B ∈ {0, 1}`;
- Theorem 2.6 for a step under a selector;
- Theorem 2.8 for a value crossing an equality;
- Theorem 3.2 for a collapse.

The two bound rules are JP 3.2 exactly. The union and entry rules are
Element's JP 3.10 and JP 3.9 in shape, generalised to a range and to a
selector per entry.

**A conflict is not a rule.** It arises when an inference's literal is already
false. The tracker then asserts `attempted literal ∨ ¬reason` as for a success,
and the backtrack closes it. No rule calls `contradiction()`. The one place
that should fail and does not is the aliased-view throw
([Robustness](#robustness-and-limits)).

The shapes below are for `max`; `min` mirrors them.

### Rule: result-bound-from-entry

- **Infers** — for `max`, `result ≥ lb(x_i)` for each entry. For `min`,
  `result ≤ ub(x_i)`.
- **Fires when** — any variable changes; the first loop of every call.
- **Strength** — with rules 2–4, `GAC` on interval domains and `bounds(D)` with
  holes, on distinct variables. With rule 5, `GAC` with holes. Checked by brute
  force at the root over 3,000 random instances per direction and shape
  (`mmcheck.cc`; seed 1). `min_max_test` also checks GAC at every node.
- **Algorithm** — one pass over the entries, `O(n)` bounds reads.
- **Why it is true** — the maximum is at least every entry.
- **Proof technique** — `RUP`, by **JP 3.2**, licensed by **Theorem 2.9** with
  `B = 0`. The reason, the negated conclusion and the unconditional row
  `result − x_i ≥ 0` are 2.9's triple.
- **Reason** — `{x_i ≥ lb(x_i)}`, one literal. Minimal. Built on every call for
  every entry, unguarded.
- **Assertion** — `result ≥ L ∨ ¬(x_i ≥ L)`. Measured at `Inferences`:
  ```
  a 1 i[r][ge5] 1 ~i[x2][ge5] >= 1::min_max:((constraint_id _1));
  ```
  Rule 2's clauses have this same shape over the same row, so the two are one
  procedure to a reconstructor.
- **Hint** — `hints::MinMax`: `originator`, the `ConstraintID`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per inference.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` No mutation lane exists for this family.

### Rule: entry-bound-from-result

- **Infers** — for `max`, `x_i ≤ ub(result)` for each entry. For `min`,
  `x_i ≥ lb(result)`.
- **Fires when** — the second loop of every call.
- **Strength** — as rule 1.
- **Algorithm** — `O(n)` bounds reads.
- **Why it is true** — no entry exceeds the maximum.
- **Proof technique** — `RUP`, by **JP 3.2** over the same unconditional row.
- **Reason** — `{result ≤ ub(result)}`, one literal. Minimal. Unguarded.
- **Assertion** — `¬(x_i ≥ U + 1) ∨ result ≥ U + 1`, the same clause shape as
  rule 1. For `min`, measured: `a 1 ~i[r][ge1] 1 i[x2][ge1] >= 1::min_max:…`.
- **Hint** — `hints::MinMax`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: result-in-union

- **Infers** — `result ∉ [lo, hi]` for each run of the result's domain that no
  entry holds.
- **Fires when** — every call, after rules 1 and 2. This is also what bounds
  the result from its loose side: the result's lower bound for `min`, and its
  upper bound for `max`.
- **Strength** — as rule 1.
- **Algorithm** — copy the result's domain, erase each entry's intervals, and
  remove what is left run by run. `O(Σ_i intervals(x_i) + intervals(result))`
  (#815).
- **Why it is true** — the result equals some entry, and none can take a value
  in the run.
- **Proof technique** — `RUP sequence`, ours: the guarded form of
  `justify_not_in_range_across_equality` given in
  [`large-domains.md`](../large-domains.md).
  - **The lemmas, per entry, three:**
    - a lower-bound lemma and an upper-bound lemma, each crossing one row.
      The one crossing the half-reified row carries `¬f_i`: the lower-bound
      lemma for `max`, and the upper-bound one for `min`;
    - `¬f_i ∨ result ∉ [lo, hi] ∨ x_i ∈ [lo, hi]`.
  - **Licences:** Theorem 2.9 with `B = 0` for each bound lemma, under Theorem
    2.6 for the guarded one.
  - **The conclusion:** RUP against the at-least-one row. The reason makes
    every `x_i ∈ [lo, hi]` false, so every `f_i` falls.
  - **The precondition:** the rows are over each operand's own encoded
    variable, which since #904 holds for views too.
- **Reason** — `{x_i ∉ [lo, hi]}` for every entry: `n` literals per run,
  minimal given the run, unguarded.
- **Assertion** — `result ∉ [lo, hi] ∨ ⋁_i x_i ∈ [lo, hi]`. Measured:
  ```
  a 1 ~i[r][in5_7] 1 i[x0][in5_7] 1 i[x1][in5_7] 1 i[x2][in5_7] >= 1::min_max:((constraint_id _1));
  ```
- **Hint** — `hints::MinMax`.
- **Offline reconstructibility** — `offline`. The run and the entries are read
  off the clause, the selectors are found by name, and the procedure is fixed.
- **Proof size** — `3n + 1` lines per run, **independent of width**.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: single-support

- **Infers** — `x_s ∉ [lo, hi]` for each run of `D(x_s) \ D(result)`, when
  `x_s` is the only entry whose domain meets the result's.
- **Fires when** — every call, after rule 3, when `domains_intersect` finds
  exactly one supporting entry.
- **Strength** — as rule 1; this is what makes the last support equal to the
  result.
- **Algorithm** — `domains_intersect` per entry until two supports are found,
  then `each_interval_minus`. Per interval.
- **Why it is true** — the result equals some entry, only `x_s` can, so
  `x_s = result`.
- **Proof technique** — `RUP sequence`, ours.
  - **The per-value lemmas.** For every other entry `x_k` and every value `r`
    of the result: `¬f_k ∨ result ≠ r`, by Theorem 2.8 (`f_k` makes `x_k`
    equal the result, and the reason says `x_k ≠ r`). Then `¬f_k`, by Theorem
    3.2's collapse over the result's domain.
  - **The bridge.** With those, the at-least-one row forces `f_s`, and
    `justify_not_in_range_across_equality` bridges `result ∉ [lo, hi]` across
    the now-active equality: two lemmas by Theorem 2.9 with `B = 0`.
  - **Where the values come from.** `rule_out_other_selectors` reads the
    result's values from `state` inside the justification, after the
    inference. That is rule 5's defect again; see Gaps.
  - **Per run.** `rule_out_other_selectors` runs inside each run's
    justification, so the per-value block is written again for every run.
- **Reason** — **per value:** `generic_reason(result)` plus `x_k ≠ r` for every
  other entry and every value `r` of the result, plus `result ∉ [lo, hi]`.
  Guarded on `want_reasons()`. Not minimal: the per-value literals are often
  implied by a bound that one literal would state. At the root of
  `Max{x, y, r}`, `x ∈ 0..5`, `r ∈ 10..20`, it names `x ≠ 10`, …, `x ≠ 20`.
- **Assertion** — measured, `D = 8`:
  ```
  a 1 ~i[x2][in0_3] 1 ~i[r][ge4] 1 i[r][ge8] 1 i[x0][eq4] 1 i[x0][eq5] 1 i[x0][eq6] 1 i[x0][eq7] 1 i[x1][eq4] 1 i[x1][eq5] 1 i[x1][eq6] 1 i[x1][eq7] 1 i[r][in0_3] >= 1::min_max:((constraint_id _1));
  ```
- **Hint** — `hints::MinMax`.
- **Offline reconstructibility** — `offline`. The supporting entry is the one
  the clause removes from, the other entries and the result's values are read
  off the reason, and the selectors are named.
- **Proof size** — **per value, per run:** `runs × ((n − 1)(|D(result)| + 1)
  + 3)` lines. For `Max{x, y, r}` with `x ∈ 0..5`, `y ∈ 0..100` and
  `|D(r)| = 22`, one run removed writes 23 selector lemmas and two runs write
  46 (the fact-check's `sruns.cc`). The equality literals the reason
  names also need defining. 61 `rup` and 1,288 lines in total at `W = 100`;
  511 and 12,088 at `W = 1,000` (`psize.cc`, mode `single`).
- **Gaps** — **the justification reads `state` after its own inference.**
  `rule_out_other_selectors` walks the result's current values, and when the
  support and the result share a variable through views, the removal from the
  support has already taken values off the result. Their lemmas are missing,
  and the bridge lemma is not RUP. Both directions; every failure found has
  view offsets differing by at least 2, none by 1
  ([Robustness](#robustness-and-limits)).
- **Tightness** — `Not shown.`

### Rule: entry-gac

- **Infers** — `x_i ≠ v` for each value `v` of each entry that is neither a
  feasible maximum nor under a larger maximum another entry can supply:
  - **not a feasible maximum:** `v ∉ D(result)`, or `v` is below the largest
    lower bound `L₋ᵢ` among the other entries;
  - **not under a larger maximum:** `v ≥ E`, where `E` is the largest result
    value `≥ L₋ᵢ` that another entry holds.
- **Fires when** — every call, last. It is the only rule that removes interior
  values from the array.
- **Strength** — completes `GAC` on distinct variables, holes included (0 of
  3,000 per direction at the root; per node in `min_max_test`). It removes
  nothing on interval domains, where rules 1–4 are already GAC.
- **Algorithm** — **per value**: for each position, a walk of the result's
  domain with an `in_domain` scan over the others, then a walk of `x_i`'s
  domain. `Θ(Σ_i |D(x_i)|)`, plus between `n·|D(result)|` and `n²·|D(result)|`
  steps per call, whatever it removes. Written for #413's per-node consistency
  check.
- **Why it is true** — if `x_i = v`, the maximum is at least `v`.
  - **A result value above `v`** would have to be taken by another entry
    (`x_i` cannot take it). The ones at or above `L₋ᵢ` are all above `E`, so no
    other entry holds them; the ones below `L₋ᵢ` are ruled out by that entry's
    lower bound.
  - **So the maximum is `v`.** That needs `v ∈ D(result)` and every other entry
    at most `v`, and one of the two fails.
- **Proof technique** — `RUP sequence`, ours. For each result value `r` beyond
  `v`, the justification writes:
  - `x_i ≠ v ∨ result ≠ r ∨ ¬f_k` for every `k`, by Theorem 2.8: `f_k` equates
    `x_k` with the result, and either the reason excludes `r` from `x_k`, or
    `k = i` and `x_i = v ≠ r`;
  - then `x_i ≠ v ∨ result ≠ r`, against the at-least-one row.

  The conclusion is then RUP, by Theorem 3.2's collapse and the unconditional
  row.
- **Reason** — `generic_reason` over the whole scope, snapshotted before the
  inference, with proofs on only, once per removed value; per run within each
  domain. Not minimal.
- **Assertion** — measured, `max(x, 0) = r` with `x ∈ 0..4` and `r ∈ {0, 4}`:
  ```
  a 1 ~i[x][eq1] 1 ~i[x][ge0] 1 i[x][ge5] 1 ~i[r][ge0] 1 i[r][ge5] 1 i[r][in1_3] >= 1::min_max:((constraint_id _2));
  ```
  The constant entry contributes no literal.
- **Hint** — `hints::MinMax`.
- **Offline reconstructibility** — `offline`. The removed value and the
  result's domain are read off the clause and the reason.
- **Proof size** — **per removed value**, `(n + 1)` lemmas for every result
  value beyond it, plus the conclusion. That is **quadratic in width** on a
  holey result. `max(x, 0) = r`, with `x ∈ 0..W` and `r` over the even values,
  writes 674, 2,544 and 9,884 `rup` lines at `W = 40`, 80 and 160 (`psize.cc`,
  mode `quad`), close to `3W²/8`.
- **Gaps** — **the justification reads `state` after its own inference.** The
  values it walks are the result's current ones, and the tracker applies an
  inference before running its justification. So when `x_i` and the result
  share a variable through a view, the removal has already taken a value off
  the result, its lemma group is missing, and the conclusion is not RUP.
  Both directions: VeriPB rejects 4 of 3,861 random view-aliased `min` proofs
  and none of 3,906 `max` ones at view offsets up to 1, and 1 `max` of 1,939
  at offsets up to 2 ([Robustness](#robustness-and-limits)).
- **Tightness** — `Not shown.`

## Evidence

### Tests

- **`min_max_test`** (`min_max_constraint`, plus
  `min_max_constraint_view_mixed`):
  - **The shapes.** For both directions: 20 fixed shapes (singletons, repeats
    of one range, constants mid-array, the #254 all-constant rows), then 10
    random shapes with a ranged result and 10 with a constant one, each of one
    to five entries, all within `−5..13`.
  - **The check.** Each runs with and without proofs under
    `solve_for_tests_checking_consistency`, checking **GAC** on the result and
    the array at every node. The harness branches with
    `reject_random_interval`, so the per-node check does see holes.
  - **VeriPB** runs when it is on the path. The tests are seeded (`--seed`).
- **Duplicate runs,** bare lane only: `{x, x, y}`, `{x, y, x}`, the result
  equal to an entry, and the result equal to the second of three entries.
  These are plain variables over `1..5` and `1..4`, under `solve_for_tests`,
  so full enumeration and the proof but no consistency check.
- **The empty array** is checked to throw `InvalidProblemDefinitionException`
  in both directions.
- **`scp_reader_test`** counts the solutions of `array_min` and `array_max`.
- **`scp_chain_array_{min,max}_sat` and `scp_chain_array_min_unsat`:** see
  [Cake conformity](#cake-conformity).
- **MiniZinc:** `arrayintminmax.mzn` (`array_int_minimum`/`maximum`, with
  `alldifferent`) and `minmax.mzn` (`int_min`/`int_max`), both optimisation.
- **XCSP3:** `minimum.xml`, `maximum.xml`.
- **Python:** `test_min` and `test_max` in `python_test.py`.
- **Audit lane:** the `ArrayMinMax` row; see [Interval
  efficiency](#interval-efficiency).

**Runtime caps.** No lane sets or clears one, and **the default caps fire**. At
`--seed=1` with `GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500`
(`c9ceea25`):
- **The bare lane** truncates 6 of its 176 runs;
- **`view_mixed`** truncates 6 of 160;
- **which runs:** in each lane, the `min` direction of two fixed shapes and one
  random one (420, 4,224 and 2,592 solutions), each with and without proofs.

Those six are checked for soundness only, against a partial proof. Everything
else runs to completion.

**Tightness:** no mutation lane, and no refusal shown by hand.

**What the tests do not cover.**

- **A result sharing a variable with an entry through a view.** The duplicate
  runs use plain variables and the view lanes wrap distinct ones, so the throw
  and the rejected proofs are invisible to the suite.
- **The consistency of repeated variables,** deliberately. Plain repeats are
  weaker than `bounds(Z)`.
- **Width.** Every tested domain is at most 16 wide, and the audit lane does
  not vary holes, a narrow result or proofs.
- **`Min` and `Max`** as classes: only through MiniZinc's `minmax.mzn`, and as
  two-entry arrays in the fixed and random shapes.
- **Real instances:** none ported.

### Benchmarks and examples

- **In the repository:**
  - `examples/colour` (`ArrayMax` for the number of colours);
  - `examples/talent` (`ArrayMin` and `ArrayMax` of each actor's slots);
  - `examples/p_dispersion` (`ArrayMin` over the pairwise distances, whose
    `tuple` variant's comment notes that the constraint reads the distances'
    interiors, #902).
- **Corpus:** 74 of the 285 flattened MiniZinc Challenge models post this
  family (one instance each; `tmp/fd-small/min_max/scan_corpus.py`).
  - **Posts:** 2,043 `array_int_maximum`, 2,846 `array_int_minimum`, 3,699
    `int_max` and 6,214 `int_min`.
  - **Array lengths:** 2 to 1,490.
  - **Wide domains:** nine models post one over a declared domain wider than
    10⁵. They are `largescheduling` 2015 and 2018, `tower` 2020, 2022 and
    2025, `ATSP` 2021, `atsp` 2025, and `road-cons` 2014 and 2017, with widths
    up to 3.2·10⁷. A tenth, `filters` 2010 (#815's), posts an
    `array_int_maximum` whose result has no declared domain at all.
- **For CPU:** the enumeration below. It reaches rules 1 to 4, and runs rule
  5's pass on every call without it ever removing anything.
- **For proof verification:** the same enumeration at `n = 3`, with `D` from 8
  to 24.
- **Never run uncapped:** `2022_tower`, `2018_largescheduling` and
  `2017_road-cons`. A single call can outlast the time limit
  ([CPU performance](#cpu-performance)).

### CPU performance

*Release build of `c9ceea25` (GCC 15.2.0, `-O3 -march=native`); Gecode 6.3.0,
built locally; fataepyc-10, boost off, pinned with `taskset -c 33`,
`GLIBC_TUNABLES` fixing the malloc thresholds; median of five runs; wall time
of the whole solve, proofs off; 2026-09-30.*

**The benchmark.** Enumerate every solution of `r = max(x₁, …, x_n)`, with
`x_i ∈ 0..D−1` and `r ∈ D/2..D−1`, branching on the `x_i` in input order,
smallest value first (`mm_gcs.cc`, `mm_gecode.cc` in
`tmp/fd-small/min_max/bench/`).

**Identical trees.** Every model here is GAC on these interval domains, so the
searches explore the same assignments in the same order: the same solution
counts, and no failure in any. GCS's `smallest_first` gives a variable one
child per value, where Gecode's `INT_VAL_MIN` branches in two. So the node
counts differ.

**The "pass off" column** is a different binary: `c9ceea25` plus the first
two aliased-view fixes and an environment switch skipping rule 5. The third
fix and the switch are both in `tmp/fd-small/min_max/exp-all.diff` now. None
of the fixes is reached here. Compare it
with the first column for what the pass costs, allowing for layout noise.

| n | D | Solutions | GCS | GCS, pass off | Gecode `IPL_BND` | Gecode `IPL_DOM` |
|---|---|---|---|---|---|---|
| 4 | 16 | 61,440 | 0.312 s | 0.176 s | 0.023 s | 0.026 s |
| 4 | 32 | 983,040 | 5.06 s | 2.89 s | 0.338 s | 0.378 s |
| 3 | 64 | 229,376 | 0.981 s | 0.575 s | 0.073 s | 0.081 s |
| 3 | 128 | 1,835,008 | 7.79 s | 4.61 s | 0.569 s | 0.628 s |

| n | D | GCS recursions | GCS propagations | Gecode nodes | Gecode propagations (`BND`, `DOM`) |
|---|---|---|---|---|---|
| 4 | 16 | 65,809 | 117,352 | 122,879 | 117,050, 160,440 |
| 4 | 32 | 1,016,865 | 1,918,032 | 1,966,079 | 1,877,586, 2,570,140 |
| 3 | 64 | 233,537 | 457,328 | 458,751 | 455,084, 604,705 |
| 3 | 128 | 1,851,521 | 3,664,096 | 3,670,015 | 3,652,460, 4,861,025 |

- **GCS takes 12 to 15 times Gecode's time on an identical tree** (11.1 to
  14.7 in the fact-check's re-run, same node and propagation counts). This is
  a whole-solve comparison on a benchmark with no failures, so it measures the
  search loop and the solution callback as well as the propagator. It is the
  kind of comparison #868 asks for, done by hand with an API-level Gecode
  driver.
- **The pass is 36% to 41% of GCS's time here** (the two GCS columns differ
  by about 1.7 times), although it never removes a value.
- **Without the pass, GCS is still 6.8 to 8.6 times Gecode** (6.6 to 8.7 in
  the re-run). A profile of the pass-off build at `n = 4, D = 32`, as hotspot
  context only:
  - the propagator's own body, 31%;
  - `State::copy_of_values`, 6%;
  - resetting the `Reason` variant, 4%;
  - `malloc` and `free`, about 7%.

  The per-call copies and `std::generator` frames are the obvious suspects:
  the fact-check counts 12.7 heap allocations per propagation with the pass
  off at `n = 4, D = 16`, a smaller size than the profile's (30.7 with it
  on). None of them is from the bound rules' one-literal reasons, which are
  inline. Nothing has been measured on its own.
- **Gecode's two levels do the same here.** `IPL_DOM` leaves the interior
  values rule 5 removes: on the instance in `gecode_dom.cc` it keeps `x0 = 2`
  and `x0 = 3`, which GCS removes. How the two compare in general is under
  [Prior art](#prior-art).
- **What the benchmark does not exercise:** holes (so rule 5 never removes),
  `min`, conflicts, repetition and views.

**Challenge models, 60 s limit (10 s for `yumi-static`).**
- **The set-up:** `fzn-glasgow -s -t 60000` under
  `GCS_PROPAGATOR_STATS=time`, same machine and pinning, one run each.
- **The builds:** "pass off" is the build above.

| Model | Build | Solve time | Nodes | Min/max calls | Time in min/max | Solutions |
|---|---|---|---|---|---|---|
| `2018_largescheduling` | `c9ceea25` | 66.4 s | 7 | 11 | 64.2 s | 0 |
| | pass off | 60.1 s | 226 | 259 | 0.006 s | 3 |
| `2022_tower` | `c9ceea25` | **104.1 s** | 1 | 77 | 104.0 s | 0 |
| | pass off | 59.9 s | 78,979 | 8,927,510 | 37.2 s | 58 |
| `2017_road-cons` | `c9ceea25` | 60.0 s | 1 | 64 | 59.9 s | 0 |
| | pass off | 59.6 s | 2,854 | 18,567,330 | 45.4 s | 14 |
| `2022_yumi-static` (10 s limit) | `c9ceea25` | 10.0 s | 200 | 28,578 | 9.69 s | 1 |
| | pass off | 10.0 s | 3,332 | 1,449,481 | 3.04 s | 1 |

- **Even with the pass off,** this family takes 62% and 76% of the `tower`
  and `road-cons` solves, at 4 µs and 2.4 µs a call.
- **The width need not be large.** `yumi-static`'s row is 12 constraints:
  one `array_int_maximum` over 23 entries and eleven two-entry `int_max`
  (`Max`, which reports under the same name), with declared domains at most
  3,099 wide and no holes. Averaged over the 12, the pass makes a call cost
  339 µs rather than 2.1 µs, and switching it off gives 16.7 times the nodes
  in the same 10 s. The model's two `int_min` posts take 0.13 s between them
  with the pass on, and 0.10 s with it off.

### Proof performance

*Same build and machine. `mm_gcs max 3 D D/2`, the enumeration above over three
entries, all solutions, VeriPB 3.0.2 with `--force-checked-deletion`; one
VeriPB run each.*

| D | Solutions | Lines, `Off` | Bytes, `Off` | VeriPB, `Off` | This family's lines, `Off` | Firings | Lines, `Definitions` | VeriPB, `Definitions` |
|---|---|---|---|---|---|---|---|---|
| 8 | 448 | 7,515 | 384 KB | 0.09 s | 3,488 (46%) | 426 | 4,453 | 0.05 s |
| 16 | 3,584 | 62,463 | 3.88 MB | 1.49 s | 34,860 (56%) | 4,054 | 31,639 | 0.78 s |
| 24 | 12,096 | 215,715 | 14.3 MB | 8.75 s | 126,232 (59%) | 14,466 | 103,897 | 4.64 s |

- **How the family's lines are counted.** They are the `rup` and `del` lines
  that disappear at `Definitions`, where each firing becomes one `a` line.
- **Firings** are the `a` lines carrying the `min_max` hint at `Inferences`.
- **The family is over half the proof,** growing with `D`: 7.3, 7.7 and 7.8
  `rup` lines per firing.
  - **Most firings are rule 3,** at `3n + 1 = 10` lines per run: 279, 2,863 and
    10,439 of them.
  - **Next, the bound rules,** at one line each: 131, 1,127 and 3,883.
  - **The single-support rule's assertions** grow with the result's width,
    from 12 literals at `D = 8` to 20 and 28.

**Assertion levels.** On these probes the results are the usual ones:
- **`Off`:** every proof verifies.
- **`Definitions` and `Inferences`:** VeriPB accepts each proof with
  `s UNDER ASSERTIONS`, not `VERIFIED`. Every one of this family's inferences
  is an `a` line there, so only `Off` checks the family.
- **`Links`:** none is accepted. Each fails at a `solx` step (line 199 at
  `D = 8`, 263 at 16), which is generic, as other families' `Links` runs
  show.
- **The family's share at `Inferences`:** 426 of 1,395 assertions at `D = 8`,
  4,054 of 11,495 at 16, and 14,466 of 39,259 at 24. The rest are the search's
  own.

## Status, gaps, and next steps

### Proof-logging gaps

- **Rules 4 and 5 under a view-aliased result:** each justification reads
  post-inference state, and VeriPB rejects the proof. See the rules.
- **The aliased-view throw** is a failure the propagator does not make. It is
  not a proof gap, since nothing is asserted, but a proof ends there.
- **Otherwise `None.`** The propagator is the same with proofs on or off.

### Known limitations

- **A min or max over wide domains is slow on every call:** one call over
  three entries of width 10⁷ takes over a second. Three challenge models make
  no progress in a minute, and a time limit can be overshot by the length of
  one call: one call on `2022_tower` takes about a minute, overshooting by
  44 s.
- **An `ArrayMin`/`ArrayMax` whose result shares a variable with an entry
  through an offset or negated view** can throw "missing support, bug in
  MinMaxArray propagator" and end the search, even on a satisfiable model. It
  can also write a proof VeriPB rejects.
- **Repeating a plain variable** (`ArrayMin{x, x} = y`) is sound but weaker
  than bounds consistency.
- **XCSP3's indexed, tree-list and `*Arg` forms** of `minimum` and `maximum`
  are unsupported.
- **The single-support rule's proofs** grow with the result's width.

### Next steps

1. **Fix the aliased-view defects.** Three changes, tested together
   (`fix-aliased-views.patch`):
   - **The throw.** Return `Enable` where it throws. The propagator claims no
     idempotence, so its own removals wake it, and the next union pass empties
     the result.
   - **Rule 5's justification.** Capture the result's values beyond `v` before
     `infer_not_equal`.
   - **Rule 4's justification.** Walk the pre-inference `result_set` in
     `rule_out_other_selectors`, not `state`.

   With all three, `satthrow`'s 40,000 random enumerations (about 28,000 of
   them with the result sharing a variable with an entry through a different
   view) give the right counts with no throw, and 8,000 of 8,000 proofs
   verify at view offsets up to 2 and 3 (16,000 of 16,000 in the first
   fact-check's sweep, and 54,000 enumerations in the second's). The rule 5
   snapshot as written is itself per value; take the values from the reason
   instead. Add a duplicate lane to `min_max_test` whose view offsets differ by
   2 or more, with negated views on both sides and varied branching. Small;
   filed as #1165.
2. **Stop the entry pass costing the width on every call.**
   - **Cheapest:** skip it when no variable in scope has a hole, an `O(n)`
     check. It has nothing to remove then.
   - **Proper:** do it by intervals. For `max`, `x_i` keeps
     `(D(result) ∩ [L₋ᵢ, ∞)) ∪ (−∞, E − 1]`, both computable by walking
     intervals, and `each_interval_minus` gives the runs to remove. Each run
     then needs a range form of the lemma group, as rule 3 has.
   - **What it buys:** the three challenge models above, and the audit row
     flipping to `Clean`.
   - **A later option:** offering the pass as optional interior pruning, which
     would have to target the result too.

   Medium; filed as #1166.
3. **Update the audit row's comment**, and add rows with a narrow result, with
   holes, and with proofs. Trivial.
4. **Make the single-support rule's reason and proof per run.** State "no
   other entry meets the result" as each other entry's generic reason, and one
   `¬f_k` per entry by a lemma per run. Small; filed as #1167.
5. **Label the rows as cake does, in cake's order.** That makes the three
   chain cases `strict`. Also correct the CMake comment's stale #358 reason.
   Small.
6. **Measure the per-call overheads:** the domain copies, the `scope` vector,
   the generator frames, and the bound rules' unconditional (though
   non-allocating) reasons. These are candidates for the remaining 6.8 to 8.6
   times against Gecode.
7. **`gcspy`:** guard `post_min`'s logging against an empty list, and make
   `post_max` log a replayable call. Trivial.

## Prior art

Nobody publishes a propagation algorithm for minimum or maximum beyond the
obvious.
- **Gecode 6.3.0** has bounds (`NaryMaxBnd`) and "domain"
  (`NaryMaxDom`) propagators (`gecode/int/arithmetic/max.hpp`); `min` is `max`
  over `MinusView`s.
  - **The domain one** does almost exactly what this family's rules 1 to 4
    do: bounds, the result cut to the union, and the last support made equal.
    Its binary form also equates an entry that dominates the other with the
    result, which rules 1 to 4 do not. Against GCS with the pass off, at the
    root of 3,000 random holey instances per direction, it is equal on 2,997
    (min) and 2,999 (max), and stronger on the rest (`x0 ∈ −3..0`,
    `x1 ∈ 0..4`, `r ∈ {−3, −2, 0, 3}` gives `x1 ∈ {0, 3}` in Gecode and `0..3`
    without the pass). Against full GCS it is never stronger, and weaker on
    164 and 155 (the fact-check's `strength.cc`).
  - **What it lacks** is rule 5's interior pruning of the array. So it is not
    GAC on the array, and GCS's default is stronger than Gecode's strongest
    level.
- **The proof side** is ours: McIlree's thesis has no procedure for minimum or
  maximum. It rests on the thesis's Theorems 2.6, 2.8, 2.9 and 3.2, with shapes
  close to Element's JP 3.9 and 3.10.
- **The range form of rule 3** is this solver's (#815, #904), and
  [`large-domains.md`](../large-domains.md) describes it.

## Further reading

- [`large-domains.md`](../large-domains.md), "Getting a range removal past the
  checker": why a range removal needs the bound lemmas, with `ArrayMinMax` as
  the worked example of a guarded equality.
- [`justification-techniques.md`](../justification-techniques.md): Theorems
  2.6, 2.8, 2.9 and 3.2, and JP 3.2, 3.9 and 3.10.
- [`view-proof-logging.md`](../view-proof-logging.md): why a view's rows are
  over its own encoded variable.
- [`optional-interior-pruning.md`](../optional-interior-pruning.md): the
  mechanism step 2's later option would use.
