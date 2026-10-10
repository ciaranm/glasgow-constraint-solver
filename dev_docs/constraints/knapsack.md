# `Knapsack`: several non-negative weighted sums of one item list, each equal to a total

> **Maturity** production (`proof_strategy::PerCall`, the default);
> production, opt-in (`proof_strategy::Upfront`) ·
> **Audited** 2026-10-10 at `86caad24` ·
> **Open issues** filed by this audit: #1337 (negative item values and
> totals, which MiniZinc allows, give an error from MiniZinc, and negative
> items, weights or profits, which XCSP3 allows, an abort from XCSP3), #1340
> (the interior-value pass walks every value of each total and scans every
> terminal state for it: quadratic in a wide item), #1334 (`PerCall` drops
> coefficients past the end of the item list without a word), #1341 (the
> MiniZinc Challenge's `multi-knapsack` models spend 43 to 125 s and up to 25 GB
> in the root call with proofs off, and write more than 40 GB of proof with them
> on). Already open and touching this family, commented on by this audit:
> #1229 (a view or constant total throws `UnimplementedException` with proofs
> on at `AssertionLevel::Off`, which this audit finds reachable from MiniZinc;
> both corpus models pass a constant total that it covers, though neither has
> been seen to reach it), #1070 (every proof line restates the 0/1 items'
> always-true bounds; the corpus does post Knapsack). Also open: #497
> (hint the dead-state RUPs), #200 (one generic layered-DAG propagator
> framework for the diagram constraints), #833 (the large-domain policy), #868
> (cross-solver comparisons; this document gives one, by hand). Tracked under
> #871.

`Knapsack(coefficients, vars, totals)` enforces `Σ_i coefficients[x][i] ·
vars[i] = totals[x]` for every row `x`, over non-negative coefficients and
non-negative items and totals; `Knapsack(weights, profits, vars, weight,
profit)` is its two-row case, which is what MiniZinc's `knapsack` and XCSP3's
`<knapsack>` post. The model is just those `k` linear equalities. The
propagation is Trick's dynamic programme, generalised to `k` rows and to
non-0/1 items, run from scratch on every call: a forward pass over layered
partial-sum states, a filter of the last layer by the totals' domains, and a
backward pass. Two proof strategies certify the same inferences against the
same OPB. `proof_strategy::PerCall` (the default) re-derives the diagram as
proof flags on every call, at `ProofLevel::Temporary`, which is the method of
Demirović et al. (CP 2024, §3.3) and McIlree's thesis (§5.2.2).
`proof_strategy::Upfront` builds the diagram once from the initial domains and
writes it, with backward chains and "phantom" states, at `ProofLevel::Top`,
leaving each call its dead-state lemmas and its cap-exceeded, terminal-filter
and bound lines, which are most of the proof's bytes on two of the four bench
instances (see [Proof performance](#proof-performance)). `dev_docs/knapsack.md`
stays as the long design note for `Upfront`.

Four things to know before touching it.

- **It is generalised arc consistent on items and totals, on distinct
  variables, under both strategies**, holes included: 4,000 random instances,
  brute-forced at the root under each strategy, found no failure, and both
  strategies give identical root domains and equal node and solution counts
  (800 seeded random enumerations). A repeated variable loses GAC but never a
  solution.
- **Its cost is pseudo-polynomial and is paid on every call.** The state count
  of a layer is bounded only by the product, over rows, of the reachable
  partial-sum range. The two MiniZinc Challenge models that post it
  (`multi-knapsack` 2015 and 2019: five constraints over 50 or 39 0/1 items,
  each pairing a weight of at most 800 with a profit fixed at the instance's
  optimum, above 10,000) spend 125 s and 43 s in the root with proofs off, at a
  peak of 25 GB and 8.7 GB, and with proofs on wrote 41 GB and 48 GB of proof
  before being killed (#1341). Gecode, by the linear decomposition, proves the
  2019 instance optimal in 0.86 s. Within one call, the totals' interior-value
  pass costs the width of the total times the number of terminal states
  (#1340), and a capacity declared near the top of the range makes even a
  one-item model unusable.
- **The two strategies trade proof size against checking time, and neither
  dominates.** On `knapsack_bench`'s four instances `Upfront`'s proofs are 3.0
  to 5.9 times smaller in bytes and are written 2.0 to 3.3 times faster, but take 1.10 to
  5.9 times longer for VeriPB to check (timed solo), because its permanent
  scaffold makes every line dearer (41 to 77 µs a line against 13 to 17). With
  proofs off `Upfront` is the slower of the two (1.14 to 1.38 times the
  instructions); it walks fixed items too and tests every edge against the
  static diagram, and which of the two costs more was not measured.
- **Negative values are refused, not handled.** A negative coefficient, item
  lower bound or total lower bound throws `InvalidProblemDefinitionException`
  from `prepare()`. MiniZinc's own definition requires non-negative weights and
  profits (its wrapper asserts it, so every solver errors on them) but
  *constrains* items and totals to be non-negative, so a model with `var -1..2`
  items or a total declared `var -3..20` errors where Gecode solves it; XCSP3
  has no sign restriction on items, weights or profits, and the throw escapes
  the XCSP3 binary as an abort (#1337). With proofs on at `AssertionLevel::Off` (which
  is what `--prove` gives), a total that is a constant or a view throws
  `UnimplementedException` (#1229) as soon as a cap-exceeded or lower-bound
  `pol` names it; MiniZinc reaches that with a fixed capacity, and both corpus
  models pass a constant total, which would reach it if their root call got far
  enough (none has been seen to). Above `Off` it does not throw.

## What it is

### Semantics

`Knapsack(coefficients, vars, totals)`, with `k = |totals|` rows and `n =
|vars|` items, holds when, for every `x` in `0..k−1`,

```
Σ_{i < n} coefficients[x][i] · vars[i] = totals[x].
```

The class requires, and checks in `prepare()` (`knapsack.cc:601–623`, and
`knapsack_upfront.cc:858–885` for `Upfront`), that `k ≥ 1`, that every row has
the same length, that every coefficient is non-negative, and that every item and
every total has a non-negative initial lower bound. Each failure throws
`InvalidProblemDefinitionException`. The constructor checks only that every
coefficient lies in `±(2⁶⁰ − 1)` (`innards::require_bounded`,
`knapsack.cc:64`, `:70`), and throws `IntegerOverflow` otherwise. The
two-total constructor is `Knapsack({weights, profits}, vars, {weight,
profit})`.

- **Row length against `n`.** `Upfront` requires each row to have exactly `n`
  entries (`knapsack_upfront.cc:870–871`). `PerCall` does not check: a longer
  row's extra coefficients are silently ignored, and a shorter row throws
  `std::out_of_range` from an `.at()` read that nothing catches
  (`knapsack.cc:638`, in `define_proof_model`, with proofs on; `:140`, in the
  propagator, with proofs off)
  (`robust/rowlen.cc`: `{{1, 2, 4}}` over two items enumerates the four
  assignments of `x₀ + 2x₁`). The `.scp` reader passes rows through unchecked,
  so a malformed `.scp` reaches this; `cake_pb_cp` refuses the same file with
  `@BAD_INPUT` (#1334). `Upfront`'s check is skipped in one corner: with
  proofs off and partial sums that do not fit, `prepare()` falls back to the
  `PerCall` path (`knapsack.cc:595–599`) before it runs.
- **No items** (`n = 0`, rows of length 0): every total must be `0`. Tested
  (#254).
- **One item, all items fixed, all items at 0:** tested.
- **Zero coefficients** are ordinary; a zero row term is left out of the OPB.
- **Items are integers, not 0/1:** `vars[i] = v` takes `v` copies of item `i`.
- **A repeated variable** (an item twice, an item that is also a total, two
  totals that are one variable) is accepted and means what the equalities say.
  The propagator treats each position as independent; see [Robustness and
  limits](#robustness-and-limits).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Knapsack`, `proof_strategy::PerCall` | ✓ `fzn_knapsack`[^mzn] | ✓ `knapsack`[^xcsp] | ?[^cpmpy] | ✓ `knapsack` | `k` rows from C++ and the `.scp` reader; MiniZinc and XCSP3 post two |
| `Knapsack`, `proof_strategy::Upfront` | — | — | — | written as `knapsack`[^sexpr] | C++ only; `knapsack_bench --upfront` |
| `knapsack_reif` | `decompose`[^reif] | n/a | — | — | |

[^mzn]: `minizinc/mznlib/fzn_knapsack.mzn` redefines `fzn_knapsack(w, p, x, W,
    P)` as `glasgow_knapsack`, and `fzn_glasgow.cc:1089–1096` posts
    `Knapsack{w, p, x, W, P}`. The standard library's `knapsack` wrapper asserts
    equal index sets and non-negative weights and profits, and maps the arrays
    through `index2int`, so no index set reaches the solver. Its own
    `fzn_knapsack`, which the redefinition replaces, also posts `x[i] ≥ 0`,
    `W ≥ 0` and `P ≥ 0` as constraints; the redefinition drops them, and
    `Knapsack` throws on a negative lower bound instead (#1337). A fixed `W`
    or `P` arrives as an integer literal, which `arg_as_var` makes a constant,
    which #1229 crashes with proofs on at `AssertionLevel::Off`. `knapsacktest.mzn` is the one test.
[^xcsp]: `buildConstraintKnapsack` (`xcsp_glasgow_constraint_solver.cc:820–845`)
    creates an auxiliary total per condition, posts the two-row `Knapsack`, and
    posts each `<condition>` on its auxiliary (`le`, `lt`, `eq`, `ge`, `gt`,
    `ne`, an interval, or a variable operand; a set is reported unsupported).
    The parser reads the weight condition from the first `<condition>` and the
    profit condition from the second, so the element order is `<list>`,
    `<weights>`, `<condition>`, `<profits>`, `<condition>`; it ignores a
    `<limit>`. A negative weight, profit or item value throws from
    `Knapsack::prepare()`, inside `solve_with`, where the binary catches only
    `IntegerOverflow`, so the process aborts (exit 134; #1337). Inside a
    `<group>`, the vendored parser tags a knapsack template as `FLOW`
    (`XMLParserTags.cc:1287`), which was not followed further.
[^cpmpy]: `gcspy` binds nothing in this family. CPMpy's upstream GCS
    interface, as copied on 2026-09-23 (`tmp/linear-audit/cpmpy_gcs.py:670`),
    decomposes every global it does not map and names Knapsack as future work.
[^sexpr]: `constraint_type()` is `"knapsack"` whatever the strategy, so an
    `Upfront` constraint's `.scp` reads back as `PerCall`; the strategy is not
    part of the model. `dev_docs/knapsack.md` still says the keyword is
    `knapsack_upfront`.
[^reif]: Glasgow's `mznlib` has no `fzn_knapsack_reif`, so the standard
    library's reified decomposition into linear equalities is used.

**Differential checks, all against `86caad24`.** The cake chain starts at the
`.scp`, so it cannot see a front end's mistranslation; each route was diffed
directly, classifying the status markers (`==========`,
`=====UNSATISFIABLE=====`, `=====ERROR=====`, no marker) and agreeing only on
status and solution set together.

- **MiniZinc**, 300 random models on each of 2.9.7 and 2.10.1, against Gecode
  and Chuffed (`tmp/fd-dd/knapsack/fe/mzndiff.py`, seed 7): index sets starting
  at 1, 0, 3 and −2, sizes 0 to 4, holey item domains, a fixed `W`, a fixed
  `P`, a fixed item, an item repeated, `W` also an item, and `W` and `P` one
  variable. Both versions give the same counts: 197 agree (170 complete
  enumerations, 27 unsatisfiable); the 67 with no items error in all three
  solvers (the standard wrapper's `lb_array` of an empty array); the 36 that
  disagree are exactly the models with a negative item or total lower bound,
  where Glasgow errors and the others solve.
- **XCSP3**, 200 random instances against ACE 2.6 (`fe/xcspdiff.py`, seed 3):
  every one of the 96 comparable instances without a negative value or weight
  agrees. ACE itself fails on 45 instances (an `ArrayIndexOutOfBoundsException`
  in its `Problem.sum`), which are not counted. The 56 disagreements are all
  aborts on a negative weight (32) or a negative domain value (24); a negative
  profit aborts the same way, since `prepare()`'s coefficient check covers
  every row (`knapsack.cc:612–615`).
- **`.scp`:** `knapsack_sat` and `knapsack_unsat` chain-verify; see [Cake
  conformity](#cake-conformity).

### Options

**`with_proof_strategy(KnapsackProofStrategy)`**, where `KnapsackProofStrategy
= std::variant<proof_strategy::PerCall, proof_strategy::Upfront>`
(`knapsack.hh:30`). Default `PerCall`.

- **It changes the proof, not the model and not the inferences.** Both
  strategies write the same `define_proof_model` rows and draw the same
  inferences. The 800 seeded random enumerations in [Tests](#tests) found
  identical solution counts and node counts, and the root brute force
  identical domains at every seed. The proofs differ entirely at `Off`
  (`Upfront`'s `Top` scaffold and `kp*` flags, and line counts 0.36 to 1.16
  times `PerCall`'s on the bench), every assertion carries a different hint name
  (`knapsack_upfront`), and some assertion clauses differ: `PerCall` has two
  rules of its own (1 and 2) that fix or bound a total by plain RUP, where
  `Upfront` reaches the same bound through the diagram.
- **Why `PerCall` is the default:** VeriPB checks its proofs faster
  ([Proof performance](#proof-performance)), as
  [`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md)
  records and explains by the permanent scaffold's cost per line.
- **`Upfront` without a proof** builds its static diagram anyway and uses it
  only as a membership filter. When the diagram's partial sums do not fit in an
  `Integer` (nine 0/1 items of weight `max_bounded_value()` suffice; eight
  fit) and no proof
  is being written, `prepare()` falls back to `PerCall`
  (`knapsack.cc:595–599`, `knapsack_upfront_partial_sums_fit`), since a proof
  strategy must not change the answer; with a proof it throws
  `IntegerOverflow`, as `knapsack_upfront_test` pins.

There is no `with_consistency()`: both strategies are GAC, and there is no
weaker arm.

### Variable kinds and views

Items may be plain variables, constants, or views of either sign: the
propagator reads domains through `State`, and the proof's partial-sum
reifications and row cancellations are written over each view's own terms. 400
random enumerations per strategy with items drawn from plain, `x + c`, `−x + c`
and constants all verify ([Tests](#tests)).

Totals may be any kind with proofs off, and at every assertion level above
`Off`. **With proofs on at `AssertionLevel::Off`, the default and what
`--prove` gives, a constant or a view total throws `UnimplementedException`**
the first time a cap-exceeded or lower-bound `pol` names its bound
(`add_bound_p_term_to`, `knapsack.cc:95–105`; `add_bound_p_term`,
`knapsack_upfront.cc:513–522`; both are reached only from the `Off` paths).
That is #1229, filed 2026-10-03, which says "with proofs on" without the level.
This audit adds that MiniZinc reaches it whenever a capacity or a profit is a
parameter and some such `pol` fires, which is nearly always (not, for example,
for all-zero weights and `W = 0`): `knapsack(w, p, x, 6, P)` with `--prove`
ends in `=====ERROR=====` at `knapsack.cc:101` (`fe/prove/wpar.mzn`), and with
`GCS_ASSERTION_LEVEL=inferences` the same run is `UNDER ASSERTIONS` with its
one solution. Both corpus models pass a fixed profit. The fact-check's sweep
with constant and view totals found 24 of 300 `PerCall` and 35 of 300 `Upfront`
runs throwing at `Off`, and none of 600 at `Inferences`.

### Reification

None. MiniZinc's `knapsack_reif` decomposes (footnote above). A reified form is
not wanted until a model needs one.

### Relation to other families

- **Decomposes into it:** nothing in the solver. MiniZinc's `knapsack` and
  XCSP3's `<knapsack>` map onto it.
- **Child constraints:** none. XCSP3's binding posts comparison constraints on
  the auxiliary totals it creates; they are not children.
- **Shares code:** nothing exported. `BinPacking`'s per-bin upfront diagram is
  a `k = 1` copy of `Upfront`'s, adapted rather than called (its comments say
  "mirrors Knapsack"); see [`bin-packing.md`](../bin-packing.md). By reading
  only, for the `bin_packing` audit: that copy has this family's interior-value
  pass shape (`bin_packing.cc:778–781` walks every value of a load and scans
  the terminal states for those inside its bounds, as in #1340) and its
  stranded temporary level on failure (`bin_packing.cc:762–764` calls
  `contradiction()` before `forget_proof_level`). The
  `proof_strategy` tags are shared with `Regular` and `BinPacking`.
  `subset_sum_strengthening` is **not** this family's: nothing here calls it.
  Its callers are `cumulative.cc:3113` (`derive_subset_sum_strengthening`) and
  the `cumulative_strengthening` presolver (`cumulative_strengthening.cc:302`,
  `:462`); `lifted_cover_cut` has a layered DP of its own and does not call it.
  Its note says only that its layered derivation has "the shape" of the
  upfront diagram. `TEMPLATE.md`'s family list (the `linear` row) and
  [`linear.md`](linear.md)'s Further reading say knapsack uses it; both are
  wrong about knapsack.
- **Presolvers:** none reads or writes a `Knapsack`.
- **Relation to `mdd` and `regular`:** the same forward, filter and backward
  passes over a layered graph, and the same proof shape (state flags,
  transitions, at-least-one per layer, dead-state lemmas). Here the graph is
  synthesised from the rows, so its flags are proof-only, where `MDD`'s and
  `Regular`'s are part of the model. No code is shared.
  [`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md)
  compares the strategies across the four families it covers (with
  `BinPacking`).

## The proof model

### OPB encoding

For each row `x`:

```
Σ_i coefficients[x][i] · BinEnc(vars[i]) − BinEnc(totals[x]) ≥ 0     @c[id][<x>_ge]
Σ_i coefficients[x][i] · BinEnc(vars[i]) − BinEnc(totals[x]) ≤ 0     @c[id][<x>_le]
```

written by `model.add_labelled_constraint(…, sum == totals[x])`
(`knapsack.cc:644–646`; `knapsack_upfront.cc:933–934`, identical). It is
**definitional**: nothing but the equalities. Neither strategy adds anything to
the OPB; every flag lives in the proof.

**Size: `2k` rows**, with, per row, one term per bit of every item with a
non-zero coefficient plus one per bit of the total, so `Σ_{i: c_xi ≠ 0}
bits(vars[i]) + bits(totals[x])` terms, where `bits(v) = ⌈log₂(ub(v) + 1)⌉`
for the non-negative domains the class accepts. Logarithmic in every width,
linear in `n` and `k`, independent of the coefficients' magnitudes except
through the coefficients themselves. Measured (`size/grid.txt`, terms summed
over the rows): 2 rows and 16 terms for four 0/1 items and one row; 4 rows and
82 terms for eight items in `0..2` and two rows; 2 rows of **no** terms for `n = 0` with the total fixed at
0 (the row is `0 ≥ 0`).

### Labels

`@c[<id>][<x>_le]` and `@c[<id>][<x>_ge]` are load-bearing: both strategies keep
the two `ProofLine`s and cite them in the cap-exceeded, lower-bound,
interior-value and terminal `pol`s (rules 3 to 6). The labels are cake's, by
#440 and #465. No other line is labelled.

### Cake conformity

Two chain cases, `knapsack_sat` and `knapsack_unsat`, both `none`
(`verified_encodings/scp_cases/CMakeLists.txt:647–648`); both pass the full
workflow-2 chain at `86caad24` (`tmp/fd-dd/knapsack/chain/`). The family's four
rows are label for label and term for term the rows cake writes (in a different
term order); `opbdiff --match-labels` differs only on the shared 0/1 variable
bound rows, which cake writes and the solver omits, and that is why the cases
stay `none`. Both cases run `PerCall`, since the reader posts the default.
`Upfront` has no chain case; its proofs chain-verify by hand on three
instances (two rows over three items, and the `holes` and `backward` shapes of
the catalogue; `chain/up_*`).

Two comments in that `CMakeLists.txt` are stale: line 587 says knapsack "does
not chain", and lines 640–646 describe the labels as `@c[_1<row>][le]`, which
neither the solver nor cake writes.

### Proof-time state

- **`PerCall`, at the root:** nothing. **During search**, each call writes its
  whole diagram at `ProofLevel::Temporary` and forgets it at the end of the
  call (`knapsack.cc:561–576`): per layer, per row and per distinct partial-sum
  value, two flags `s<L>x<x>ge<w>` and `s<L>x<x>le<w>`, reifying that the sum
  of the first `L + 1` **unfixed** items is at least or at most `w`; per state,
  one flag `s<L>x_<w₀>_<w₁>…`, reifying the conjunction of its `2k` coordinate
  flags; then transitions, must-pick lines and layer at-least-ones, each a RUP
  under the reason. Layer numbers count unfixed items only, so the same name
  means a different prefix at another node; the tracker's `f[<id>]` keeps the
  flags apart. Nothing a later step needs is deleted.
- **`Upfront`, at the root** (the initialiser, `knapsack_upfront.cc:964–968`,
  only at `AssertionLevel::Off`): for every state of the static diagram and
  every phantom, flags `kpup_<i>_<x>_<w>`, `kpdn_<i>_<x>_<w>` (shared by the
  states of layer `i` with coordinate `w`) and `kpat_<i>_<w…>` or
  `kphantom_<i>_<w…>`, all at `ProofLevel::Top`, over the sum of the first `i`
  items, fixed or not; then forward chains, the layer-0 unit, per-state
  implications, layer at-least-ones, backward chains and the phantom rules
  ([`knapsack.md`](../knapsack.md), "Top-level scaffolding"). **During
  search**, each call writes `¬kpat` lemmas for states it finds dead, and
  `¬kpdn` lemmas for last-layer coordinates below a total's lower bound
  (`DeadCache::dead_g_dn`, `knapsack_upfront.cc:702–706`), at
  `ProofLevel::Current`, recorded in the backtrackable `DeadCache` so that a
  subtree writes each at most once, plus its `pol`s and terminal lines at
  `ProofLevel::Temporary`. The cache and the `Current` lines are undone by the
  same backtrack.
- **Naming:** the flag names above, which encode layer, row and value, are how
  an external tool finds the scaffolding.
- **In the OPB versus the proof:** every auxiliary is a proof-only flag
  introduced by `redundance`, and each is a reification of a partial sum of the
  items, so on a solution unit propagation determines every one.
- **Dangling proof-only vectors:** none. `_eqns_lines` (`PerCall`) and
  `opb_lines` (`Upfront`) are filled by `define_proof_model`, which runs at
  every assertion level, and read only on the `AssertionLevel::Off` paths;
  `Upfront`'s flag tables are empty without a proof, and the `emitting` guard
  keeps them unread.
- **A failure strands the call's temporary lines.** Both strategies take
  `t = temporary_proof_level()` on entry and call `forget_proof_level(t)` on
  the way out, but an `infer` that fails, or `contradiction()`, unwinds past
  the forget (`knapsack.cc:441`, `:575–576`; `knapsack_upfront.cc:753–755`,
  `:832–833`). Not unsound: the lines are swept by the next forget of that
  level. It breaks the rule `inference_tracker.hh:700–715` states, that the
  code which opens a temporary level closes it, and leaves a failing call's
  diagram live until then, which costs checking time (by code reading; not
  measured; [Next steps](#next-steps)).

## The implementation

### Initialisation and global data

**`PerCall`:** `prepare()` validates and returns; no initialiser, no state.

**`Upfront`:** `knapsack_upfront_prepare()` validates, computes per-row caps as
the sum of every item's largest contribution (`compute_caps`, through
`WideSum::narrow_or_throw`), and builds the static diagram by forward
reachability from the zero vector over the **initial** item domains, capped but
not intersected with the totals' initial bounds (`build_static_dag`,
`knapsack_upfront.cc:139–167`). That costs `Σ_i |DAG[i]| · |dom(vars[i])|`
steps of `k` additions and a `std::set` insertion each, and the diagram is held
for the whole search, with or without a proof. The not-intersected choice is
deliberate: the per-call cap-exceeded `pol` needs a flag for the over-bound
state. With a proof, the initialiser writes the scaffold; its size is in
[Proof performance](#proof-performance), and on the bench instances it is 11,116
to 32,670 `red` lines.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| `PerCall` DP | `on_change`, every item and total | derived: **every item and total** | 1–7 | `proof_strategy::PerCall` (default), or `Upfront` without a proof when the partial sums do not fit | not claimed | never |
| `Upfront` scaffold initialiser | — | — | none (scaffolding) | `proof_strategy::Upfront`, `AssertionLevel::Off` | n/a | n/a |
| `Upfront` DP | `on_change`, every item and total | derived: **every item and total** | 3–7 | `proof_strategy::Upfront` | not claimed | never |

**The `on_change` triggers tell the truth.** The forward pass enumerates every
value of every unfixed item (`each_value_mutable`), so a hole in an item can
remove an edge, and the last layer is filtered by `in_domain` on each total, so
a hole in a total can remove a terminal state.

**Idempotence.** Neither propagator claims it, and both return
`PropagatorState::Enable`. On distinct variables one call reaches GAC against
the domains it started from, which would make a second call change nothing;
the evidence is consistent with that (bench instance 1: 1,783 calls over 907
nodes, 876 of them effectful). The claim is not made and has not been checked
with the idempotence checker (#1056); with a repeated variable it would be
false. See [Next steps](#next-steps).

### Mutable state and incrementality

**`PerCall`: none.** Every call rebuilds the diagram over the unfixed items,
with the fixed items' contribution folded into `committed`, in
`std::list<std::map<std::vector<Integer>, …>>`. Nothing is maintained between
calls: neither the layers, nor the terminal set, nor the supports. In the
profile of the 18-item enumeration below, the propagator's own code is 16% of
the cycles and `malloc` and `free` together about a third (`perf record` on
`perf/gecode/b1`, hotspot context only), from building that map of vectors
afresh on every call.

**`Upfront`:** the static diagram and the flag tables (built once, immutable),
and `DeadCache`, backtrackable through `add_constraint_state`. The cache only
saves proof lines; the walk is still a full rebuild per call, over **every**
item, fixed or not, and each edge is tested against the static diagram's
`std::set`; together these are why `Upfront` runs 14 to 38% more instructions
than `PerCall` with proofs off (the split between them was not measured).

An incremental version, restoring the layered graph on backtrack as the
`Regular` propagator of McIlree's thesis does (§5.3), would save the rebuild;
the proof could stay as it is, since neither derivation depends on how the
graph was found. #364, the survey of restore-on-backtrack state, lists
knapsack.

### Interior values and optional pruning

**Offers.** `None.` Both strategies are GAC, with no weaker arm.

**Observes.** **Holes in every item and every total**, as the inventory says.
A `Knapsack` over a variable is therefore a reason for another family's
optional interior pruning on that variable to stay on, and correctly so. The
triggers have been `on_change` throughout this family's history; the hole-wake
work of #966 did not touch it.

### Robustness and limits

**Unbounded domains.** The work is pseudo-polynomial: a layer's states are
bounded by `Π_x (reachable range of row x's partial sum + 1)`, the reachable
range at layer `L` being at most `min(ub(totals[x]) − committed_x, Σ_{i ≤ L}
c_xi · ub(vars[i]))`, the sum running over the items up to and including that
layer's. A wide item or a wide reachable sum is a wide layer. A wide total
whose reachable range is small costs only the per-value pass in [Interval
efficiency](#interval-efficiency), but that pass is per value of the declared
domain: one 0/1 item against a total in `0..2⁶⁰ − 1` never finished its root
call in 120 s with proofs off, under either strategy, where a total in `0..10⁹`
takes 15 to 16 s (the fact-check's `edge.cc`, cases 8 and 9).

**Negative values and zero.** Zero is ordinary everywhere (a zero coefficient,
an item or total at 0, `n = 0`). Negatives are refused in `prepare()`: a
negative coefficient, item lower bound or total lower bound throws
`InvalidProblemDefinitionException`. The DP's over-cap prune relies on every
contribution being non-negative, so the refusal is what keeps it sound; the
front ends' problem is that they pass such shapes through (#1337).

**Degenerate shapes.**

- *Empty item list, single item, all-fixed items:* tested (#254), both
  strategies.
- ***A repeated variable loses GAC, never a solution.*** The DP treats each
  position as a separate variable. Root brute force with repeats (an item
  twice, a total that is an item or another total; `gac/kcheck.cc`, `alias`
  mode): no unsound root in 4,000 instances per strategy, and GAC failures in
  231 of 2,000 at seed 1 and 253 at seed 2 (on items 289 and 314 values, on
  totals 1,320 and 1,490, on a variable that is both 4 and 11), the same counts
  under both strategies. The smallest: `4x = t` written as `[2, 2]` over `[x,
  x]`, with `x ∈ {1, 2}` and `t ∈ 5..12`, leaves `x ∈ {1, 2}` and `t ∈ {6, 8}`;
  only `x = 2, t = 8` is a solution.
- *Constant or view items:* fine, with and without proofs. *Constant or view
  totals:* fine without proofs and above `AssertionLevel::Off`,
  `UnimplementedException` at `Off` (#1229).
- *A row of the wrong length:* `PerCall` ignores the extra coefficients or
  throws `std::out_of_range`; `Upfront` throws
  `InvalidProblemDefinitionException` (#1334).

**Overflow.** The coefficients are checked against `±(2⁶⁰ − 1)` at
construction. Every DP sum and product goes through `Integer`'s checked
arithmetic, so it throws `IntegerOverflow` rather than wrapping, which the
integer-range policy on main ([`integer-ranges.md`](../integer-ranges.md), at
`86caad24`) allows an arithmetic constraint "when a value it genuinely needs
does not fit". The product `value · coefficient` is formed before the
over-cap test, so an item value whose contribution cannot fit throws even when
the state would be pruned: `x ∈ {0, 2⁴⁰}` with coefficient `2³⁰` and a total in
`0..10` throws `Integer overflow: 1099511627776 * 1073741824` with proofs off,
though `x = 0` is the answer (`robust/ovf.cc`). Without a proof `Upfront` falls
back to `PerCall` here, so that is the per-call DP either way. With a proof,
`PerCall` stops writing the model (the OPB row cannot be written), and
`Upfront` throws the same product overflow earlier, in `compute_caps`
(`knapsack_upfront.cc:119`). `Upfront`'s caps go through `WideSum`, and its
fallback is described under [Options](#options).

### Interval efficiency

**Not fine at width.** This is a dynamic programme over values and partial sums,
so per-value work is its nature; what matters is which loops are per value of
which domain, and whether a declared width with no reachable sum behind it
costs anything.

1. **The propagation side.**
   - *Forward pass, per state of the previous layer, per value of the item*
     (`each_value_mutable`, `knapsack.cc:168`, `knapsack_upfront.cc:594`): the
     DP's edges. A genuine per-value support scan, with no interval structure
     to exploit; its cost is the item's width times the layer's states.
   - *Unsupported-value scans, per value of the item* (`knapsack.cc:358`,
     `:520`; `knapsack_upfront.cc:676`, `:826`): one pass each, bounded by the
     forward pass.
   - *The interior-value pass, per value of each total, with a scan of the
     terminal states for each value inside the new bounds* (`knapsack.cc:458–463`,
     `knapsack_upfront.cc:772–775`): it walks every value of `totals[x]`'s
     domain and runs `none_of` over every terminal state for those in
     `[lo, hi]` (`PerCall`) or `(lo, hi]` (`Upfront`, whose test is `v > lo`), so `|dom(totals[x])| + |dom(totals[x]) ∩ [lo, hi]| ·
     |terminal|` per row. The first term is the width of the **declared** total
     at the root, before the call's own bounds narrow it (one-off per call:
     0.30 s at a width of 10⁷ for three 0/1 items, linear in the width, under
     both strategies; `size/kwide.cc`); at a capacity of `2⁶⁰ − 1` the root
     call does not finish. The second is quadratic when the terminal states are
     as many as the total's values: one
     item in `0..W` against a total in `0..W` takes 4.1 s at `W = 10⁴` under
     `PerCall` and 5.9 s under `Upfront`, and did not finish in 300 s at `10⁵`.
     With the total fixed instead, the same item is linear (1.05 s and 1.75 s
     at `W = 10⁶`). Collecting each row's reachable values once and walking the
     domain by intervals would make it one step per terminal state (#1340).
   - *`Upfront`'s static diagram,* per value of each **initial** item domain,
     once, in `prepare()`.
   Nothing here uses an interval primitive.
2. **The reason side.** Rules 3 to 7 use `generic_reason` over every item and
   total: each variable's bounds, or its value if fixed, plus one
   `not_in_range` per hole, so **one literal per run**, and found by walking
   intervals. Rule 1's reason is the items' values; rule 2's is the generic
   reason over the items. `Upfront` passes the reason lazily to the tracker.
   **`PerCall` materialises it eagerly** (`eager_reason` at 28 sites: 27 of the
   `generic_reason(reason_variables)` call #1070 counts, and rule 2's at
   `knapsack.cc:555`), and
   not only for proof lines: rule 2 builds it `k` times on every call, and
   every pruning builds it again, with proofs off (3.1% of the 18-item
   enumeration's cycles, in `materialise_generic`). It also always names the
   0/1 items' always-true bounds (#1070).
3. **The proof side.** Every line is per state or per edge: a flag per
   partial-sum value, a transition per edge, a must-pick per state, a dead
   lemma per state. So the proof is as wide as the diagram, which is as wide
   as the items and the reachable sums, and every RUP line carries the whole
   reason. There is no width gate, and no interval form to gate to: the
   per-value ban does not extend to what a proof emits, and here the proof
   follows the algorithm.
4. **The audit lane.** One row, `Knapsack`, pinned `KnownTrip`
   (`large_domain_audit_test.cc:783–787`): three 0/1 items and two totals in
   `0..10⁹`, `PerCall`, proofs off. What trips is the interior-value pass
   above. It does not vary the strategy, a wide item, a holey total, or proofs,
   and the family has no row in `"Large domain proof sizes"`. A wide item is the
   costlier hazard and is unprobed.

## Inference catalogue

Seven rules. Rules 1 and 2 are `PerCall`'s alone; rules 3 to 7 are the DP's,
under both strategies. Every rule is an `infer` or `infer_all` with
`JustifyUsingRUP`, or `contradiction()` for rule 4: the conclusion is a RUP
under the reason, after whatever scaffolding the strategy has written. With
proofs on but at an assertion level, `PerCall` runs the DP without proof lines
(`knapsack_gac<false>`) and `Upfront` skips its initialiser, so an assertion
carries nothing but its clause and hint.

Five facts hold for rules 3 to 7.

**The procedure is published.** Trick's algorithm, certified by the method of
Demirović, McCreesh, McIlree, Nordström, Oertel and Sidorov (*Pseudo-Boolean
Reasoning About States and Transitions to Certify Dynamic Programming and
Decision Diagram Algorithms*, CP 2024, LIPIcs 307, 9:1–9:21,
doi:10.4230/LIPIcs.CP.2024.9, §3.3) and
McIlree's thesis (§5.2.2, Encoding Procedure 5.3 and Example 5.2): define
partial-sum flags and state flags by `redundance` (Theorem 2.4); derive each
transition `¬S_parent ∨ vars[i] ≠ v ∨ S_succ` from two reification halves by a
`pol` whose partial sums cancel exactly, then by RUP; derive each layer's
at-least-one by RUP from the previous one and the per-state must-pick lines;
kill dead states by RUP; and close each conclusion by RUP. The preconditions
are that every partial-sum flag ranges over the same item order on both sides
of a transition (so the sums cancel), and that every coefficient and item value
is non-negative (so a sum over the cap cannot come back down).

**What the two strategies write per call.**

| | `PerCall` (`knapsack_gac<true>`) | `Upfront` (`propagate`, `emitting`) |
|---|---|---|
| state and coordinate flags | per call, `Temporary` | once, `Top` |
| transitions | per call, per edge: per row two `pol`s and four RUPs, plus one joint RUP | once, per edge of the static diagram |
| layer at-least-ones | per call, with per-state must-pick lines | once |
| over-cap edge | `pol` (coordinate flag, the `_le` row, the total's bound) then two RUPs | `pol` then a `Current` `¬S` lemma, once per subtree |
| dead state | `Temporary` `¬S` RUP | `Current` `¬S` RUP through the `Top` backward chains, once per subtree |
| terminal bound lines | per terminal per row: two `pol`s, two RUPs; then two RUPs | the same |

**The reason** is `generic_reason` over every item and every total. It is
enough and not minimal: an item prune does not need the bounds of items in
other layers to be stated, only their domains to be what they are, and a 0/1
item's bounds are always true (#1070). Its size is one literal per fixed
variable, two per unfixed one and one per hole run, over `n + k` positions; a
variable that appears at two positions is stated twice, since the list is not
deduplicated. Every RUP line of the scaffolding carries it, under
`emit_rup_proof_line_under_reason`.

**Offline reconstructibility, for all of rules 3 to 7.** `offline`. The reason
gives every item's and every total's domain exactly, holes included; the hint
names the constraint, whose rows are in the OPB. That fixes the whole
procedure: run the forward pass, the terminal filter and the backward pass over
those domains, in the constraint's item order, and write the derivation above.
Nothing is chosen. The states, edges and dead states are determined by the
rows and the domains, and the procedure succeeds whenever the clause follows by
GAC from the reason, which every rule's clause does. The solver's own derivation
is one instance; a reconstructor need not reproduce `Upfront`'s phantoms or its
caching. The cost is the diagram's: pseudo-polynomial, as for the solver.

**Two wire forms.** `hints::Knapsack`, `(constraint_id <id>)` with hint name
`knapsack`, for every `PerCall` rule, and `hints::KnapsackUpfront`, hint name
`knapsack_upfront`, for every `Upfront` rule; each carries only `originator`,
a `ConstraintID` (`hints.hh`). On `knapsack_bench` at `Inferences`, the family's
assertions are 62 to 72% of all the proof's assertions under either strategy
(the rest are the search's); see [Proof performance](#proof-performance).

### Rule: totals-when-all-fixed

- **Infers** — `totals[x] = Σ_i coefficients[x][i] · value(vars[i])`, for each
  row.
- **Fires when** — `PerCall` only, on a call where every item is fixed
  (`knapsack.cc:544–552`).
- **Strength** — `partial`: a fixed total, which rule 5 would also give.
- **Algorithm** — the committed sums, `O(nk)`.
- **Why it is true** — the row is an equality and every term on its left is
  known.
- **Proof technique** — `RUP`, against the row's two halves: with every item's
  bits fixed by the reason, each half propagates the total's bits.
- **Reason** — `vars[i] = value` for every item. Minimal unless an item has a
  zero coefficient in every row, when its value is not needed.
- **Assertion** — `totals[x] = v ∨ ¬reason`. Measured at `Inferences`, two
  items fixed at 1 and 0 with weights 2 and 3:
  ```
  a 1 i[t][eq2] 1 ~i[x][eq1] 1 ~i[y][eq0] >= 1::knapsack:((constraint_id _3));
  ```
  When the total cannot take the value, this same line is the conflict, as for
  any ordinary inference whose literal is already false; it is how `PerCall`
  fails at a leaf whose sum is outside a total's domain.
- **Hint** — `hints::Knapsack`: `originator`.
- **Offline reconstructibility** — `offline`: plain RUP against the cited
  constraint's rows.
- **Proof size** — one line of `n + 1` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: totals-lower-from-fixed

- **Infers** — `totals[x] ≥ committed_x`, the fixed items' contribution.
- **Fires when** — `PerCall` only, on every call, before the DP, whenever it
  tightens (`knapsack.cc:554–555`).
- **Strength** — `partial`: subsumed by rule 5's lower bound, which the same
  call infers next.
- **Algorithm** — `O(nk)`.
- **Why it is true** — every other term is non-negative.
- **Proof technique** — `RUP` against the row's `_le` half: with the fixed
  items' bits known and the negated conclusion bounding the total, the half's
  slack is negative.
- **Reason** — `generic_reason` over the items only. Not minimal (the unfixed
  items' bounds are not needed).
- **Assertion** — `totals[x] ≥ committed ∨ ¬reason`. Measured, one item fixed
  at 1 with weight 3 and one 0/1 item:
  ```
  a 1 i[t][ge3] 1 ~i[x][eq1] 1 ~i[y][ge0] 1 i[y][ge2] >= 1::knapsack:((constraint_id _2));
  ```
- **Hint** — `hints::Knapsack`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line of `O(n + h)` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: item-over-cap

- **Infers** — `vars[i] ≠ v`.
- **Fires when** — in the forward pass at item `i`'s layer, when every edge
  labelled `v` from every live state of the previous layer lands on a state
  whose partial sum exceeds some total's current upper bound
  (`knapsack.cc:357–371`; `knapsack_upfront.cc:673–679`).
- **Strength** — `partial` alone: the forward half of GAC on the items. With
  rule 7 it is GAC on the items (see rule 7).
- **Algorithm** — the forward pass: per state, per value of the item, `k`
  additions and a map insertion. `O(|layer| · |dom(vars[i])| · k log |layer|)`
  for the layer.
- **Why it is true** — every reachable partial sum of the earlier items plus
  `v · coefficients[x][i]` already exceeds `ub(totals[x])` for some `x`, and
  every later term is non-negative.
- **Proof technique** — `redundance` (`PerCall`'s flags), `pol` and `RUP
  sequence` (`PerCall`: the transitions, then for
  each over-cap edge a `pol` of the successor's coordinate flag, the row's
  `_le` half and the literal axiom `totals[x] ≤ ub`, then `¬S_parent ∨
  vars[i] ≠ v`; then the previous layer's at-least-one closes the conclusion).
  `PerCall` also writes, for each live state `w` of the new layer, a RUP `¬S_w
  ∨ vars[i] ≠ v` (`knapsack.cc:360–366`), which the conclusion should not need:
  at layer 0 the eliminated lines are already `vars[i] ≠ v`, and later the
  previous layer's at-least-one with the eliminated lines suffices. A scratch
  build without them verifies all 400 of the sweep's `PerCall` proofs below
  (200 plain, 200 with views and constants; `tmp/fd-dd/knapsack/exp-trim/`),
  which is evidence, not a proof that no instance needs them. `Upfront`:
  `chain scaffolding` (the `Top` forward chains and layer at-least-ones), the
  over-cap `pol` and a `Current` `¬S` lemma per newly dead state, then the
  conclusion by RUP. Both are Demirović et al.'s procedure.
- **Reason** — `generic_reason`, as in the preamble.
- **Assertion** — `vars[i] ≠ v ∨ ¬reason`. Measured, `5x + y = t`, `t ∈ 0..3`:
  ```
  a 1 ~i[x][b0] 1 ~i[x][ge0] 1 i[x][ge2] 1 ~i[y][ge0] 1 i[y][ge2] 1 ~i[t][ge0] 1 i[t][ge4] >= 1::knapsack:((constraint_id _1));
  ```
  (`::knapsack_upfront:` and the same clause under `Upfront`.)
- **Hint** — `hints::Knapsack` or `hints::KnapsackUpfront`.
- **Offline reconstructibility** — `offline`, as in the preamble.
- **Proof size** — `PerCall`: the call's diagram, shared by every inference of
  the call: `O(E · k)` lines for `E` edges, each RUP carrying the reason's
  `O(n + k + h)` literals, plus `|layer|` redundant RUPs per unsupported value.
  `Upfront`: per newly dead state a `Current` `¬S` lemma, with a `pol` first
  for an over-cap one, each written once per subtree, and the conclusion. Measured per root call in [Proof
  performance](#proof-performance).
- **Gaps** — `None.`
- **Tightness** — `Not shown.` No mutation lane.

### Rule: no-terminal-state

- **Infers** — a contradiction.
- **Fires when** — after the terminal filters (rule 5's lower bounds and rule
  6's holes), no terminal state is left (`knapsack.cc:434–442`;
  `knapsack_upfront.cc:750–756`).
- **Strength** — `partial`: it detects that no terminal state survives; if it
  fires the constraint has no solution in the current domains. Not every failure arrives here: when the forward pass
  leaves an item with no supported value, rule 3 wipes its domain first and the
  call fails as an ordinary inference (`attempted literal ∨ ¬reason`), and
  under `PerCall` rules 1 and 2 can fail before the DP runs. The fact-check's
  `chain/wipe.cc` (`5x + y = t`, `x ∈ 1..2`, `t ∈ 0..3`) fails through rule 3
  under both strategies and never reaches this rule.
- **Algorithm** — the forward pass and the filters.
- **Why it is true** — every assignment of the items in their domains either
  passes through a state erased as over a cap (and so violates that row) or
  reaches some terminal state, and every terminal state has a row whose total
  cannot take its sum.
- **Proof technique** — `pol` and `RUP sequence`: the scaffolding, then for
  each filtered
  terminal a `pol` against the row and the total's bound (or two `pol`s and a
  RUP naming the missing value), `¬S`, then the empty clause by RUP under the
  reason, then `contradiction()`.
- **Reason** — `generic_reason`.
- **Assertion** — `¬reason`, from `contradiction()`. Measured, `2x + 3y = t`
  with `t ∈ {4}`:
  ```
  a 1 ~i[x][ge0] 1 i[x][ge2] 1 ~i[y][ge0] 1 i[y][ge2] 1 ~i[t][eq4] >= 1::knapsack:((constraint_id _2));
  ```
  (the same clause with `::knapsack_upfront:`).
- **Hint** — as rule 3.
- **Offline reconstructibility** — `offline`.
- **Proof size** — as rule 3, plus one RUP of `O(n + k + h)` literals.
- **Gaps** — `None.` The call's temporary lines are stranded until the next
  forget of their level ([Proof-time state](#proof-time-state)).
- **Tightness** — `Not shown.`

### Rule: total-bounds

- **Infers** — `totals[x] ≥ committed_x + min_w w[x]` and `totals[x] ≤
  committed_x + max_w w[x]`, over the surviving terminal states `w`, for every
  row, in one `infer_all` with rule 6 (`knapsack.cc:444–490`;
  `knapsack_upfront.cc:758–796`; `committed` is 0 under `Upfront`).
- **Fires when** — the terminal set is non-empty and some bound moves.
- **Strength** — `bounds(D)` on the totals alone: each new bound is the
  coordinate of a surviving terminal state, which is a support in the current
  domains. With rule 6, `GAC` on the totals; with a repeated variable, `GAC`
  only on the decomposition in which each position is a distinct variable.
  Checked by brute force
  (`gac/kcheck.cc`: 2,000 random instances per seed at seeds 1 and 2, per
  strategy, `k` from 1 to 3, `n` from 0 to 4, coefficients 0 to 4, items in
  `0..d` with `d ≤ 3` and totals in up to `0..48`, every domain holey; no GAC
  failure on any variable, no unsound root, and identical root domains under
  the two strategies).
  `knapsack_test` and `knapsack_upfront_test` check GAC at every node too.
- **Algorithm** — a min and a max over the terminal states per row.
- **Why it is true** — the terminal states that survive the filters are
  exactly the vectors of reachable sums that every total admits, so the
  total's value in any solution is one of their coordinates.
- **Proof technique** — `pol` and `RUP sequence`: per row and per surviving
  terminal, a
  `pol` of the row's `_le` half with the state's `≥` coordinate flag, in which
  the unfixed items' partial sum cancels exactly against the row, and its RUP
  `¬flag ∨ totals[x] ≥ lo`; the mirror for `≤ hi`; then `totals[x] ≥ lo` and
  `totals[x] ≤ hi` by RUP from the last layer's at-least-one; then the
  `infer_all` conclusions.
- **Reason** — `generic_reason`.
- **Assertion** — `bound ∨ ¬reason`, one per literal. Measured, `2x + 3y = t`
  with `t ∈ 1..9` (sums 0, 2, 3 and 5):
  ```
  a 1 i[t][ge2] 1 ~i[x][ge0] 1 i[x][ge2] 1 ~i[y][ge0] 1 i[y][ge2] 1 ~i[t][ge1] 1 i[t][ge10] >= 1::knapsack:((constraint_id _1));
  a 1 ~i[t][ge6] 1 ~i[x][ge0] 1 i[x][ge2] 1 ~i[y][ge0] 1 i[y][ge2] 1 ~i[t][ge1] 1 i[t][ge10] >= 1::knapsack:((constraint_id _1));
  ```
  Where `PerCall` fixes a total by rule 1 at a leaf, `Upfront` writes this
  rule's two bound lines instead.
- **Hint** — as rule 3.
- **Offline reconstructibility** — `offline`.
- **Proof size** — on top of the diagram, `4` lines per row per terminal
  state and `2` per row.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: total-holes

- **Infers** — `totals[x] ≠ v` for each value `v` strictly inside the new
  bounds that no surviving terminal state reaches, in the same `infer_all`.
- **Fires when** — as rule 5.
- **Strength** — `partial` alone: it removes every unsupported value strictly
  inside the totals' new bounds. With rule 5, `GAC` on the totals.
- **Algorithm** — **a walk of every value of the total's current domain, and
  for each value inside the new bounds a scan of every terminal state**
  (`none_of`): `|dom(totals[x])| + |dom(totals[x]) ∩ [lo, hi]| · |terminal|`
  per row, so `O(|dom(totals[x])| · |terminal|)` at worst.
  See [Interval efficiency](#interval-efficiency) and #1340.
- **Why it is true** — as rule 5.
- **Proof technique** — `RUP`, after rule 5's terminal `pol`s: with the
  negated conclusion fixing the total at `v`, each surviving terminal state's
  `≥` or `≤` line is falsified unless its coordinate is `v`, and none is.
- **Reason** — `generic_reason`.
- **Assertion** — `totals[x] ≠ v ∨ ¬reason`. Measured, the same instance:
  ```
  a 1 ~i[t][eq4] 1 ~i[x][ge0] 1 i[x][ge2] 1 ~i[y][ge0] 1 i[y][ge2] 1 ~i[t][ge1] 1 i[t][ge10] >= 1::knapsack:((constraint_id _1));
  ```
- **Hint** — as rule 3.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one RUP of `O(n + k + h)` literals per removed value, on
  top of rule 5's lines.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: item-unsupported-backward

- **Infers** — `vars[i] ≠ v`.
- **Fires when** — in the backward pass after the `infer_all`, when no edge
  labelled `v` into item `i + 1`'s layer reaches a state that can still reach a
  surviving terminal (`knapsack.cc:492–525`; `knapsack_upfront.cc:798–830`).
- **Strength** — `partial` alone: the backward half of GAC on the items,
  removing values whose every edge leads to no surviving terminal. With rule 3,
  `GAC` on the items, on distinct variables, and on the decomposition with a
  distinct variable per position otherwise; the brute force under rule 5 covers
  it.
- **Algorithm** — a walk of the recorded predecessor lists from the last layer
  back, collecting the reached states and supported values, then a pass over
  the item's values. `O(edges)` with set operations.
- **Why it is true** — every solution is a path from the zero state to a
  surviving terminal, and no such path takes the edge.
- **Proof technique** — `RUP sequence`: `¬S` by RUP for each state the pass
  finds unreached (`Temporary` under `PerCall`; `Current`, through the `Top`
  backward chains, and once per subtree under `Upfront`), then the conclusion by
  RUP, the steps McIlree and McCreesh (*Proof Logging for Smart Extensional
  Constraints*, CP 2023) use for `Regular`, as Demirović et al. note.
- **Reason** — `generic_reason`, materialised after the `infer_all`, so with
  the totals' new bounds.
- **Assertion** — `vars[i] ≠ v ∨ ¬reason`. Measured, `2x + 3y = t` with
  `t ∈ 5..9`, after rule 5 fixed `t = 5`:
  ```
  a 1 i[y][b0] 1 ~i[x][ge0] 1 i[x][ge2] 1 ~i[y][ge0] 1 i[y][ge2] 1 ~i[t][eq5] >= 1::knapsack:((constraint_id _1));
  ```
- **Hint** — as rule 3.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one `¬S` per unreached state plus the conclusion, each of
  `O(n + k + h)` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

- **`knapsack_test`** (`PerCall`) and **`knapsack_upfront_test`** (`Upfront`)
  run the same 21 curated instances (`k` from 1 to 3; items 0/1, `1..4` and
  `2..4`; #254's degenerate shapes, with items fixed at 0 or 1) and 10 random
  ones (`k` and `n` up to 4, coefficients up to 8, item ranges from
  `random_bounds(0, 2, 1, 3)`: a lower bound in `0..2` and a width of 1 to 3,
  so up to `2..5`), under `solve_for_tests_checking_gac`, so GAC at every node,
  against a brute force, with and without proofs; VeriPB runs when it is on
  the path. Every domain starts as an interval. Two duplicate-variable runs each (`[x, x]` and
  `[x, y, x]`), under plain `solve_for_tests`. Seeded.
- **`knapsack_upfront_test`** also runs a deterministic regression first
  (`run_knapsack_upfront_regression`, `dom_then_deg` and smallest-first over
  five 0/1 items and two rows, with a proof), which pins a phantom-rule failure
  that random branching masked, and `run_wide_partial_sums_test`, which pins
  the fallback to `PerCall` without a proof and `IntegerOverflow` with one.
- **`integer_ranges_test`:** a refusal case for a coefficient past the range,
  through the two-total constructor.
- **`scp_chain_knapsack_sat`, `_unsat`:** see [Cake
  conformity](#cake-conformity).
- **MiniZinc:** `knapsacktest.mzn` (four 0/1 items, maximise profit), with a
  proof.
- **XCSP3:** none.
- **Audit lane:** the one `KnownTrip` row.

**Runtime caps.** No lane sets or clears one. Under the default caps
(`GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500`) neither test
truncates a single run, at seeds 1 to 5: 66 runs in `knapsack_test` and 69 in
`knapsack_upfront_test`, the largest expecting 210 solutions. So the capped run
checks everything the uncapped one does. Uncapped at seed 1, they take 5.2 s
and 2.9 s (`knapsack_test --seed=1`, VeriPB on the path, at `86caad24`).

**Tightness:** no mutation lane. The `Upfront` regression is a control in the
sense that it must verify uncorrupted; nothing corrupts a derivation.

**This audit's own checks** (all at `86caad24`, fataepyc-10, 2026-10-10):

- **Root brute force**, `gac/kcheck.cc`, as under rule 5: 4,000 instances
  without repeats, each under both strategies, no failure; 4,000 with repeats,
  each under both, sound.
- **Proofs**, `proofs/ksweep.cc`: 400 random instances (`k` 1 to 3, `n` 1 to
  5, coefficients 0 to 5, holey item and total domains), enumerated under a
  seeded random value order, for each strategy with plain items and with items
  drawn from plain, offset views, negated views and constants: all 1,600 proofs
  verify with VeriPB 3.0.2 (`--force-checked-deletion`), every solution count
  matches the brute force, and the two strategies' node counts agree on all 800
  pairs. Another 40 per strategy at `Inferences` are `UNDER ASSERTIONS` with the
  right counts.
- **Front ends**, as under [Concrete
  constraints](#concrete-constraints-and-frontend-coverage).

**What the tests do not cover.**

- **Holey initial domains, views and constants**: none in the suite; this
  audit's root checks and sweeps cover them.
- **A view or constant total with proofs at `Off`** (#1229): nothing tests it, which is
  how it stayed hidden from MiniZinc's fixed capacities.
- **Negative values from a front end**, and any XCSP3 knapsack at all.
- **Wide domains**, beyond the one `KnownTrip` row; and **any instance large
  enough to show the pseudo-polynomial cost**. The largest test has 210
  solutions.
- **A row of the wrong length.**
- **Real instances:** neither corpus model is ported, and neither could run.

### Benchmarks and examples

- **In the repository:** `benchmarks/knapsack_bench` (four curated instances,
  either strategy, deterministic search; not a ctest) and `examples/knapsack`.
- **Corpus:** `multi-knapsack` 2015 and 2019 (`mknapsack_global.mzn`) post five
  `knapsack` constraints each, over 50 and 39 0/1 items, with weight totals in
  `0..b_i` (at most 800 and 600) and the profit total fixed at the instance's
  known optimum `z` (16,537 and 10,618): the model passes `z` as `P`, which
  makes it a search for a solution of that exact profit. No other model in
  the throw survey's flattenings (`tmp/throw-survey/fzn.tar.gz`, one instance
  per model) posts the family; `2014_multi-knapsack` posts none; #1070 said none did, which these two
  correct. **Never run either with a proof:** the root call alone wrote 41 GB
  and 48 GB in about five minutes, and neither `-t` nor `SIGTERM` takes effect
  until the call returns; stop it with `SIGKILL`, or cap the file size.
- **For CPU:** the generated enumerations below (`perf/gecode/b1.txt`,
  `b2.txt`, `b3.txt` with their `.mzn` twins), which run seconds and keep the
  node and solution counts equal across both strategies.
- **For proof verification:** `knapsack_bench` 1 to 4, which verify in 6 to 40
  s.

### CPU performance

*Release build of `86caad24` (GCC 15.2.0, `-O3 -march=native`); Gecode 6.3.0 through
MiniZinc 2.9.7; fataepyc-10, pinned to one core, malloc thresholds fixed;
2026-10-10; medians of three runs.*

**Against Gecode, enumerating every solution.** `kbig.cc` posts one two-row
`Knapsack` and branches in input order, smallest value first; the MiniZinc twin
uses `int_search(x, input_order, indomain_min)`, so Gecode runs the standard
decomposition into two linear equalities, bounds consistent. The strengths
differ: Glasgow is GAC and never fails, Gecode fails often.

| Instance | Solutions | GCS nodes | Gecode nodes | Gecode failures | `PerCall` | `Upfront` | Gecode |
|---|---|---|---|---|---|---|---|
| b1: 18 items 0/1, weights 1–9 | 8,278 | 16,555 | 23,635 | 3,540 | 1.158 s | 1.519 s | 0.395 s |
| b3: 12 items in `0..2`, weights 1–6 | 13,131 | 23,083 | 43,225 | 8,482 | 1.332 s | 1.624 s | 0.569 s |
| b2: 22 items 0/1, weights 1–9 | 60,469 | 120,937 | 269,305 | 74,184 | 11.28 s | 15.25 s | 3.27 s |

Gecode is 2.3 to 3.5 times faster while exploring 1.4 to 2.2 times the nodes,
so per node it is 4 to 8 times cheaper. The rebuild-per-call design, and its
allocation (see [Mutable state](#mutable-state-and-incrementality)), is the
difference.

**`knapsack_bench`, proofs off.** Same build; five runs each, median.

| Instance | Solutions | Nodes | Calls (effectful) | `PerCall` instructions:u | `Upfront` instructions:u | `PerCall` solve | `Upfront` solve |
|---|---|---|---|---|---|---|---|
| 1: 10 items 0/1, k = 2 | 454 | 907 | 1,783 (876) | 131.8 M | 175.9 M | 0.0230 s | 0.0285 s |
| 2: 10 items 0/1, k = 2, wider weights | 328 | 655 | 1,290 (635) | 131.9 M | 164.1 M | 0.0232 s | 0.0274 s |
| 3: 7 items in `0..2`, k = 2 | 724 | 1,205 | 2,355 (1,150) | 118.4 M | 162.9 M | 0.0210 s | 0.0267 s |
| 4: 9 items 0/1, k = 3 | 173 | 345 | 679 (334) | 80.2 M | 91.7 M | 0.0139 s | 0.0153 s |

The solve times are 14 to 29 ms, close enough to the 10 ms floor this arc
trusts that the instruction counts are the measure. Node and call counts are
identical across the strategies.

**The corpus.** With proofs off and `-t 30000`, `multi-knapsack` 2015 spends
125 s in one root call at a peak of 25 GB, and 2019 43 s in two calls at 8.7 GB,
before reporting `UNKNOWN`; `-t` cannot interrupt a call (`/usr/bin/time`,
`corpus/run/gcs_nop_*.txt`). The DP's layers pair a weight partial sum in
`0..800` with a profit partial sum in `0..16,537`, and the profit total being
fixed does not help until the last layer, since the forward pass prunes only on
upper bounds. Gecode 6.3.0 on the same models, by the standard decomposition:
2019 found and proved `objective = 10618` in 0.86 s (349,357 nodes); 2015 did
not finish in 120 s (56 million nodes), so that instance is hard for both.

**What the benchmarks do not exercise.** Holey domains, views, repeated
variables, a contradiction (the bench enumerations never fail), and anything
wide.

### Proof performance

*Same build and machine, 2026-10-10. VeriPB 3.0.2 with
`--force-checked-deletion`, timed solo by this document's fact-check on an idle
fataepyc-10 (load 0.13), bound to one NUMA node and one physical core
(`numactl --cpunodebind=1 --membind=1 taskset -c 90`), on the same proof files;
a pinned re-run under light load agreed within 4%. This audit's own first
timings, taken while other work was running, had `Upfront` 8 to 42% slower and
`PerCall` within 7%; the `Upfront` proofs' larger working sets (207 to 289 MB on
instances 2 and 4) make them sensitive to memory load.*

**`knapsack_bench`, both strategies.** "Scaffold `red`" counts the `red` lines
naming a `kp` flag.

| Instance | Strategy | Solve, proof on | Lines | Bytes | VeriPB | µs per line | Scaffold `red` |
|---|---|---|---|---|---|---|---|
| 1 | `PerCall` | 1.161 s | 484,165 | 121.3 MB | 6.42 s | 13.3 | — |
| 1 | `Upfront` | 0.354 s | 174,207 | 20.7 MB | 7.09 s | 40.7 | 11,116 |
| 2 | `PerCall` | 1.292 s | 515,588 | 138.2 MB | 8.52 s | 16.5 | — |
| 2 | `Upfront` | 0.516 s | 305,597 | 26.9 MB | 22.68 s | 74.2 | 23,792 |
| 3 | `PerCall` | 0.797 s | 407,724 | 82.3 MB | 6.19 s | 15.2 | — |
| 3 | `Upfront` | 0.390 s | 182,660 | 19.3 MB | 8.95 s | 49.0 | 7,838 |
| 4 | `PerCall` | 0.938 s | 379,442 | 102.1 MB | 5.74 s | 15.1 | — |
| 4 | `Upfront` | 0.421 s | 441,141 | 34.2 MB | 33.88 s | 76.8 | 32,670 |

`Upfront`'s proofs are 3.0 to 5.9 times smaller in bytes and are written 2.0 to
3.3 times faster, and they take 1.10 to 5.9 times as long to check: only 10%
longer on instance 1, 2.7 and 5.9 times on instances 2 and 4. On instance 4
they are larger in lines too. The ratio of checking to solving is 5.5 to 7.8
for `PerCall` and 20 to 80 for `Upfront`.

**How much of `Upfront`'s proof is per call.** Splitting each `Upfront` `Off`
proof at the end of its `Top` scaffold (the last `kphantom` line; the
fact-check's re-check), the scaffold is 59%, 81%, 52% and 90% of the lines on
instances 1 to 4, but only 29%, 52%, 29% and 70% of the bytes, since its lines
carry no reason. So the per-call part (which also holds the search's `solx`
and backtrack lines) is most of the bytes on instances 1 and 3 and never most
of the lines; `decision-diagram-proof-strategies.md`'s "≈ 60% of upfront's lines"
for the scaffold matches instance 1.

**Figures measured elsewhere**, not to be mixed with the table above:
`dev_docs/knapsack.md` and
[`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md)
give `Upfront` as 3.6 to 18 times slower to check, with per-call checks of 1
to 2 s and 3.7 to 4.4 µs a line, from the PR #210 era.
`dev_docs/knapsack.md` names no VeriPB version; the decision-diagram note says
3.0.2; neither names a machine. The re-measurement above has the per-call proofs at
5.7 to 8.5 s and 13 to 17 µs a line, and the gap at 1.10 to 5.9 times.

**Own against shared, approximately.** At `Inferences` the family's inferences
are `a` lines and the search's lines are almost unchanged (above
`Definitions` each solution adds an asserted `solx_block` line, 454 on instance
1, and `Off` has 186 lines of shared literal definitions that `Inferences`
does not), so `Off` lines minus (`Inferences` lines minus the family's `a`
lines) is approximately the family's own volume, to well under one point:
479,202 of 484,165
lines on instance 1 under `PerCall` (99.0%), and 169,244 of 174,207 under
`Upfront` (97.2%); across the four instances and both strategies, 96.2% to
99.5%. The shared layers, the search's solution and backtrack lines, are 1,900
to 6,900 lines here, since the bench has no other constraint.

**Per root call, against the instance.** One root call (`size/ksize.cc`, items
in `0..d`, weights drawn from `1..wmax`, totals in a quarter to a half of the
reachable range; `size/grid.txt`): `PerCall`'s whole proof, which is almost all
the root call, against `Upfront`'s scaffold (the lines before the first that
names a total).

| n | k | d | wmax | `PerCall` lines | `PerCall` bytes | `Upfront` scaffold lines | scaffold bytes |
|---|---|---|---|---|---|---|---|
| 0 | 1 | 1 | 5 | 30 | 764 | 9 | 476 |
| 1 | 1 | 1 | 5 | 95 | 4.5 KB | 56 | 3.1 KB |
| 8 | 1 | 1 | 5 | 1,961 | 402 KB | 5,520 | 342 KB |
| 16 | 1 | 1 | 5 | 6,745 | 2.5 MB | 19,605 | 1.3 MB |
| 8 | 2 | 1 | 5 | 5,094 | 1.2 MB | 36,693 | 2.1 MB |
| 12 | 2 | 1 | 5 | 31,233 | 10.8 MB | 221,805 | 12.5 MB |
| 8 | 3 | 1 | 5 | 8,716 | 2.3 MB | 145,748 | 8.6 MB |
| 8 | 2 | 2 | 5 | 27,165 | 7.0 MB | 221,330 | 12.0 MB |
| 8 | 2 | 3 | 5 | 72,054 | 19.0 MB | 656,279 | 34.2 MB |
| 8 | 2 | 1 | 20 | 9,233 | 2.2 MB | 173,113 | 9.6 MB |

Once there are a few items, `PerCall`'s lines average 200 to 370 bytes, since
each RUP carries the whole reason; `Upfront`'s scaffold lines 52 to 68, since
they name no reason. The scaffold grows with the static diagram, which holds every partial sum reachable
from the initial domains whatever the totals allow, plus the phantoms, and so it
is much larger than one call's diagram whenever the totals are tight. The
`multi-knapsack` root calls are this table's extreme: tens of gigabytes for one
call.

**Assertion levels.** This audit measured `Off` and `Inferences` only. The
fact-check ran `Definitions`, `Links` and `Backtracking` too, on its own fuzzer
(1 to 2 constraints, repeats, views, constants and an `Element`): no mismatch
and no rejection except at `Links`, where 61 of 300 proofs per strategy are
rejected at their first `solx` line, as plain `Equals` and `LinearEquality`
proofs are; that is #1210, not this family's. At `Inferences` the bench proofs are 0.59 to 1.52 MB and
check `UNDER ASSERTIONS` in 0.02 to 0.05 s. The family's `a` lines: 2,590 of
3,951 on instance 1 under `PerCall` (65.6%), 2,245 of 3,228, 3,171 of 5,100 and
1,347 of 1,865 on the others; under `Upfront` the counts are within a few on
instances 1, 2 and 4 (2,587 against 2,590 on instance 1) and 7% higher on
instance 3 (3,385 against 3,171). By wire form on instance 1, `PerCall`: 612
rule 1, 1,009 rule 5 (with rule 2), 704 rule 6, 265 rules 3 and 7; `Upfront`:
1,618 rule 5, 704 rule 6, 265 rules 3 and 7. So `Upfront`'s bound lines number
about `PerCall`'s rule-5 and rule-1 lines together (1,618 against 1,621);
`Upfront` writes two lines where `PerCall`'s rule 1 writes one only at some
leaves, such as the catalogue's all-fixed shape, and this was not broken down
further. A clause averages 16.8 to 20.4 terms on the 0/1 instances.

## Status, gaps, and next steps

### Proof-logging gaps

`None` for the inferences: every one is justified at `Off` under both
strategies, and neither propagator changes with proofs on. Two ways a proof is
not produced at all, each a filed issue rather than a gap in a
derivation:

- **A constant or view total, with proofs on at `AssertionLevel::Off`,**
  throws `UnimplementedException` (#1229); above `Off` the inferences are
  asserted and nothing throws. Reachable from MiniZinc's `--prove` whenever a
  capacity or profit is a parameter and some cap-exceeded or lower-bound `pol`
  fires; both corpus models pass a constant total, though neither has been
  seen to get far enough to throw.
- **A pseudo-polynomial diagram is written in full on every call** under
  `PerCall`, and from the initial domains under `Upfront`, so a large instance
  cannot be proved in practice (#1341).

### Known limitations

- **A model with negative item values or totals does not run from MiniZinc**,
  which errors where its own definition would have constrained them to be
  non-negative (negative weights and profits are refused by MiniZinc's wrapper
  for every solver). **XCSP3 aborts** on a negative item value, weight or
  profit. #1337.
- **Large partial-sum ranges make every call slow**, and a two-row knapsack
  whose second row has a large range (a profit) can stall the root: the
  `multi-knapsack` models spend their whole time limit in it. #1341.
- **A total with a wide declared domain, or an item whose values reach many
  sums, costs time proportional to the total's width times the reachable
  sums.** #1340.
- **With proofs on at `AssertionLevel::Off` (`--prove`), a fixed capacity or
  profit fails** (#1229); at higher assertion levels it does not.
- **A repeated variable propagates less than it could.**
- **`Upfront` proofs are smaller but slower to check**, and `Upfront` is slower
  than `PerCall` with proofs off.

### Next steps

1. **Fix #1229.** For a view total, add the bound literal on the view, as
   `PolBuilder::add_for_literal` does elsewhere; for a constant total, the row
   has no total term to cancel and the axiom can be skipped. Small. Then test
   view and constant totals with proofs; MiniZinc's fixed capacities and the
   corpus need it.
2. **Front-end semantics for negative values** (#1337): have Glasgow's
   `fzn_knapsack` post `x[i] ≥ 0`, `W ≥ 0` and `P ≥ 0` (or clamp) as the
   standard definition does; in XCSP3, decompose shapes with negative item
   values, weights or profits to linear equalities, and catch `InvalidProblemDefinitionException`
   around the solve so a refusal is `UNSUPPORTED` rather than an abort. Small.
3. **Make the interior-value pass per terminal state** (#1340): collect each
   row's reachable sums once, then remove the gaps from the total's domain by
   intervals. Small; removes the quadratic case and the audit lane's trip at
   the root.
4. **Do something about large partial-sum ranges** (#1341). The
   `multi-knapsack` models show the exact DP is the wrong tool when a row's
   range is in the tens of thousands; the relaxation and approximation
   filtering of Fahle and Sellmann and of Sellmann are the published
   alternatives, and choosing among propagators by the diagram's size is a
   design question not filed separately (#200 is about one generic diagram
   propagator, not that). Per the standing rule, not a budget. Large; needs a
   design.
5. **Validate row lengths in the constructor, for both strategies** (#1334).
   Trivial: move `Upfront`'s checks into `Knapsack`'s constructor (the lower
   bounds still need `prepare()`).
6. **Close the temporary level on a failure.** Wrap the call in the same
   `try`/`catch` the inference tracker uses, or a scope guard. Small; cuts the
   live database after every failing call. Not filed.
7. **Claim idempotence when no variable repeats**, after checking it with the
   idempotence checker (#1056): on the bench, 907 of 1,783 calls change
   nothing, and whether those are the propagator re-running after its own
   change was not shown. Small; measure on a fixed tree. Not filed.
8. **Trim `PerCall`'s proof** (#1070's always-true bounds; the redundant `¬S ∨
   vars[i] ≠ v` lines under rule 3; materialise the reason once per call
   rather than per line, and not at all with proofs off). Per the arc's rule,
   which lemmas the RUPs need is an empirical question. Not filed beyond
   #1070.
9. **Hint the dead-state RUPs** (#497), and **sweep the large-domain lane
   wider**: an `Upfront` row, a wide item, and a proof-size row.
10. **Bring the out-of-stack text into line**: `dev_docs/knapsack.md` still
    describes a `KnapsackUpfront` class, a `knapsack_upfront` keyword and XCSP3
    posting "the general k-total constructor" (it posts the two-row one), and
    its benchmark table predates this one; `bin-packing.md` cites CP 2024 "§4"
    for §3.3 and still names a `KnapsackUpfront` variant; the `Dag` comment at
    `knapsack_upfront.cc:75–76` says the cap is intersected with the totals,
    which `compute_caps` deliberately does not do; `knapsack.hh:25–26` and
    `knapsack_upfront.hh:25` repeat the superseded 3.6–18× and 3–6× figures,
    as `frontend-support-matrix.md:93` does, which also still names a
    `KnapsackUpfront` variant (that file is being retired, so it is left to
    rot, as TEMPLATE.md says);
    and `TEMPLATE.md` and `linear.md` say knapsack uses subset-sum
    strengthening.

## Prior art

**Propagation.** Trick (*A Dynamic Programming Approach for Consistency and
Propagation for Knapsack Constraints*, Annals of Operations Research
118(1–4):73–84, 2003) gives the layered dynamic programme for a single 0/1
linear constraint whose sum is a variable; propagators built on it reach domain
consistency on the items and bounds or domain consistency on the sum (Trick's
paper as Demirović et al. §3.3 and McIlree's thesis §5.2.2 summarise it; this
audit did not read Trick's paper itself). This family's propagator is Trick's,
generalised to `k` rows sharing one item list and to non-0/1 items, with the
totals filtered by value. Fahle and Sellmann (*Cost Based Filtering for the
Constrained Knapsack Problem*, Annals of OR 115(1–4):73–93, 2002), Sellmann
(*Approximated Consistency for Knapsack Constraints*, CP 2003, LNCS 2833,
679–693) and their successors (Katriel et al., AAAI 2007; Malitsky et al., AAAI
2010) work on the two-row weight-and-profit form, by filtering against
relaxations and approximations rather than an exact diagram; none of that is
implemented here.

**Certification.** Demirović, McCreesh, McIlree, Nordström, Oertel and Sidorov
(CP 2024, LIPIcs 307, 9:1–9:21, doi:10.4230/LIPIcs.CP.2024.9) give the PB
proof method, partial-sum flags
`W↑`, `W↓`, `P↑`, `P↓` and a state flag per weight and profit pair, with
transitions by cutting planes and RUP and at-least-ones by resolution, in §3.3
("Knapsack as a Constraint"), and report implementing it in this solver "using
a top-down construction" for arbitrarily many rows and non-0/1 items. McIlree's
thesis (§5.2.2) restates it as Encoding Procedure 5.3 and Example 5.2, and notes
that the Knapsack implementation in this solver is not its author's. So
certified Knapsack is not new, and `PerCall` is that published method,
generalised to `k` coordinates. The arrangement `Upfront` shares with the other
diagram constraints, backward chains derived once at the root and kept at
`Top` with a per-search-path cache of the per-call dead-state lemmas, is the
solver's upfront strategy, landed for `Regular`, `MDD`, `Knapsack` and
`BinPacking` in one PR stack (#210 to #213), and is claimed once, in
[`regular.md`](regular.md#prior-art); the lemma-then-RUP shape itself is CP 2024
§3.3's. What is this family's own is the synthesised diagram over the initial
domains, `k`-dimensional and not intersected with the totals, with its phantom
states and their closing rules. `BinPacking`'s `k = 1` copy keeps the phantom
states and the per-coordinate closing rule (`bin_packing.cc:71–86`, `:552–557`)
but cannot need the joint-only closing case (`knapsack_upfront.cc:470–477`). As far as this audit knows they are unpublished; they are described in
`dev_docs/knapsack.md`.

## Further reading

- [`knapsack.md`](../knapsack.md): the long design note for `Upfront`: the
  static diagram, the not-intersected caps, the phantoms and their two closing
  cases, the `Top` scaffolding line by line, and the `DeadCache`. Its
  strategy-comparison figures predate this audit's.
- [`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md):
  upfront against per-call for `Regular`, `MDD`, `Knapsack` and `BinPacking`,
  the displacement-against-cost-per-line model that explains why `PerCall` is
  the default here, and the negative results on deleting scaffolding and
  hinting.
- [`bin-packing.md`](../bin-packing.md): the `k = 1` copy of the upfront
  diagram.
- [`integer-ranges.md`](../integer-ranges.md): what the overflow behaviour is
  allowed to be.
