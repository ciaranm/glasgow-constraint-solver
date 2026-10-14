# `BinPacking`: each item in one bin, each bin's sizes summing to its load or within its capacity

> **Maturity** production (`consistency::GAC` with `proof_strategy::PerCall`,
> the default, and `consistency::BC`); production, opt-in
> (`proof_strategy::Upfront`, `bin_packing::Shaw`) ·
> **Audited** 2026-10-10 at `86caad24`, with the proof timings re-taken on
> 2026-10-14 at the same commit ·
> **Open issues** filed by this audit: #1345 (XCSP3's single-`<condition>`
> form constrains bins no item can take, so it reports `UNSATISFIABLE` on
> satisfiable instances and loses solutions), #1347 (item domains outside the
> bins and negative load lower bounds, which MiniZinc's definition constrains
> away, error from MiniZinc, `var opt` models over 1-based bins among them;
> XCSP3 aborts on negative sizes, limits and loads and on out-of-range item
> domains), #1346 (Stage 3 never commits an item to a bin its load forces it
> into, so it is not the per-bin GAC its header claims), #1349 (in the
> constant-capacity form the default Stage 3 never infers anything and no
> Stage 3 changes the fixpoint, yet `GAC` builds the diagrams, sweeps them and
> writes their flags at `Top`), #1348 (no cross-bin load reasoning: the loads
> are never made to sum to the total size). Commented on by this audit: #1340
> (`Upfront`'s interior-value pass is `Knapsack`'s, linear in a large size and
> quadratic in the terminals) and #1210 (the `Links` rejections of
> range-declared variables, which this family's proofs meet too).
> Already open and touching this family: #497 (an open draft PR, a
> prototype that hints the `pol`-based dead-state RUPs of `Knapsack` and of
> `BinPacking`'s `Upfront`, recording a negative result), #200 (one layered-diagram framework), #833
> (the large-domain policy), #868 (cross-solver comparisons; this document
> gives one, by hand). Tracked under #871.

`BinPacking(items, sizes, loads)` puts item `i` in bin `items[i]` and makes
each bin's sizes sum to `loads[b]`; `BinPacking(items, sizes, capacities)`
makes them sum to at most `capacities[b]`. MiniZinc's `bin_packing`,
`bin_packing_capa` and `bin_packing_load`, and XCSP3's `<binPacking>`, map
onto it. The model is one linear row per bin (two in the load form). The
propagation is staged, and the stages are the thing to know:

- **Stage 2** (always): per-bin bounds, Shaw's basic rules (CP 2004, §2.5):
  a bin's load lies between the sizes already in it and the sizes that can
  still be; an item that would overflow a bin leaves it, and one without which
  the bin cannot reach its load joins it. Plain RUP against the bin's row.
- **Stage 3** (`consistency::GAC`, the default): a per-bin partial-load
  diagram (Trick's dynamic programme, `k = 1`), which removes `b` from an
  item's domain when no packing of bin `b` uses the item, and cuts the load to
  the reachable sums. Two proof strategies: `PerCall` (the default) defines a
  flag per diagram node at `Top` and writes each state-independent chain line
  at `Top` the first time an inference needs it, after which every inference
  is a RUP; `Upfront` is a `k = 1` copy of `Knapsack`'s upfront diagram
  ([`knapsack.md`](knapsack.md)), with its whole scaffold at `Top`.
- **Stage 4** (`bin_packing::Shaw`, opt-in): a cross-bin counting bound,
  one cutting-planes derivation per threshold `α` (divide each bin's row by
  `α`, sum against the items' at-least-one rows), which catches pigeonhole
  infeasibilities that no single bin can see, plus a shaving loop that turns
  it into item prunes.

Five things to know before touching it.

- **One wrong-answer route, in a front end.** XCSP3's single-`<condition>`
  form makes a load for every bin from 0 up to the largest item value and puts
  the condition on all of them, including bins that no item's domain contains,
  whose load is 0. A condition that rejects 0 then makes Glasgow report
  `UNSATISFIABLE` on satisfiable instances, with a proof VeriPB accepts, or
  lose solutions: 7 of 400 random instances against ACE (#1345). No other
  route gave a wrong answer: 1,600 random proofs plus 800 tight ones verify
  with the right counts, and brute-forced root fixpoints are sound,
  views, constants and repeated variables included (128,000 random instances
  without repeated variables, half of them with views and constants, and
  20,000 with repeats).
- **Stage 3 is per-bin GAC on the bin values and the loads, not on the
  items.** It removes `b` from an item when no packing of bin `b` takes it,
  but never commits an item to `b` when every packing does, which the bin's
  constraint alone requires; Shaw states both rules. In the load form 36 of
  2,000 random instances at the root leave such a value (#1346). In the
  constant-capacity form an item can always leave a bin, so Stage 2 alone is
  per-bin GAC there (for distinct item variables), and Stage 3 never changes
  the fixpoint: under `PerCall`
  it never infers at all, and under `Upfront` it only draws, a call early,
  what Stage 2 would draw next.
- **Which is why the default wastes work on the constant-capacity form.**
  `consistency::GAC` builds the per-bin diagrams over every partial sum the
  items' initial domains reach, sweeps them on every call that changes a bin,
  and with proofs on writes six `red` lines per diagram node at `Top`, for no
  change to the fixpoint: `GAC` and `BC` search the same trees (equal node
  and solution counts on all 400 random capacity-form pairs); on the
  bench, `GAC` runs 2.6 to 3.3 times `BC`'s instructions on the two capacity
  enumerations and its proof takes 9.5 times as long to check (#1349).
- **`Upfront` is bigger, slower to check and, with a large size, much slower
  to run.** On the bench its proofs are 4.5 to 20.8 times `PerCall`'s in
  bytes and 3.7 to 6.0 times slower to check, and with proofs off it runs 1.6
  to 3.5 times the instructions on the same trees. Its copy of `Knapsack`'s
  interior-value pass walks every value of the load after Stage 2: two items
  of sizes 1 and 10⁸ take 60 s in the root call under `Upfront` and about
  0.1 ms under `PerCall` (#1340, commented on). The declared width of a load costs nothing under either, because
  Stage 2 cuts the load to the reachable range first.
- **Front ends refuse shapes their definitions constrain away.** An item
  domain reaching outside the bins, or a load with a negative lower bound,
  throws `InvalidProblemDefinitionException` from `prepare()`. MiniZinc's own
  decompositions constrain both (and `var opt` models over 1-based bins arrive
  this way),
  so Glasgow errors where Gecode and Chuffed solve; XCSP3 aborts on negative
  sizes, limits and loads, where ACE answers (#1347, the same shape as
  `Knapsack`'s #1337).

## What it is

### Semantics

`BinPacking(items, sizes, loads)`, with `n = |items|` items and `m = |loads|`
bins, holds when every `items[i]` is in `0..m−1` and, for every bin `b`,

```
Σ_{i : items[i] = b} sizes[i] = loads[b].
```

`BinPacking(items, sizes, capacities)`, with `m = |capacities|`, holds when
every `items[i]` is in `0..m−1` and `Σ_{i : items[i] = b} sizes[i] ≤
capacities[b]`.

The constructors check only that every size, and every capacity, lies in
`±(2⁶⁰ − 1)` (`innards::require_bounded`, `bin_packing.cc:1716–1727`), and
throw `IntegerOverflow` otherwise. `prepare()` (`bin_packing.cc:1758–1787`)
throws `InvalidProblemDefinitionException` when `|items| ≠ |sizes|`, a size is
negative, there are no bins, an item's initial domain leaves `0..m−1`, a load's
initial lower bound is negative, or a capacity is negative.

- **No items:** every load must be 0 (each row reads `0 = loads[b]`), and the
  capacity form holds whenever no capacity is negative.
- **No bins:** refused, even with no items, where the meaning is "true". The
  MiniZinc redefinitions guard it (`if length(c) = 0 then length(bin) = 0`).
  XCSP3's condition form with an empty `<list>` (invalid XCSP3, which needs
  two items; ACE fails on it too) makes zero bins and aborts on the refusal,
  and the `.scp` reader passes zero bins through to the same uncaught throw:
  `glasgow_scp_solver` aborts.
- **Zero-size items** take a bin and add nothing; their terms are left out of
  the rows.
- **An item that fits no bin** is ordinary: Stage 2 removes each bin from it
  and the domain empties.
- **The bins are numbered from 0.** Front ends with other numbering pass an
  offset and post views (MiniZinc), or create bins from 0 (XCSP3); see the
  table's footnotes.
- **A negative capacity or a constant negative load** is unsatisfiable, but is
  refused rather than failed.
- **A repeated variable** (an item twice, a load that is another load or an
  item) is accepted and means what the rows say. The propagator treats each
  position as independent; see [Robustness and limits](#robustness-and-limits).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `BinPacking`, variable loads | ✓ `fzn_bin_packing_load`[^mznload] | ✓ `<loads>` of variables or constants; `<condition>`[^xcond] | `decompose`[^cpmpy] | ✓ `binpacking … loads` | |
| `BinPacking`, constant capacities | ✓ `fzn_bin_packing_capa`, `fzn_bin_packing`[^mzncapa] | ✓ `<limits>` of constants[^xlim] | `decompose`[^cpmpy] | ✓ `binpacking … capacities` | |
| any form, `var opt` items | `decompose`, then refused[^opt] | n/a | — | — | |
| reified forms | `decompose`[^reif] | n/a | — | — | |
| `<limits>` of variables, `<conditions>` | n/a | `unsupported`[^xuns] | — | — | |

[^mznload]: `minizinc/mznlib/fzn_bin_packing_load.mzn:12–16` redefines the
    standard `fzn_bin_packing_load` as `glasgow_bin_packing_load(load, bin, w,
    min(index_set(load)))`, and `fzn_glasgow.cc:936–943` posts `BinPacking`
    over the views `bin[i] − offset` (`zero_based`, `fzn_glasgow.cc:321–328`),
    so the item domains keep their holes (#803, #817). The standard
    definition also posts `min(index_set(load)) <= bin[i] <= max(...)` and
    `sum(load) = sum(w)`; the redefinition drops both. An item whose domain
    reaches outside the load array's index set, or a load declared with a negative lower bound, then
    throws from `prepare()` and the run ends in `=====ERROR=====` where Gecode
    and Chuffed solve (#1347). Tests: `binpackingloadtest.mzn` (the only one
    of the load form).
[^mzncapa]: `fzn_bin_packing_capa.mzn:23–27` passes `min(index_set(c))` as the
    offset, and `fzn_bin_packing.mzn:11–19` builds a capacity array over
    `lb_array(bin)..ub_array(bin)` with that lower bound as the offset;
    `fzn_glasgow.cc:928–935` posts the capacity form. As for the load form,
    the standard definition's range constraint on `bin[i]` is dropped, so an
    item whose domain reaches outside the capacity array's index set errors
    (#1347); `fzn_bin_packing`
    cannot meet that, since its bins are the items' own range. Tests:
    `binpackingtest.mzn`, `binpackingoffsettest.mzn` (non-1-based capacities
    and the single-capacity form).
[^xcond]: `buildConstraintBinPacking` (`xcsp_glasgow_constraint_solver.cc:700–723`)
    creates a load in `0..Σ sizes` for every bin from 0 up to the largest item
    upper bound (`bin_packing_num_bins`, `:680–690`), posts the load form and
    applies the condition to every load. Bins no item's domain contains get
    the condition too, with load 0, so a condition that rejects 0 answers
    wrongly (#1345). An item domain with a negative value is reported
    unsupported (`:685–686`). The XCSP3 3.2 specification quantifies over the
    bins items take (§4.1.6.4); ACE 2.6 over the union of the domains.
[^xlim]: `:725–748` posts the capacity form for constant `<limits>` and the load
    form over constants for constant `<loads>`; `:750–764` the load form for
    variable `<loads>`. Bins are numbered from 0, with no `startIndex` (the
    parser reads one for every `<binPacking>`, `XMLParserTags.cc:1628–1630`,
    but the manager passes it on only for `<conditions>`,
    `XCSP3Manager.cc:1256`). A negative size, a negative constant limit or
    load, a variable load whose lower bound is negative, or an item domain
    outside `0..|L|−1`, throws from `prepare()` inside
    `solve_with`, which the binary does not catch there, so the process aborts
    with exit 134 (#1347; the same uncaught exception as #1337). Test:
    `xcsp/tests/bin_packing.xml` (constant `<limits>`).
[^xuns]: `:753–754` and `:766–769` call `report_unsupported`; for `<conditions>`
    the parser itself reports the condition malformed first.
[^cpmpy]: `gcspy` binds nothing in this family. CPMpy's upstream GCS
    interface, as copied on 2026-09-23 (`tmp/linear-audit/cpmpy_gcs.py:93–94`,
    `:670–672`), does not list bin packing among its supported globals and
    decomposes it.
[^opt]: Glasgow redefines only the three non-optional predicates. The
    standard `fzn_bin_packing*_opt` decompositions add a dummy bin one past
    the last and call the non-optional predicate over `[b default dummy_bin |
    b in bin]`. MiniZinc represents an absent value by 0, so those variables
    are declared from 0 up to the dummy bin, and `prepare()` refuses the model
    whenever 0 lies outside the bins: every 1-based `var opt` model, under all
    three predicates, on 2.9.7 and 2.10.1 (#1347). Bins indexed from 0, or
    ending at −1, are not affected (the fact-check's 0-based and negative
    models give 17 solutions, as Gecode and Chuffed do).
[^reif]: Glasgow's `mznlib` has no `_reif` predicate, so the standard library's
    reified decomposition is used; it agrees with Gecode by hand.

**Differential checks, all against `86caad24`.** `cake_pb_cp` has no
`binpacking` rule, so no route is chain-checked at all; each was diffed
directly, classifying the status markers (`==========`,
`=====UNSATISFIABLE=====`, `=====ERROR=====`, no marker) and agreeing only on
status and solution set together. Harnesses and reproducers are in
`tmp/fd-bp/bin_packing/fe/`.

- **MiniZinc**, 320 random models (seeds 1 to 8) plus 160 of the load form
  only (seeds 11 to 14), on each of 2.9.7 and 2.10.1, against each bundle's
  Gecode and Chuffed (6.3.0 and 0.13.2 with 2.9.7, 6.4.0 and 0.14.0 with
  2.10.1; `mzndiff.py`): `bin_packing`, `bin_packing_capa`, `bin_packing_load`
  as a predicate and as a function, item and bin index sets starting at 1, 0, 3
  and −2, 0 to 5 items, 0 to 4 bins, holey item domains and ones reaching
  outside the bins, a fixed item, a repeated item, zero sizes, an item that fits no
  bin, capacity 0, negative and fixed loads, and a load that is an item
  variable. The two versions give identical results. **No wrong answer.** 413
  agree (275 complete enumerations and 138 unsatisfiable). The 50 disagreements are all Glasgow
  `=====ERROR=====` where both others answer: 13 item domains reaching
  outside the bins and 37 negative load lower bounds (five of them a load that is also an
  item variable declared below 0). The other 17: in 16, Gecode errors on
  `bin_packing` with no items or an empty capacity array (its own library takes
  `lb_array` of an empty array) and Glasgow matches Chuffed; in one (no items,
  no bins), Gecode says unsatisfiable and Glasgow and Chuffed find the one
  solution, which is right.
- **XCSP3**, 400 random instances against ACE 2.6 and a brute force
  (`xcspdiff.py`, seeds 1 to 8): 214 agree with ACE, and 18 more where ACE
  itself fails agree with the brute force. **7 are wrong answers**, all in the
  condition form, all against both ACE and the brute force (#1345). ACE is
  not ground truth on its own: a fact-check found it answering wrongly on
  condition-form instances with zero-size items (four, none among these 400),
  so every disagreement was settled by the brute force. 54 abort where ACE answers (negative sizes 33,
  limits 10, loads 11) and 64 abort where ACE fails too (63 item domains
  outside `0..|L|−1`, one negative size in the condition form); 31 are `UNSUPPORTED` where ACE answers (a negative bin value in
  the condition form, 14; variable `<limits>`, 17). One `<loads>` instance
  with a non-zero constant load on a bin no item can take is unsatisfiable to
  Glasgow and satisfiable to ACE, which matches the specification's literal
  reading; it is not counted as wrong. 61 agreeing instances differ from that
  literal reading in the same way, so both solvers read "every bin".
- **`.scp`:** the reader (`scp_reader.cc:881–904`) posts the default
  constraint, with `consistency::GAC`, `PerCall` and no Shaw: none of the
  three choices is part of the `.scp`, and `constraint_type()` is
  `binpacking` whatever they are (`bin_packing.cc:2025–2028`).
  `scp_reader_test` enumerates both forms (`:1640`) and round-trips them
  (`:1741`). Proofs through `glasgow_scp_solver` verify (workflow 1);
  `cake_pb_cp` prints "unsupported constraint: binpacking" and exits 0. See
  [Cake conformity](#cake-conformity).

### Options

**`with_consistency(BinPackingConsistency)`**, where `BinPackingConsistency =
std::variant<consistency::GAC, consistency::BC>` (`bin_packing.hh:29`).
Default `consistency::GAC`.

- `consistency::GAC` installs Stages 2 and 3 (and 4 with Shaw). The header
  calls it "per-bin GAC"; what it reaches is per-bin GAC on the items' bin
  values and on the loads, short of committing items (rules 7 to 10, #1346).
  It also builds the static diagrams in `prepare()`, and with proofs the
  initialiser writes their flags.
- `consistency::BC` installs Stage 2 alone (and 4 with Shaw): bounds(R) on each
  bin's row, over the load and each item's membership in the bin (rules 1 to
  6). The loads are then watched for bounds only.
- **It changes the propagation, not the model.** The OPB is the same rows
  either way. In the constant-capacity form the two search the same tree,
  because Stage 2 is already per-bin GAC there (for distinct item variables;
  a repeated one loses strength under either consistency) and so Stage 3
  cannot change the fixpoint (and the random sweep's node and solution counts agree on 400
  of 400 pairs, see [Tests](#tests)); `GAC` only costs more (#1349).

**`with_proof_strategy(BinPackingProofStrategy)`**, where
`BinPackingProofStrategy = std::variant<proof_strategy::PerCall,
proof_strategy::Upfront>` (`bin_packing.hh:43`). Default `PerCall`.

- **It changes the proof and the Stage 3 code path, not the model or the
  fixpoint.** `PerCall` runs `run_stage3_for_bin` and `Upfront` runs
  `propagate_bin`; they reach the same fixpoint, so the trees agree (node
  counts on 800 of 800 random pairs, plus the suite's `check_strategies_agree`
  on every case). They do not always draw the same inferences within a call:
  in the capacity form `Upfront`'s sweep can draw a call early what Stage 2
  draws next (its `a` lines differ from `PerCall`'s in 221 of 3,000 random
  capacity-form instances in the re-check, and it makes fewer propagator calls
  on bench instances 1, 5 and 6). Nor do they
  cost the same with proofs off ([CPU
  performance](#cpu-performance), and [Interval
  efficiency](#interval-efficiency) for a large size). Without `GAC` there is
  no Stage 3 and the option does nothing. All assertions carry the same hint
  name, `binpacking`, under either strategy.
- **Why `PerCall` is the default:** its proofs are smaller and faster to check
  on every instance measured ([Proof performance](#proof-performance)), which
  [`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md)
  (on main at `86caad24`, after #995) explains: almost nothing it writes is per call, so there is nothing for the
  upfront scaffold to displace, and the scaffold taxes every RUP.

**`with_cardinality_reasoning(BinPackingCardinality)`**, where
`BinPackingCardinality = std::variant<bin_packing::NoCardinality,
bin_packing::Shaw>` (`bin_packing.hh:83`). Default `NoCardinality`.

- `bin_packing::Shaw` adds Stage 4 (rules 11 and 12), under either consistency.
  It changes the propagation, not the model: no new rows, flags or `Top` lines.
- **Why it is off:** on the in-tree benchmark it cuts the pigeonhole instances
  from 4,485 nodes to one, and on the four enumerations, where it cannot cut
  anything, it costs 1.27 to 1.37 times the instructions under `GAC` and 1.9
  to 2.0 times under `BC` ([CPU performance](#cpu-performance);
  `dev_docs/bin-packing.md` gives 17 to 24% of the wall time, from the #209
  era, measured elsewhere).

There is no `consistency::Auto` and no `consistency::Dynamic`.

### Variable kinds and views

Items may be plain variables, constants, or views of either sign: every stage
reads an item only through `in_domain(item, b)` and `optional_single_value`,
and the rows are written over each item's `[item = b]` literal, which the
tracker spells over the view. MiniZinc hands every item over as a view
(`bin[i] − offset`). Loads may be plain variables, views or constants, with and
without proofs, at every assertion level except where #1210's generic
`Links` defect applies (see [Proof performance](#proof-performance)):

- `add_bound_p_term` (`bin_packing.cc:332–337`) cites a view load's bound over
  the view's own bits and skips a constant, whose row has folded it into its
  degree (#1195);
- `define_proof_model` registers every view load before writing any row, so
  an item that is the same view as a later bin's load is spelled one way
  throughout (#1195, as #1197 did for `GlobalCardinality`;
  `bin_packing.cc:1895–1910`). A view first registered by a
  constraint posted after this one is #1200's case, which the
  `view_mixed_late` lane covers;
- Stage 4 counts a bin's ceiling only when its load is a plain variable (or in
  the capacity form), decided from the operand's kind so that the inferences
  are the same with and without proofs (`bin_contribution`, `:1420–1423`;
  `prepare`, `:1805–1812`); a constant or view load's bin contributes zero.

The 800 of the audit's 1,600 random enumerations that draw items and loads
from plain variables, `x + c` views and constants all verify
([Tests](#tests)); negated views come only from the suite's view lanes and its
negated-view load case.

### Reification

None. MiniZinc's reified forms decompose. A reified form is not wanted until a
model needs one.

### Relation to other families

- **Decomposes into it:** nothing in the solver. MiniZinc's three predicates
  and XCSP3's `<binPacking>` map onto it.
- **Child constraints:** none. XCSP3's condition form posts comparison or `In`
  constraints on the auxiliary loads it creates; they are not children.
- **Shares code:** nothing exported, and nothing called from elsewhere. The
  `Upfront` Stage 3 is a `k = 1` **copy** of `Knapsack`'s upfront diagram
  (`build_fwd_dag`, `compute_phantoms`, `emit_bin_scaffolding`,
  `propagate_bin`; the comments say "mirrors knapsack"), adapted rather than
  called: one partial-sum coordinate, the two branches "in bin `b`" and "not
  in bin `b`" instead of an item's values, and the load as the total.
  [`knapsack.md`](knapsack.md) owns the original; this document owns the copy
  and cites `knapsack.md` for what is identical. Two of `Knapsack`'s defects
  are in the copy: the interior-value pass (#1340) and the stranded
  temporary level on failure ([Proof-time state](#proof-time-state)). The
  `proof_strategy` tags are shared with `Regular` and `Knapsack`. `PerCall`
  is this family's own and shares nothing with `Knapsack`'s `PerCall`.
- **Presolvers:** none reads or writes a `BinPacking`.
- **Relation to `knapsack`, `mdd` and `regular`:** the same layered-diagram
  proof shape (state flags, transitions, dead states).
  [`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md)
  compares the strategies across the four families; #200 is the unification.
  A `Knapsack` with one row over 0/1 items is one bin's diagram, but
  `BinPacking`'s items are bin indices, so the two do not share variables'
  meanings, and nothing here posts a `Knapsack`.
- **Relation to `linear`:** each bin's row is a linear constraint over the
  items' equality literals; the family posts no `LinearEquality`.
- **Relation to `counting`:** the cardinality reasoning of Schaus and
  colleagues (a count of items per bin, kept consistent with a global
  cardinality constraint) has no counterpart here; Stage 4 counts items above
  a threshold inside one `pol` instead, and posts no `Count` or
  `GlobalCardinality`.

## The proof model

### OPB encoding

For each bin `b`, in the variable-load form:

```
Σ_i sizes[i] · [items[i] = b] − BinEnc(loads[b]) ≥ 0     @c[id][<b>_ge]
Σ_i sizes[i] · [items[i] = b] − BinEnc(loads[b]) ≤ 0     @c[id][<b>_le]
```

and in the constant-capacity form:

```
Σ_i sizes[i] · [items[i] = b] ≤ capacities[b]           @c[id][<b>_le]
```

written by `model.add_labelled_constraint` (`bin_packing.cc:1912–1932`). The
term for item `i` is its equality literal at `b`, so a row has one term per
item, not one per bit. A constant item's term is a constant and is folded into
the degree; a zero size leaves the term out; a constant load is folded into
the degree (it has no bits). It is **definitional** given what `prepare()`
refuses: the rows say only that each bin's sizes sum to its load, or stay
within its capacity. The rows alone do not say that an item is in some bin; an
item domain inside `0..m−1` says it, which is why `prepare()` refuses one
reaching outside that range rather than prune it. Nothing else is in the OPB; every flag lives in the
proof.

**Size: `m` rows (capacities) or `2m` (loads).** Row `b` has one term per
non-constant item with a non-zero size, **including items whose domain does
not contain `b`** (their literal is never true, but the term is written), plus
`bits(loads[b]) = ⌈log₂(ub(loads[b]) + 1)⌉` terms for the load in the load form.
So `m · n′` terms in the capacity form and `2m · (n′ + bits)` in the load form,
for `n′` such items: linear in `n` and `m`, logarithmic in the loads' widths,
independent of the sizes' magnitudes. The equality literals each row names
are defined in the OPB too, through the shared literal layer: two rows for
`[x = b]`, over its two order atoms `x ≥ b` and `x ≥ b + 1`, and two for each
order atom, over `bits(x) + 1` terms, the boundary atoms `x ≥ lb` and `x ≥ ub
+ 1` included (so an item over `0..2` gets 14 rows), for each item `x` (none
for 0/1 items, whose literal is their bit). A zero-size item has no term but
still gets its literal definitions written (benign). Measured
(`size/bpsize.cc`, seed 1): ten items, sizes 1 to 5, three bins:
3 rows and 30 terms (capacities), 6 rows and 84 terms (loads), plus 140
literal-definition rows; with two bins, no literal-definition rows.

### Labels

`@c[<id>][<b>_le]` and, in the load form, `@c[<id>][<b>_ge]` are load-bearing:
the `DagBridge` keeps their `ProofLine`s (`opb_lines`, `:1703–1706`) and Stage
3's pols cite them (the terminal lines under `PerCall`; the cap-exceeded,
lower-bound, interior-hole and terminal pols under `Upfront`), as do Stage 4's
pols. Stage 2's RUPs reach the rows by unit propagation and cite nothing. The
code calls the labels internal (`:1891–1892`): no cake rule reads them.

### Cake conformity

None. `cake_pb_cp` has no `binpacking` rule ("unsupported constraint:
binpacking", exit status 0), `verified_encodings/scp_cases` has no
`binpacking` case, and so no chain test covers this family. The proofs are
checked against the solver's own OPB only (workflow 1), where they verify. The
`.scp` round-trips (`scp_reader_test.cc:1741`).

### Proof-time state

- **At the root, with `consistency::GAC`** (the initialiser,
  `bin_packing.cc:1962–1970`, only at `AssertionLevel::Off`): for every node
  `(b, i, w)` of every bin's static diagram, three flags at `ProofLevel::Top`,
  `bpup_<b>_<i>_<w>` and `bpdn_<b>_<i>_<w>` reifying that the sizes of the
  first `i` items in bin `b` sum to at least, or at most, `w`, and
  `bpat_<b>_<i>_<w>` reifying their conjunction; each is defined by
  `redundance` with two reification lines (`emit_bin_scaffolding`,
  `:391–404`). That is all `PerCall` writes at the root. `Upfront` adds, at
  `Top`, the phantom flags `bpphantom_<b>_<i>_<w>`, the forward chains, the
  layer-0 unit, the per-state implications and layer at-least-ones, the
  backward chains and the phantom closures (`:423–575`), `Knapsack`'s scaffold
  at `k = 1` ([`knapsack.md`](knapsack.md), Proof-time state, and
  [`dev_docs/knapsack.md`](../knapsack.md), "Top-level scaffolding"). With
  `consistency::BC` nothing is written at the root.
- **During search, `PerCall`:** each Stage 3 justification writes, at `Top`
  and at most once per proof (`PerCallTopLines`, `:153–158`), the forward
  chain of each edge it needs (two `pol`s and three RUPs, `emit_forward_chain`,
  `:352–367`), the split of each node into its two successors (one RUP), and
  each reachable terminal's load in order atoms (two `pol`s and two RUPs);
  then, at `Temporary`, one RUP under the reason ruling out each reachable
  terminal whose load falls in a hole of the load's domain (`:969–978`). The
  temporary lines are the inference tracker's level and are closed by it.
- **During search, `Upfront`:** as `Knapsack`'s `Upfront`: `¬S` lemmas for
  dead nodes and `¬g_dn` lemmas for terminals below the load's lower bound, at
  `ProofLevel::Current`, recorded in the backtrackable `DeadCache` so that a
  subtree writes each at most once (`:177–181`, `:1872–1874`), plus the
  cap-exceeded, lower-bound, interior-hole and terminal `pol`s and RUPs at
  `Temporary`.
- **During search, Stages 2 and 4:** Stage 2 writes nothing but its
  conclusions. Stage 4 writes, at `Temporary` under the tracker's level, per
  bin whose row it uses one `pol`, preceded by one weakening RUP when some
  item is dropped from the row, one trivially true
  RUP per other bin with a kept item, and the summing `pol`.
- **Naming:** the flag names above encode bin, layer and partial sum, and are
  how an external tool finds the scaffolding.
- **In the OPB versus the proof:** every auxiliary is a proof-only flag
  introduced by `redundance`, each a reification of a partial sum of the
  items' equality literals, so on a solution unit propagation determines every
  one.
- **Dangling proof-only vectors:** none. `opb_lines` is filled by
  `define_proof_model` at every assertion level and read only on the `Off`
  paths; the flag tables are empty at every assertion level above `Off`, and
  every reader is behind the
  `emitting` test or the tracker's `Off` branch.
- **`Upfront` strands its temporary lines when a call fails.** `propagate_bin`
  takes `temporary_proof_level()` on entry (`:622–624`) and forgets it on the
  way out (`:841–842`), but `contradiction()` at `:762` is `[[noreturn]]`, so
  the forget at `:763–764` never runs, and an `infer_all` or `infer_not_equal`
  that fails (`:801`, `:838`) unwinds past `:842` the same way. This is
  `Knapsack`'s defect, by code reading: not unsound, since the lines are swept
  by the next forget of that level (normally the next propagator call at the
  same depth), but it breaks the rule `inference_tracker.hh:700–715` states,
  that the code which opens a temporary level closes it, and leaves a failing
  call's lines live until then. `PerCall` and Stage 4 do not open a level of
  their own; the tracker's `JustifyExplicitly` path closes its level on a
  failure too.

## The implementation

### Initialisation and global data

**`prepare()`** validates (above). With `consistency::GAC` or Shaw it
allocates the `DagBridge` (`:1795–1799`), which the propagator and the
initialiser share; each search's clone of the constraint prepares its own. With Shaw it sizes Stage 4's scratch and computes the
threshold list (1 and every distinct size above 1, largest first) and the
items in decreasing size (`:1801–1839`): `O(n log n)`.

With `consistency::GAC` it builds, for each bin, the **static diagram**: the
partial sums of the sizes of the first `i` items that can be in the bin,
over the **initial** item domains, not intersected with the load's bounds or
the capacity (`build_fwd_dag`, `:205–264`), so that the cap-exceeded `pol` has
a flag to chain against, as in `Knapsack` (`dev_docs/knapsack.md`, "Static
reduction"). Layer `i` has at most `min(2^i, Σ_{j<i} sizes[j] + 1)` nodes; it
costs a `std::set` insertion per node and branch, plus two binary searches
per node for the precomputed successor positions (exclude and include,
`:258–260`), and a backward pass for the
phantoms (`compute_phantoms`, `:272–313`), which `PerCall` never uses but
computes anyway. A partial sum that does not fit in 64 bits throws
`IntegerOverflow` here (`build_fwd_dag`, `:226–228`, when `include_weight`
returns nothing). The diagrams are held
for the whole search, with or without a proof, and in the constant-capacity
form without ever changing the fixpoint (#1349). Stage 3's per-bin scratch is sized here so that the
hot path never allocates (#514). Measured root calls, proofs off
(`size/grid.txt`, one core): ten items of sizes 1 to 5 over two bins, 0.3 ms;
forty items of sizes 1 to 100 over ten bins, 0.23 s under `PerCall` and 0.25
s under `Upfront`.

**With a proof,** the initialiser writes `6 × Σ_b Σ_i |DAG_b[i]|` `red` lines
under `PerCall` (each reification over up to `i` equality literals), and
`Upfront`'s whole scaffold: a root-only proof is 2,318 lines (310 KB, 2,214
of them flag definitions) under `PerCall` and 19,661 (1.33 MB) under `Upfront`
for ten items of sizes 1 to 5 over three bins in the load form
(`size/bpsize.cc`, seed 1; `PerCall`'s is the same in the capacity form,
`Upfront`'s 19,499 lines and 1.29 MB), and grows to 1.86 M
lines (693 MB) under `PerCall` for forty items of sizes up to 100 over ten bins
in the capacity form, where `Upfront` passed the 4 GB file cap
(`size/grid.txt`). See [Proof performance](#proof-performance).

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| Stage 3 flags initialiser | — | — | none (scaffolding) | `consistency::GAC`, `AssertionLevel::Off`; `Upfront` adds the full scaffold | n/a | n/a |
| `BinPacking` (Stages 2, 4, 3 in that order) | `on_change` on every item; on every load `on_change` under `GAC`, `on_bounds` under `BC` | derived: **every item; every load under `GAC`, none under `BC`** | 1–6; 11–12 with Shaw; 7–10 under `GAC` | always | not claimed | never |

One propagator runs every stage (`:1991–2022`): Stage 2 for every bin, then
Stage 4, then Stage 3 for every bin, each reading the state the previous ones
left. It returns `PropagatorState::Enable`.

**The triggers tell the truth.** Every stage reads an item's domain as "can
be in bin `b`" for each `b` (`in_domain`), so a hole in an item, which is a bin
removed, changes Stage 2's partition and Stage 3's edges. Stage 3 drops a
terminal whose load falls in a hole of the load's domain, under either
strategy (#966 made `Upfront` wake on it, and #995 made `PerCall` read the
load at all); Stages 2 and 4 read only a load's bounds, which is why `BC`
watches them `on_bounds`.

**Idempotence.** Not claimed, and by reading one call need not reach a
fixpoint: Stage 2 visits the bins once, in order, with each bin's floor and ceiling computed before its inferences, so a
prune in a later bin that fixes an item changes an earlier bin's floor
without that bin being revisited (under `GAC` Stage 3 then often catches it in
the same call; under `BC` only the next call does). The framework re-runs the
propagator on its own changes, so the fixpoint is reached.

### Mutable state and incrementality

- **Stage 2:** none; one pass over items and bins per call.
- **Stage 3, `PerCall`:** per bin, position-indexed forward and backward
  reachability bitmaps over the static diagram, the per-item "can be in" and
  "can be elsewhere" flags they were built from, and the load's intervals the
  accepted terminals were computed from (`Stage3Scratch`, `:123–136`). Not
  backtrackable, and needing no restore: each call diffs the current flags
  against the cached ones, recomputes the forward pass from the first changed
  layer and the backward pass down from the last, and recomputes the terminal
  acceptance only when the load's domain changed; a backtrack is seen as a
  change like any other. A bin whose inputs did not change and whose last
  sweep drew nothing is skipped (`:1138–1144`). The bitmaps and the
  incremental recompute came from #514's allocation problem. The `Top` lines
  already written are recorded in `PerCallTopLines`, also never restored,
  since `Top` lines persist.
- **Stage 3, `Upfront`:** the static diagram and flag tables (immutable) and
  `DeadCache` (backtrackable). Each call rebuilds a `list<map<long long,
  LiveNode>>` per bin with predecessor vectors, so it allocates on every call,
  where `PerCall` allocates only when a bin infers (its inference lists and
  reason).
- **Stage 4:** per-call scratch sized once in `prepare()`; the per-bin totals
  are folded once per call across the descending threshold list rather than
  once per threshold (`:1548–1611`).

### Interior values and optional pruning

**Offers.** `None.` No stage installs an optional-interior-pruning pair, and
removing an item's interior values (bins) is the whole of what the family
does.

**Observes.** **Holes in every item**, always, and **holes in every load under
`consistency::GAC`**, as the inventory says; a `BinPacking` over a variable is
therefore a reason for another family's optional interior pruning on it to
stay on. **Under `consistency::BC` the loads' vocabulary is bounds**: no stage
that runs reads a load's interior, and its triggers say so. The load
triggers' history is #966 (the `Upfront` sweep read holes it watched only for
bounds, fixed by watching `on_change`) and #995 (`PerCall` read no load at all,
fixed by reading its domain, under the same `on_change` trigger).

### Robustness and limits

**Unbounded domains.** Items cannot be wide: `prepare()` refuses a domain
outside `0..m−1`. A load can be declared wide at no cost, because Stage 2 cuts
it to `[floor, ceiling]` before Stage 3 runs (three unit items against loads in
`0..10⁹`: 0.1 ms under either strategy, `size/bpwide.cc`). What can be wide is
the reachable range itself, when sizes are large; see [Interval
efficiency](#interval-efficiency).

**Negative values and zero.** Zero sizes, zero capacities, loads at 0 and no
items are ordinary. Negative sizes, capacities and load lower bounds are
refused in `prepare()`; the diagram's monotone partial sums and Stage 2's
floor and ceiling rely on non-negative sizes, so that refusal is load-bearing,
and the load and capacity refusals are a choice (a negative capacity or
constant load is simply unsatisfiable, and a load's negative values are
unreachable). The front ends pass such shapes through (#1347).

**Degenerate shapes.**

- *No items:* every load is fixed at 0 by Stage 2 (the ceiling is 0). Tested by
  the brute force and the sweeps (`n = 0` instances), not in the suite.
- *One bin:* every item is fixed at 0 by its domain; the load is the total.
- *Zero-size items:* handled; no term in the rows.
- ***A repeated variable loses strength, never a solution.*** Each position is
  treated as an independent item, and a load that is also an item or another
  load as independent too. Root brute force with repeats
  (`gac/bpalias.cc`: item positions repeating a variable, a load that is an
  item's variable or an earlier load): no unsound root in 20,000 instances
  (both forms and both strategies, plus a Shaw and a `BC` run), and per-bin
  GAC lost on 92 to 116 instances of 2,000 per seed in the capacity form. The smallest: one variable `x ∈ {0,
  2}` at both item positions, sizes 1 and 2, capacities `3, 1, 2`, leaves `x ∈
  {0, 2}`, where `x = 2` puts 3 in a bin of capacity 2.
- *Constant or view items and loads:* fine, with and without proofs (#1192,
  #1195 fixed the proof side).

**Overflow.** Sizes and capacities are checked against `±(2⁶⁰ − 1)` at
construction, and a load's bounds lie within twice that (views). Stage 2's
floor and ceiling saturate at `4 × (2⁶⁰ − 1)`, past any bound plus any size, so
every comparison comes out as on the true sums (`stage2_saturation`, `:1220`).
Stage 3's static diagram holds exact partial sums and throws `IntegerOverflow`
when one does not fit in 64 bits, which the integer-range policy allows an
arithmetic constraint ([`integer-ranges.md`](../integer-ranges.md), on main
at `86caad24`); with `consistency::BC` the same instance answers. Stage 4's
sums are checked (`add4`, `sub4`, `mul4`): an overflow in a threshold's
`DELTA` or shaving arithmetic skips that threshold or candidate, and one in the
per-bin totals ends Stage 4 for the call (`:1565–1566`, `:1609–1610`), since
the totals only grow; either way it costs strength only, and the same with and
without proofs (`:1356–1389`). **With a proof, the rows themselves are
fine**: a row whose coefficients sum past `2⁶³` is written and verifies
(the fact-check's runs of `bin_packing_test`'s "star" and "pinned" shapes,
nine items of size `2⁶⁰ − 1`, under `BC` in both forms, with and without
Shaw: all verify). Under `GAC` they throw from Stage 3: the "star" from
`build_fwd_dag`, with or without a proof; the "pinned" shape only with a
proof at `AssertionLevel::Off`, from the `Top` flags' reification
(`names_and_ids_tracker.cc:3011`, "cannot size the reification constant for
a half-reified row"), since above `Off` the initialiser writes no flags and
the re-check's runs at every assertion level answer its two solutions; except
that under `Upfront` in the load form "pinned" does not finish at all, with
or without a proof (600 s, twice; the interior-value pass of #1340 over
loads that Stage 2 leaves at `0..2⁶⁰ − 1`). `bin_packing_test`'s edge-of-range
cases pin Stage 2's saturation, and, with Shaw, Stage 4's skip on the two
items; they run "star" only in the capacity form under `BC` with proofs off,
and skip "pinned" and "star" whenever proofs are on, so neither `GAC` throw is
exercised. The test's comment (`bin_packing_test.cc:160–164`) gets the
mechanism wrong: it says the two shapes' rows cannot be written, but the rows
are written and verify (under `BC`); what throws is `GAC`'s Stage 3, its
diagram for "star" and its `Top` flags at `Off` for "pinned".

### Interval efficiency

**Fine at any declared width; not fine at any reachable width under
`Upfront`.** The family's work is per item, per bin and per diagram node, and
a node is a reachable partial sum.

1. **The propagation side.**
   - *Stage 2,* per item per bin (`in_domain`, `optional_single_value`):
     bounded by the constraint's size, since an item's domain is a subset of
     the bins.
   - *Stage 3's diagrams* (both strategies): per node and branch, nodes being
     distinct reachable partial sums, so bounded by `min(2^i, Σ sizes + 1)`
     per layer and independent of the loads' declared widths. A genuine
     support computation with no interval structure to exploit.
   - *`PerCall`'s load cut:* the accepted terminals are found by walking the
     sorted terminals against the load's intervals (`copy_of_values(...)
     .for_each_interval`, `:1044–1055`), and each gap between surviving
     terminals that the domain reaches into is removed with one
     `domain_intersects_with` test and one `not_in_range` literal
     (`:1186–1205`). One step per terminal plus one per run.
   - *`Upfront`'s interior-value pass* (`propagate_bin`, `:778–782`): every
     value of the load's domain (`each_value_immutable`), and for each value in
     `(lo, hi]` a `none_of` over every surviving terminal: `|dom(loads[b])| +
     |dom(loads[b]) ∩ (lo, hi]| × |terminal|` per bin per call. Stage 2 has
     already cut the load to `[floor, ceiling]`, so the first term is the
     reachable range, which is wide only when a size is large: two items of
     sizes 1 and `W` over two bins take 0.57 s, 6.4 s and 60.2 s in the root
     call at `W = 10⁶, 10⁷, 10⁸` under `Upfront` and about 0.1 ms under
     `PerCall` (one cold first run took about 4 ms). The second term is quadratic: `k` items of sizes `1, 2, 4, …,
     2^(k−1)` (every value a terminal) take 0.035, 0.48 and 7.76 s at `k = 10,
     12, 14` under `Upfront`, against 0.0066, 0.031 and 0.165 s under
     `PerCall` (`size/bpwide.cc`, one core, proofs off). This is #1340's loop,
     confirmed for the copy (commented on #1340). Its lambdas also take `pair<long long,
     LiveNode>` by `const &` where the map holds `pair<const long long,
     LiveNode>`, so each comparison copies an entry and its predecessor vector
     (`:771`, `:780`).
   - *Stage 4,* per item per bin to read the domains, per item per threshold,
     and per bin per shaving candidate: bounded by `n`, `m` and the number of
     distinct sizes.
   Outside `Upfront`'s pass, nothing walks a load's values.
2. **The reason side.** Stage 2's reasons are one literal per decided item
   plus one load bound, assembled only when `want_reasons()` (`:1231`).
   `PerCall` Stage 3's reason is per bin: one literal per item whose
   membership in the bin is decided, plus `generic_reason` of the load, which
   is one literal per run; it is materialised **eagerly and unguarded**, with
   proofs off too, whenever a bin infers (`:869–879`), which is `O(n + runs)`.
   `Upfront` Stage 3 and Stage 4 share one lazy `generic_reason` over every
   item and, under `Upfront` in the load form, every load (`:1981–1984`):
   one literal per bound or run of every variable in the constraint, built
   only by a materialising tracker. Stage 4 adds every bin's load upper bound
   (`reason_with_loads`, `:1574–1581`), built unguarded per inference, `O(m)`.
3. **The proof side.** Stage 3's lines are per node or per edge (flags,
   chains, splits, dead-node lemmas), so the proof is as wide as the diagrams,
   which is as wide as the reachable sums; the per-value ban does not extend to
   what a proof emits, and here the proof follows the algorithm. `PerCall`
   writes its gap cuts as range literals (`i[l][in4_5]`), `Upfront` its hole
   removals one value at a time (`i[l][eq4]`, `i[l][eq5]`): the form is chosen
   by the strategy, not by a width test, but both are bounded by the
   terminals, since every removed value lies between two reachable sums.
4. **The audit lane.** One row, `BinPacking`, pinned `Clean`
   (`large_domain_audit_test.cc:779–782`): three 0/1 items of size 1 and two
   loads in `0..10⁹`, default `GAC` and `PerCall`, proofs off. It is `Clean`
   because the sizes are unit, so Stage 2 cuts the loads to `0..3` before
   Stage 3 runs, and it would be `Clean` under `Upfront` too (0.1 ms; not run
   with the guard build), not because it runs `PerCall` (#1340's body says
   otherwise; this audit's comment there corrects it). It does not vary the strategy, the sizes
   (a large size is what makes `Upfront` wide),
   the capacity form, Shaw, holes, or proofs, and the family has no row in
   `"Large domain proof sizes"`. The `Upfront` hazard above is unprobed by the
   lane. (Open PR #1302 would add wide-declaration rows for index-valued
   positions; `BinPacking`'s items are refused if declared wide, which it
   records.)

## Inference catalogue

Twelve rules: six from Stage 2, which always runs; four from Stage 3, under
`consistency::GAC`, each under either proof strategy; and two from Stage 4,
under `bin_packing::Shaw`. Stage 2's rules are `infer_*` or `contradiction()`
with `JustifyUsingRUP`; Stage 3's under `PerCall` are one `infer_all` (or a
`contradiction()`) per bin with `JustifyExplicitly` and `ThenRUP::Yes`, and
under `Upfront` an `infer_all` for the load and one `infer_not_equal` per
prune, with `JustifyUsingRUP` after the strategy's own lines; Stage 4's are
`JustifyExplicitly` with `ThenRUP::Yes`. At an assertion level no stage writes
anything but the assertions: the initialiser returns early, `PerCall`'s
justifications are not called, and `Upfront`'s `emitting` is false.

Facts that hold for every rule.

**One hint for everything.** `hints::BinPacking` (`hints.hh`), hint name
`binpacking`, carrying only `originator`, a `ConstraintID`. It names neither
the stage nor the strategy nor the bin. A reconstructor learns the bin from
the conclusion (a load literal names its bin; an item literal `items[i] = b`
or `≠ b` names `b` by its value, and a 0/1 item's literal is its bit), and the
stage only from which procedure succeeds.

**Every assertion carries its reason.** Checked, not assumed: at
`AssertionLevel::Inferences`, 8 configurations (covering both strategies,
both consistencies, Shaw on and off, and both forms) × 60 random seeds,
enumerating every solution (`asrt/falsify/check.py`): none of 16,026
`binpacking` assertions is falsified by a solution logged in the same proof.
No rule asserts a bare unit that is not a consequence of the model; the bare
units that do occur (a ceiling with nothing excluded, below) are.

**The reasons, by stage.** Stage 2: every decided item's literal for the bin
(every item fixed in it, or every item excluded from it, zero sizes included,
whether or not the bound needs it), plus at most one load bound. `PerCall` Stage 3: for bin `b`, `items[i] ≠ b` for
each item that cannot be in it, `items[i] = b` for each that must, and the
load's `generic_reason` (bounds and one literal per hole run), built at
`:869–879`. `Upfront` Stage 3 and Stage 4: the shared `generic_reason` over
every item's bounds and holes, plus every load's in the `Upfront` load form;
Stage 4 adds `loads[c] ≤ ub` for every bin. That one is far from minimal, and
always names a 0/1 item's always-true bounds, as #1070 records for `Knapsack`.

**Stage 3's procedure is published; `PerCall`'s arrangement of it is ours.**
Trick's dynamic programme, certified by the method of Demirović, McCreesh,
McIlree, Nordström, Oertel and Sidorov (*Pseudo-Boolean Reasoning About States
and Transitions to Certify Dynamic Programming and Decision Diagram
Algorithms*, CP 2024, LIPIcs 307, 9:1–9:21, §3.3) and McIlree's thesis
(§5.2.2): partial-sum and state flags by `redundance` (the thesis's
Theorem 2.4), each
transition from two reification halves by a `pol` whose partial sums cancel
exactly, then by RUP. Preconditions: the same item order on both sides of a
transition, and non-negative sizes, so that a partial sum never comes back
down. `Upfront` is that method in `Knapsack`'s upfront arrangement
([`knapsack.md`](knapsack.md), rules 3 to 7). **`PerCall` writes no layer
at-least-ones, no backward chains and no dead-state lemmas**: it writes, at
`Top` and once each, the forward chains and splits of the nodes an inference
needs and the terminals' load lines, and leaves the rest to the RUP. Why the
RUP closes: negate the conclusion; unit propagation marks a terminal as not
the state when the reason's load literals rule out its load (through the
terminal's two order-atom lines), or, for a load inside a hole, when the
explicit refutation says so; a node whose admissible successors are all not
the state is then not the state either (through its split, or through its one
admissible chain when the reason decides the item); and the root's state is
forced by its own definition, so the walk ends in a conflict. A prune starts
the walk from the pruned item's include chains, which the negated prune makes
the only way on. That argument is the design note's and the code's
(`:881–906`); it is not a published procedure, and the mutation lanes that
show its pieces load-bearing were run by hand, not kept (`dev_docs/bin-packing.md`
on main at `86caad24`, "Mutation-tested"; the note in this document's base
predates that paragraph).

**Offline reconstructibility, by stage.** Stage 2: `offline`, plain RUP
against the conclusion's bin's rows. Stage 3: `offline`. The reason gives,
for the bin the conclusion names, every item's membership exactly and the
load's domain exactly (under `PerCall` that is all it gives; under `Upfront`
it gives every variable's domain); that fixes the per-bin diagram, its
terminals and its dead nodes, and the procedure (forward pass, terminal
filter, backward pass, then the derivation above or `Knapsack`'s) succeeds
whenever the clause follows from bin `b`'s constraint and the reason, which
every Stage 3 clause does. Nothing is chosen. For an `Upfront` contradiction,
whose reason names every variable, the procedure runs every bin's diagram, a
fixed enumeration, one of which fails. Stage 4: `offline`, by the same kind
of argument, under rules 11 and 12. The one hint name does not tell a
reconstructor which stage produced a clause, for any rule; it runs the fixed
procedures in turn, and one is guaranteed to succeed.

### Rule: load-floor

(Rule 1, Stage 2.)

- **Infers** — `loads[b] ≥ floor_b`, the sum of the sizes of the items fixed
  in bin `b`.
- **Fires when** — the load form, every call, for each bin whose lower bound is
  below the floor (`bin_packing.cc:1268–1271`).
- **Strength** — `partial` alone: the load's lower bound. With rules 2 to 4,
  `bounds(R)` on each bin's row, over the load and each item's membership in
  the bin as a 0/1 term: all 8,377 root fixpoints of 16,000 random load-form
  instances (`gac/bpcheck.cc`, both consistencies, plain and with views,
  seeds 1 and 2; the rest fail at the root) are bounds(R) fixpoints of every
  bin's row. Not `bounds(Z)` per bin: under
  `consistency::BC`, 304 load bounds in 2,000 instances (seed 1) have no
  support in their bin's constraint.
- **Algorithm** — one pass over the items for the bin, `O(n)`.
- **Why it is true** — every item fixed in the bin contributes its size, and
  every other term is non-negative.
- **Proof technique** — `RUP` against the `_le` row, by Theorem 2.7 (opposing
  bounds on one bit sum) once the reason's literals are assumed (Theorem 2.6):
  with the fixed items' literals true, the row's only unassigned item terms
  have negative coefficients, so for unit propagation on the load's bits it
  acts as `BinEnc(loads[b]) ≥ floor_b`, which the negated conclusion opposes.
- **Reason** — `items[i] = b` for every item fixed in the bin, zero sizes
  included. Not minimal: a zero-size item's literal is never needed (measured:
  fixed sizes 3 and 0 give `a 1 i[l0][ge3] 1 ~i[x0][eq0] 1 ~i[x1][eq0] >= 1`).
- **Assertion** — `loads[b] ≥ floor ∨ ¬reason`. Measured at `Inferences`
  (`asrt/w/r1_floor_v.pbp`), item `x0` fixed in bin 0 with size 3:
  ```
  a 1 i[l0][ge3] 1 ~i[x0][eq0] >= 1::binpacking:((constraint_id _2));
  ```
  A constant item drops out of the reason (`a 1 i[l0][ge3] >= 1`). When the
  floor exceeds the load's upper bound, this line is the conflict.
- **Hint** — `hints::BinPacking`: `originator`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line of at most `n + 1` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: load-ceiling

(Rule 2, Stage 2.)

- **Infers** — `loads[b] ≤ ceiling_b`, the sum of the sizes of every item that
  can still be in bin `b`.
- **Fires when** — the load form, every call, for each bin whose upper bound is
  above the ceiling (`:1272–1275`).
- **Strength** — `partial`; with rules 1, 3 and 4, `bounds(R)` per bin row, as
  rule 1.
- **Algorithm** — the same pass.
- **Why it is true** — only the items that can be in the bin contribute.
- **Proof technique** — `RUP` against the `_ge` row, by Theorems 2.6 and 2.7,
  as rule 1 mirrored: the excluded items' literals are false, the rest have
  positive coefficients, and the row acts as `BinEnc(loads[b]) ≤ ceiling_b`.
- **Reason** — `items[i] ≠ b` for every item excluded from the bin, zero sizes
  included. Not minimal, as rule 1.
- **Assertion** — `loads[b] ≤ ceiling ∨ ¬reason`. Measured (`r2_ceiling`), `x0`
  fixed in bin 1, sizes 3 and 1:
  ```
  a 1 ~i[l0][ge2] 1 i[x0][eq0] >= 1::binpacking:((constraint_id _2));
  a 1 ~i[l1][ge5] >= 1::binpacking:((constraint_id _2));
  ```
  The second has an empty reason: nothing is excluded from bin 1, and the
  ceiling is the total size, which every solution respects. It is a bare unit
  that is a consequence of the model.
- **Hint** — `hints::BinPacking`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line of at most `n + 1` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: item-over-load

(Rule 3, Stage 2.)

- **Infers** — `items[i] ≠ b`.
- **Fires when** — the load form, for an item that can still be in bin `b`,
  when `floor_b + sizes[i] > ub(loads[b])` (`:1277–1282`), with the upper
  bound as rule 2 may just have lowered it.
- **Strength** — `partial`; Shaw's single item elimination (§2.5). With rules
  1, 2 and 4, `bounds(R)` per bin row.
- **Algorithm** — one test per undecided item, `O(n)`, against the floor
  computed before the bin's own inferences (an item fixed in by rule 4 in the
  same pass is not added; the next call sees it).
- **Why it is true** — putting the item in the bin would make the load at
  least `floor_b + sizes[i]`.
- **Proof technique** — `RUP` against the `_le` row, by Theorems 2.6 and 2.7:
  the negated conclusion sets the item's literal, and the row then acts as
  `BinEnc(loads[b]) ≥ floor_b + sizes[i]`, opposed by the reason's bound.
- **Reason** — every fixed item's `items[j] = b`, and `loads[b] ≤ ub`. Not
  minimal: it names fixed items the overflow does not need (fixed sizes 5 and
  1, bound 6, an item of size 3: `a 1 i[x2][b0] 1 ~i[x0][eq0] 1 ~i[x1][eq0] 1
  i[l0][ge7] >= 1`, where the size-1 item is not needed).
- **Assertion** — `items[i] ≠ b ∨ ¬reason`. Measured (`r3_overload`), `x0` fixed
  in bin 0 with size 3, `x1 ∈ {0, 1}` of size 2, `l0 ∈ 0..4`:
  ```
  a 1 i[x1][b0] 1 ~i[x0][eq0] 1 i[l0][ge5] >= 1::binpacking:((constraint_id _2));
  ```
- **Hint** — `hints::BinPacking`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line of at most `n + 2` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: item-forced-by-load

(Rule 4, Stage 2.)

- **Infers** — `items[i] = b`.
- **Fires when** — the load form, for an undecided item, when `ceiling_b −
  sizes[i] < lb(loads[b])` (`:1283–1287`).
- **Strength** — `partial`; Shaw's single item commitment (§2.5), the bounds
  version of the commitment Stage 3 lacks (#1346). With rules 1 to 3,
  `bounds(R)` per bin row.
- **Algorithm** — as rule 3, against the ceiling computed before the bin's own
  inferences.
- **Why it is true** — without the item, the bin cannot reach its load.
- **Proof technique** — `RUP` against the `_ge` row, by Theorems 2.6 and 2.7,
  as rule 3 mirrored.
- **Reason** — every excluded item's `items[j] ≠ b`, and `loads[b] ≥ lb`. Not
  minimal, as rule 3 mirrored.
- **Assertion** — `items[i] = b ∨ ¬reason`. Measured (`r4_forced`), sizes 3 and
  2, `l0 ∈ 4..10`:
  ```
  a 1 ~i[x0][b0] 1 ~i[l0][ge4] >= 1::binpacking:((constraint_id _1));
  ```
  (`~i[x0][b0]` is `x0 = 0` for a 0/1 item.)
- **Hint** — `hints::BinPacking`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line of at most `n + 2` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: capacity-overflow

(Rule 5, Stage 2.)

- **Infers** — a contradiction.
- **Fires when** — the capacity form, when `floor_b > capacities[b]`
  (`:1291–1293`).
- **Strength** — `checker` for the bin's row, on its fixed items.
- **Algorithm** — the pass of rule 1.
- **Why it is true** — the items fixed in the bin already exceed its capacity.
- **Proof technique** — `RUP` against the `_le` row: with the reason's
  literals true the row's left-hand side alone exceeds its degree; no bits are
  involved.
- **Reason** — every fixed item's `items[i] = b`. Not minimal when a subset
  already exceeds the capacity, or an item has size 0.
- **Assertion** — `¬reason`, from `contradiction()`. Measured (`r5_capfail`),
  two items fixed in bin 0, sizes 2 and 2, capacity 3:
  ```
  a 1 ~i[x0][eq0] 1 ~i[x1][eq0] >= 1::binpacking:((constraint_id _3));
  ```
  Rare in practice: rule 6 removes an item from a bin before it can overflow
  it, so the rule fires mostly when the domains arrive already overfull, or
  when an item is fixed later in the same call.
- **Hint** — `hints::BinPacking`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line of at most `n` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: item-over-capacity

(Rule 6, Stage 2.)

- **Infers** — `items[i] ≠ b`.
- **Fires when** — the capacity form, for an undecided item, when `floor_b +
  sizes[i] > capacities[b]` (`:1294–1298`).
- **Strength** — `GAC` on each bin's row, alone, for distinct item variables
  (a repeated one loses it; [Robustness](#robustness-and-limits)): an item
  that fits can always be packed with only the fixed items, and an item can
  always leave. Checked:
  no per-bin failure at any of the 4,199 root fixpoints of 8,000 random
  capacity-form instances (seeds 1 and 2, plain and with views; the rest fail
  at the root), under either consistency (`gac/bpcheck.cc`). This is why no
  Stage 3 changes the fixpoint in this form (#1349).
- **Algorithm** — one test per undecided item.
- **Why it is true** — as rule 3, against a constant.
- **Proof technique** — `RUP` against the `_le` row, as rule 5.
- **Reason** — every fixed item's `items[j] = b`. Not minimal, as rule 3
  (fixed sizes 5 and 1, capacity 6, an item of size 3: `a 1 i[x2][b0] 1
  ~i[x0][eq0] 1 ~i[x1][eq0] >= 1`).
- **Assertion** — `items[i] ≠ b ∨ ¬reason`. Measured (`r6_overcap`):
  ```
  a 1 i[x1][b0] 1 ~i[x0][eq0] >= 1::binpacking:((constraint_id _2));
  ```
- **Hint** — `hints::BinPacking`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line of at most `n` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: item-unsupported-in-bin

(Rule 7, Stage 3.)

- **Infers** — `items[i] ≠ b`.
- **Fires when** — `consistency::GAC`, when no node alive at item `i`'s layer
  (forward-reachable under the current item flags, and backward-reachable from
  an accepted terminal) has an alive include successor. `PerCall`:
  `run_stage3_for_bin`, `:1162–1183`, in the bin's one `infer_all` with rules 8
  and 9. `Upfront`: the backward pass, `:811–839`, after rules 8 and 9's
  `infer_all`.
- **Strength** — with rules 8 to 10, `partial`: **GAC on each bin's constraint
  for the items' value `b` and for every value of `loads[b]`**, short of the
  commitment `items[i] = b` (#1346). Checked by brute force
  (`gac/bpcheck.cc`, 2,000 random instances per seed at seeds 1 and 2, per
  strategy, load and capacity forms, plain and with `x + c` views and
  constants, up to five items and three bins, holey domains; about half of
  the instances fail at the root and test nothing about strength): no item value
  `b` and no load value without a support in its bin's constraint; in the load
  form, 54 and 37 values `c ≠ b` (in 36 and 28 instances) whose only supports
  need the item elsewhere; identical counts under the two strategies.
  Not joint GAC, which Shaw (§3) notes is NP-complete to achieve.
- **Algorithm** — `PerCall`: incremental forward and backward reachability
  over position-indexed bitmaps of the static diagram (see [Mutable
  state](#mutable-state-and-incrementality)), then one scan per item over its
  layer's nodes: `O(nodes)` per bin per call at worst. `Upfront`: a fresh
  forward pass with predecessor lists in a `std::map` per layer, then the
  backward pass: `O(nodes · log)` per bin per call. Trick (2003); the per-bin
  reading is Shaw's §3.
- **Why it is true** — every packing of bin `b` consistent with the current
  domains is a path from the root to an accepted terminal, and none takes the
  item's include edge.
- **Proof technique** — `PerCall`: `redundance` (the flags, at the root), `pol`
  and `RUP` (each forward chain and terminal line, at `Top` on first use),
  `RUP` (splits, at `Top`; hole refutations under the reason, at
  `Temporary`), then the conclusion by `RUP`; a `RUP sequence` whose lemmas
  live at `Top`, as in the preamble. `Upfront`: `chain scaffolding` (the `Top`
  scaffold), `RUP` lemmas `¬S` at `Current` for the dead nodes the backward
  pass finds, then the conclusion by `RUP` (`Knapsack`'s rule 7,
  [`knapsack.md`](knapsack.md)). Both rest on CP 2024 §3.3; the backward
  lemmas are McIlree and McCreesh's (*Proof Logging for Smart Extensional
  Constraints*, CP 2023) for `Regular`.
- **Reason** — `PerCall`: the bin's reason, `O(n + runs)`. `Upfront`: the
  shared generic reason over every item and load.
- **Assertion** — `items[i] ≠ b ∨ ¬reason`. Measured (`r7_prune_pc`,
  `r7_prune_up`), sizes `1, 2, 2, 2, 2` into a load of 4 (#995's case: what
  else goes in bin 0 is even):
  ```
  a 1 i[x0][b0] 1 ~i[l0][eq4] >= 1::binpacking:((constraint_id _2));
  ```
  under `PerCall`; under `Upfront` the same conclusion carries every item's
  and every load's bounds (14 literals).
- **Hint** — `hints::BinPacking`.
- **Offline reconstructibility** — `offline`, as in the preamble.
- **Proof size** — `PerCall`: per proof, at most one forward chain (two `pol`s,
  three RUPs) per edge, one split per node and one terminal pair (two `pol`s,
  two RUPs) per terminal, shared by every later inference; per call, one RUP
  of the reason's size per reachable terminal in a hole, plus the conclusion.
  `Upfront`: per newly dead node a `Current` `¬S` lemma, once per subtree,
  plus the conclusion; the scaffold is paid at the root. Measured in [Proof
  performance](#proof-performance).
- **Gaps** — `None.`
- **Tightness** — `Not shown` by a kept lane. The design note records hand-run
  mutations of `PerCall`'s derivation that VeriPB refused: dropping each of the
  three kinds of `Top` line, the hole refutations, or the include chains out of
  a pruned item's layer (the last two each needed a fixture of their own, now
  in `load_data` and `load_hole_data`).

### Rule: stage3-load-bounds

(Rule 8, Stage 3.)

- **Infers** — `loads[b] ≥ w_min` and `loads[b] ≤ w_max`, the smallest and
  largest accepted terminals.
- **Fires when** — `consistency::GAC`, load form, when a bound moves. `PerCall`:
  `:1186–1204`; `Upfront`: `:768–802`, in one `infer_all` with rule 9.
- **Strength** — `bounds(D)` on the load alone (each new bound is a terminal,
  that is a packing of the bin in the current domains); with rule 9, `GAC` on
  the load with respect to its bin's constraint, checked as under rule 7.
- **Algorithm** — the first and last accepted terminals, from the sweep.
- **Why it is true** — every packing ends at an accepted terminal.
- **Proof technique** — `PerCall`: as rule 7; the walk starts from the
  terminals the negated bound leaves, and the terminal lines rule out the rest.
  `Upfront`: per surviving terminal, a `pol` of the `_le` row with the
  terminal's `≥` flag and its RUP `¬g_up ∨ loads[b] ≥ lo`, the mirror for `≤ hi`,
  then the two bounds by RUP from the last layer's at-least-one; below the
  lower bound, the terminals are first killed by a `pol` against the `_ge` row
  and the load's bound and two `Current` lemmas (`:704–735`). That is
  `Knapsack`'s rule 5.
- **Reason** — as rule 7.
- **Assertion** — `bound ∨ ¬reason`. Measured (`r8_bounds_pc`), sizes `3, 3, 3`,
  `l0 ∈ 1..8`:
  ```
  a 1 i[l0][ge3] 1 ~i[l0][ge1] 1 i[l0][ge9] >= 1::binpacking:((constraint_id _1));
  a 1 ~i[l0][ge7] 1 ~i[l0][ge1] 1 i[l0][ge9] >= 1::binpacking:((constraint_id _1));
  ```
- **Hint** — `hints::BinPacking`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — as rule 7 for `PerCall`; for `Upfront`, four lines per
  surviving terminal and two more, each with the full reason.
- **Gaps** — `None.`
- **Tightness** — `Not shown` (see rule 7's hand-run lanes, which include a
  bound cut).

### Rule: stage3-load-gaps

(Rule 9, Stage 3.)

- **Infers** — that `loads[b]` is not in a gap between two accepted terminals.
  `PerCall`: one `not_in_range` per gap the domain reaches into
  (`:1197–1199`). `Upfront`: one `loads[b] ≠ v` per value in `(lo, hi]` that no
  surviving terminal reaches (`:778–782`).
- **Fires when** — as rule 8.
- **Strength** — `partial` alone; with rule 8, `GAC` on the load per bin.
- **Algorithm** — `PerCall`: one step per terminal and one interval test per
  gap. `Upfront`: per value of the load's domain, with a scan of the terminals
  per value inside the bounds, `O(|dom(loads[b])| · |terminal|)`: see
  [Interval efficiency](#interval-efficiency) and #1340.
- **Why it is true** — no packing reaches a value strictly between two
  consecutive reachable sums.
- **Proof technique** — `PerCall`: as rule 7. `Upfront`: `RUP` after rule 8's
  terminal `pol`s, with the negated conclusion fixing the load, each surviving
  terminal's bound line is falsified (`Knapsack`'s rule 6).
- **Reason** — as rule 7.
- **Assertion** — **two forms, chosen by the strategy and not by width.**
  `PerCall`, a range literal per gap (`r8_bounds_pc`, bin 1 over `0..9`):
  ```
  a 1 ~i[l1][in1_2] 1 ~i[l1][ge0] 1 i[l1][ge10] >= 1::binpacking:((constraint_id _1));
  ```
  `Upfront`, one line per value (`r8_bounds_up`): `a 1 ~i[l1][eq1] …`, `a 1
  ~i[l1][eq2] …`, each with the full reason. A one-value gap is `~i[l][eqv]`
  in both.
- **Hint** — `hints::BinPacking`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — `PerCall`: one conclusion per gap; `Upfront`: one RUP per
  removed value, each of `O(n + m + h)` literals.
- **Gaps** — `None.`
- **Tightness** — `Not shown` (rule 7's hand-run lanes include a gap cut).

### Rule: stage3-no-packing

(Rule 10, Stage 3.)

- **Infers** — a contradiction.
- **Fires when** — `consistency::GAC`, when no accepted terminal is reachable
  (`PerCall`: `feasible` false, `:1152`, then `contradiction()` at `:983`;
  `Upfront`: an empty last layer after the load filters, `:759–766`). In the
  capacity form `PerCall` cannot reach it, since every terminal is accepted
  and every node reaches one; `Upfront` can only when an item fixed earlier in
  the same call has overfilled the bin, which Stage 2's next call would catch
  as rule 5.
- **Strength** — `partial`: detects that bin `b` has no packing in the current
  domains.
- **Algorithm** — the sweep.
- **Why it is true** — every packing would end at an accepted terminal.
- **Proof technique** — `PerCall`: as rule 7, walking from every terminal.
  `Upfront`: the filters' lemmas, then the empty clause by RUP under the reason
  (`:760–761`), then `contradiction()`; the call's temporary lines are then
  stranded ([Proof-time state](#proof-time-state)).
- **Reason** — as rule 7.
- **Assertion** — `¬reason`, from `contradiction()`. Measured (`r10_fail_pc`),
  sizes 2 and 2, `l0 ∈ {1, 3}`:
  ```
  a 1 ~i[l0][ge1] 1 i[l0][ge4] 1 i[l0][eq2] >= 1::binpacking:((constraint_id _2));
  ```
  Under `Upfront` the same with every item's and load's bounds. Not every
  failure arrives here: a Stage 2 inference whose literal is already false
  fails as an ordinary inference first, asserting `attempted literal ∨
  ¬reason`.
- **Hint** — `hints::BinPacking`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — as rule 7, plus one empty-clause RUP under `Upfront`.
- **Gaps** — `None.` `Upfront` strands its temporary lines.
- **Tightness** — `Not shown.`

### Rule: shaw-overload

(Rule 11, Stage 4.)

- **Infers** — a contradiction.
- **Fires when** — `bin_packing::Shaw`, for the first threshold `α` (from the
  largest down, skipping any above every ceiling) at which `DELTA ≥ 1`
  (`run_stage4`, `:1585–1636`), where, with `S(α)` the items of size at least
  `α` plus every item of positive size fixed in a bin, `c_i = ⌈sizes[i] / α⌉`,
  `T_b` the counted size that can still go in bin `b` and `cap_b` its ceiling
  (the capacity, or the load's upper bound for a plain-variable load; zero
  contribution otherwise):
  `DELTA = Σ_b max(0, ⌈(T_b − cap_b)/α⌉) − Σ_{i ∈ S(α)} c_i (|D_i| − 1)`.
- **Strength** — `partial`: a cross-bin infeasibility test, spanning the energy
  bound (`α = 1`) and pigeonhole counts (large `α`), in the family of Martello
  and Toth's L2. It does not make the constraint GAC; at the root it removed
  every joint GAC failure the per-bin stages left at the root fixpoints of
  8,000 random capacity-form instances but one value in one instance, and changed almost
  nothing in the load form (`gac/bpcheck.cc`).
- **Algorithm** — `O(n · m)` to read the domains, then per threshold `O(n)` for
  the weights and `O(m)` for the bins, the totals folded once across the
  descending list: `O(n · m + d · (n + m))` for `d` distinct sizes. The
  bound's derivation is the code's own (`:1303–1347`); its threshold rule is
  the domain-aware form of L2's.
- **Why it is true** — divide each bin's capacity row, weakened to the counted
  items, by `α` and round up; add `c_i` times each counted item's at-least-one
  over its domain. Every `[x = b] + ¬[x = b]` pair cancels, leaving a line whose
  surviving terms are exactly the item literals the reason rules out, with
  degree `DELTA`; so `DELTA ≥ 1` contradicts the reason. A bin with room to
  spare contributes the trivially true `Σ c_i ¬[x_i = b] ≥ 0` rather than its
  row, whose negative right-hand side would cancel another bin's overflow.
- **Proof technique** — `pol`: per bin with a positive rounded overflow, its
  `_le` row plus, in the load form, the load's bound (`add_bound_p_term`) plus
  one trivially true weakening line (written by `RUP` so that a view item is
  spelled as its row spells it), divided by `α`; per other bin with a kept
  item, one trivially true `RUP`; then the summing `pol` with each counted
  non-constant item's at-least-one row over its current domain
  (`need_constraint_saying_variable_takes_at_least_one_value_over_cover`)
  weighted by `c_i`; then the conclusion by `RUP` (`ThenRUP::Yes`). Division is
  the cutting-planes rounding rule. **No published procedure**: the
  derivation is this family's (`emit_stage4_proof`, `:1430–1520`), and the
  argument is the one above. Preconditions: non-negative sizes, `α ≥ 1`, and a
  citable ceiling for every bin that contributes.
- **Reason** — the shared generic reason over every item (and every load under
  `Upfront` in the load form), plus `loads[c] ≤ cap_c` for every bin in the
  load form: one literal per bound or run of every variable. Not minimal (it
  names every item, counted or not).
- **Assertion** — `¬reason`. Measured (`r11_shawfail`), three items of size 7
  over two bins of capacity 10:
  ```
  a 1 ~i[x0][ge0] 1 i[x0][ge2] 1 ~i[x1][ge0] 1 i[x1][ge2] 1 ~i[x2][ge0] 1 i[x2][ge2] >= 1::binpacking:((constraint_id _1));
  ```
- **Hint** — `hints::BinPacking`. It does not carry `α`.
- **Offline reconstructibility** — `offline`. The clause and the reason fix
  every item's domain (and, in the load form, every bin's ceiling); the model
  fixes the sizes, so the threshold list (1 and the distinct sizes above 1,
  at most `n + 1` values), each `S(α)`, each `c_i` and which bins have a
  citable ceiling. The procedure is fixed: for each threshold from the
  largest, skipping any above every ceiling, compute `DELTA` on the reason's
  domains by `O(n · m)` arithmetic, and write the derivation above for the
  first with `DELTA ≥ 1`. One exists: the solver's `α` gave `DELTA ≥ 1` on the
  domains it swept, and the reason's domains can only be tighter (the reason
  is materialised at inference time, after any earlier prunes of the same
  sweep), while `DELTA` cannot fall as domains shrink (removing a bin from a
  counted item lowers the penalty by `c_i` and that bin's rounded overflow by
  at most `c_i`; fixing an item only adds to some `T_b`). So this is a scan
  over a list the model fixes that is guaranteed to stop at a success: not a
  case split in which every case succeeds, as in Appendix C's "a fixed case
  split is not a search", but the same shape as the `Upfront`
  contradiction's scan over bins, and like it nothing is found that the rows
  and the reason do not fix; `offline` is the reading taken here. The hint does not carry `α`; carrying it
  would save the enumeration, not make anything reconstructible that is not.
- **Proof size** — per firing, at most `2m + 1` `pol` and `RUP` lines plus the
  conclusion, `O(n · m)` terms (the at-least-one rows are per run of each
  domain).
- **Gaps** — `None.`
- **Tightness** — `Not shown` by a kept lane. The design note's hand-run
  mutations (`dev_docs/bin-packing.md`, "Mutation testing", at two pinned
  seeds): firing at `DELTA ≥ 0`, dropping the division, dropping every or two
  of the at-least-one rows, and using the capacity row where the clamp chose
  the trivial one are all refused; dropping one at-least-one row survives,
  because VeriPB's own propagation recovers it. The clamp fixture (`{7, 7, 7,
  1}` over capacities `{10, 10, 100}`) is in `capa_data`.

### Rule: shaw-shave

(Rule 12, Stage 4.)

- **Infers** — `items[h] ≠ b`.
- **Fires when** — `bin_packing::Shaw`, at each threshold that did not fail,
  for each item `h` with at least two bins and positive size passing the
  necessary condition `DELTA + c_h |D_h| ≥ 1`, and each bin `b` it can take,
  when `DELTA` recomputed with `h` taken out of `S(α)` and put back into `b`
  alone is at least 1 (`:1641–1693`).
- **Strength** — `partial`: shaving on rule 11's bound (Shaw §3.4's
  construction of a propagation rule from a pruning rule, after Gent and
  Walsh). It prunes the #209 example, `sizes {1, 2, 2}` over capacities `{3,
  2}`, which no single bin can.
- **Algorithm** — `O(1)` per item for the necessary condition and `O(m)` per
  candidate, incrementally from the sweep's totals.
- **Why it is true** — rule 11's argument under the hypothesis `items[h] = b`.
- **Proof technique** — `pol` and `RUP`, as rule 11, with `h` kept in bin
  `b`'s row only and its at-least-one row stated over its real domain, so that
  its other bins survive as positive terms and the closing `RUP`'s own negated
  conclusion (`items[h] = b`) removes them: the hypothesis costs no line, and
  nothing is pinned into the reason.
- **Reason** — as rule 11.
- **Assertion** — `items[h] ≠ b ∨ ¬reason`. Measured (`r12_shave`):
  ```
  a 1 ~i[x0][b0] 1 ~i[x0][ge0] 1 i[x0][ge2] 1 ~i[x1][ge0] 1 i[x1][ge2] 1 ~i[x2][ge0] 1 i[x2][ge2] >= 1::binpacking:((constraint_id _1));
  ```
  (`~i[x0][b0]` is `x0 ≠ 1`.)
- **Hint** — `hints::BinPacking`.
- **Offline reconstructibility** — `offline`, as rule 11, with the shaved
  `DELTA` for the `h` and `b` the clause names.
- **Proof size** — as rule 11, per prune.
- **Gaps** — `None.`
- **Tightness** — as rule 11 (the shaving arm at `DELTA ≥ 0` is refused).

## Evidence

### Tests

- **`bin_packing_test`**: 13 curated capacity cases and 16 load cases
  (`bin_packing_test.cc:603–645`, `:648–702`), each under both strategies and with and
  without Shaw, with and without proofs, and their recursion counts compared
  (`check_strategies_agree`, which #995 added); four load cases whose loads
  start with holes on reachable terminals (`:706–711`, run at `:736–745`);
  the Stage 4
  pigeonhole cases, required to cut the search, under `GAC` and `BC`, one over
  105 bins so that the at-least-one rows come back as interval covers; the
  degenerate-load cases (a view load, a negated view load, a constant load,
  under both strategies, #1195), the item-that-is-a-later-load's-view cases
  (#1195), the constant-item cases (#1192), and the edge-of-range cases (sizes
  at `2⁶⁰ − 1`, through `solve_for_tests_with_callbacks` and their own
  enumerator; see [Overflow](#robustness-and-limits) for what they do not
  run). Everything else under plain `solve_for_tests` against a brute force:
  **solutions only, no GAC check at any node**. VeriPB runs, as a subprocess
  (`constraints_test_utils.hh:62–73`), when it is on the path: 156 proofs in the bare lane at seed 1. Every domain is an
  interval unless a case makes holes. Seeded (`--seed=N`).
- **Lanes:** the bare lane, `view_mixed` and `view_mixed_late` (items wrapped
  in views, the latter registering them late, #1200); the per-wrap sweep
  (`view_w1` to `w18`, per position) is registered only with
  `GCS_ENABLE_VIEW_WRAP_SWEEP`, off by default. The bare-lane-only cases are
  gated so that the view lanes do not race on proof names (#961).
- **`hole_wakes_test`:** a hole in a load wakes `Upfront`'s Stage 3 (#966).
- **`integer_ranges_test`:** refusal of a size and a capacity past the range.
- **`scp_reader_test`:** both forms enumerate, and round-trip.
- **MiniZinc:** `binpackingtest.mzn`, `binpackingoffsettest.mzn` (offsets,
  single capacity) and `binpackingloadtest.mzn` (the load form), with proofs.
- **XCSP3:** `xcsp/tests/bin_packing.xml` (constant `<limits>`).
- **Audit lane:** the one `Clean` row.

**Runtime caps.** No lane sets or clears one. Under the default caps
(`GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500`), at seeds 1 to 5,
the bare lane makes 314 runs per seed and truncates 2: the edge-of-range "star"
case under `BC`, with and without Shaw, proofs off, which checks 300 of its 512
solutions for soundness only. Everything else runs to completion. Uncapped at
seed 1 the bare lane takes 6.5 s (`bin_packing_test --seed=1`, VeriPB on the
path, at `86caad24`).

**Tightness:** no kept mutation lane. The design note records hand-run lanes
for `PerCall`'s Stage 3 and for Stage 4 (rules 7 and 11); their fixtures stayed
in the suite, so the controls (the same instances verifying uncorrupted) are
the suite's own runs.

**This audit's own checks** (all at `86caad24`, fataepyc-10, 2026-10-10,
scratch `tmp/fd-bp/bin_packing/`):

- **Root brute force** (`gac/bpcheck.cc`): 64 runs of 2,000 random instances
  ({`PerCall`, `Upfront`} × {`GAC`, `BC`} × Shaw on and off × both forms ×
  plain and views-and-constants × seeds 1 and 2; about half fail at the root,
  which tests soundness only): no unsound root; per-bin
  strength as under rules 6 and 7; bounds(R) per bin row at every fixpoint
  (rule 1); identical counts under the two strategies. With repeated variables
  (`gac/bpalias.cc`): no unsound root in 20,000 instances.
- **Proofs** (`proofs/bpsweep.cc`): 1,600 random instances (up to seven items,
  four bins, sizes 0 to 5, holey domains, plain and with views and constants),
  enumerated under a seeded random value order, for every combination of
  strategy, consistency, Shaw and form: all 1,600 proofs verify with VeriPB
  3.0.2 (`--force-checked-deletion`) and every solution count matches the
  brute force. The two strategies' node counts agree on all 800 pairs; `GAC`'s
  and `BC`'s node and solution counts agree on all 400 capacity-form pairs (and differ on 52 of 400
  load-form pairs). 800 more "tight" instances (sizes 2 to 7 against
  capacities 5 to 12), where Stage 4 changes 98 of 400 proofs and cuts the
  nodes of 14, all verify.
- **Assertions** (`asrt/`): every rule's `a` line above, and the falsification
  check in the catalogue's preamble.
- **Front ends**, as under [Concrete
  constraints](#concrete-constraints-and-frontend-coverage).

**What the tests do not cover.**

- **Strength.** No test checks GAC, per bin or otherwise, at any node, which is
  how the missing commitment (#1346) went unseen; the comment at
  `bin_packing_test.cc:228–233` defers a per-bin GAC checker "if regressions
  appear".
- **The constant-capacity form's waste** (#1349): nothing compares `GAC`
  with `BC`.
- **Holey item domains, views on loads beyond the degenerate cases, and
  repeated variables**, outside the audit's sweeps.
- **XCSP3's condition form, negative values from any front end, item domains
  reaching outside the bins, and `var opt` models**: none tested, which is how #1345
  and #1347 stayed hidden.
- **Wide shapes**: a large size under `Upfront`, beyond the one `Clean` row
  with unit sizes.
- **The `.scp` against cake**: there is no rule to chain against.
- **Real instances:** none of the corpus models is ported.

### Benchmarks and examples

- **In the repository:** `benchmarks/bin_packing_bench` (eight curated
  instances: 1, 3, 5, 6, 7 in the capacity form, 2, 4, 8 in the load form; 7
  and 8 are pigeonholes; deterministic search; not a ctest).
- **Corpus:** 14 MiniZinc Challenge instances post the family, nearly all in
  the load form (`mapping` 2015, 2016, 2018 and 2021; `gbac` 2016, 2017, 2020;
  `steelmillslab` 2017 and 2019; `team-assignment` 2018 and 2022, one of each
  form; `kidney-exchange` 2019 and 2023, capacities; `ihtc-2024-marte` 2025).
  None finishes in 60 s, so none is a proof benchmark.
- **For CPU:** bench instances 3 and 4 (tens of seconds, millions of nodes, the
  same tree under every configuration but Shaw's), and 1 and 2 for quick
  checks; 7 and 8 for Stage 4.
- **For proof verification:** bench instances 1, 2, 7 and 8 under `PerCall`,
  which check in 0.2 to 21 s; never prove 3 or 4.

### CPU performance

*Release build of `86caad24` (GCC 15.2.0, `-O3 -march=native`); fataepyc-10,
pinned to one core, malloc thresholds fixed; 2026-10-10, while other work ran on
other cores (load 4 to 9), so the instruction counts are the measure; medians
of five runs (three for instances 3 and 4); runs under 10 ms by instructions
only (`tmp/fd-bp/bin_packing/perf/off/`).*

**`bin_packing_bench`, proofs off, every configuration.** The bench enumerates
every solution with deterministic search (`dom_then_deg` over the items,
smallest value first). `GAC` is the default, with `PerCall`.

| Instance | Solutions | Nodes | `GAC` instr:u | `Upfront` | `BC` | `GAC` + Shaw | `BC` + Shaw | `GAC` wall | `BC` wall |
|---|---|---|---|---|---|---|---|---|---|
| 1: 10 items, 3 bins, capacities | 3,780 | 7,192 | 170.7 M | 600.0 M | 64.7 M | 233.2 M | 127.7 M | 33.1 ms | 12.4 ms |
| 2: the same, loads `8..14` | 12,198 | 20,029 | 679.3 M | 2,234.9 M | 230.2 M | 893.1 M | 457.9 M | 134.1 ms | 48.6 ms |
| 3: 12 items, 4 bins, capacities | 3,913,416 | 5,654,897 | 161.1 G | 502.5 G | 49.3 G | 204.6 G | 92.8 G | 30.2 s | 9.7 s |
| 4: the same, loads `6..12` | 1,922,184 | 2,726,033 | 130.7 G | 451.8 G | 41.8 G | 167.5 G | 81.8 G | 25.7 s | 9.0 s |
| 5: 8 items, 2 bins, tight capacities | 22 | 63 (47 with Shaw) | 5.1 M | 8.3 M | 3.7 M | 4.8 M | 3.6 M | — | — |
| 6: 8 items, 2 bins, wide sizes | 32 | 83 (71 with Shaw) | 5.4 M | 9.6 M | 3.8 M | 5.5 M | 4.0 M | — | — |
| 7: pigeonhole, capacities | 0 | 4,485 (1 with Shaw) | 216.6 M | 388.4 M | 171.7 M | 3.4 M | 2.8 M | 33.4 ms | 24.5 ms |
| 8: pigeonhole, loads `0..10` | 0 | 4,485 (1 with Shaw) | 186.2 M | 456.3 M | 162.2 M | 3.6 M | 2.9 M | 31.0 ms | 24.7 ms |

What the table says, with the trees checked (solutions and nodes on all;
propagation counts too where stated):

- **`PerCall` and `Upfront` search the same tree on all eight, and `Upfront`
  runs 1.6 to 3.5 times the instructions** (3.1 to 3.5 on the four
  enumerations) with proofs off: its per-call map of predecessor lists and its
  allocation, against `PerCall`'s incremental bitmaps.
- **In the capacity form `GAC` and `BC` search the same tree** (instances 1,
  3, 5, 6 and 7, propagation counts equal too), and `GAC` costs 2.6 and 3.3
  times the instructions on the two enumerations and 1.26 times on instance 7:
  the `PerCall` Stage 3 sweep, which never infers in this form (#1349). On
  instances 5 and 6 the ratio (1.4) mostly measures process start-up, which is
  most of a 4 to 5 M-instruction run; the difference is about 1.4 M and 1.6 M
  instructions.
- **In the load form the two also search the same tree on this bench**
  (instances 2, 4 and 8: equal nodes and solutions; `BC` makes more
  propagator calls), at 2.9 and 3.1 times the instructions for `GAC` on the
  enumerations. Why Stage 3's extra inferences never change a node count here
  was not traced; it is these instances and not a rule, since the random
  load-form sweeps differ on 52 of 400 trees.
- **Shaw** cuts the pigeonholes from 4,485 nodes to 1, and instances 5 and 6
  from 63 to 47 and 83 to 71 nodes; on 1 to 4, where it cuts nothing, it costs
  1.27 to 1.37 times the instructions on top of `GAC` and 1.9 to 2.0 times on
  top of `BC`.

**Against Gecode 6.3.0**, on MiniZinc twins of instances 1 to 4 (bins
numbered from 1, `int_search(bin, input_order, indomain_min)`, every solution;
flattened with MiniZinc 2.9.7 and run directly, `fzn-glasgow -a -s` against
`fzn-gecode -a -s`; default Glasgow configuration; medians of three; same
build, machine and date; `perf/gecode/`). Gecode's MiniZinc library maps both
`bin_packing_load` and `bin_packing_capa` onto its own propagator, Shaw's
(`gecode_bin_packing_load`; the capacity form through auxiliary loads), so
this is propagator against propagator.

| Twin | Solutions | Glasgow nodes | failures | Gecode nodes | failures | Glasgow solve | instr:u | Gecode solve | instr:u |
|---|---|---|---|---|---|---|---|---|---|
| g1 (1, capacities) | 3,780 | 7,559 | 0 | 7,559 | 0 | 0.080 s | 236 M | 0.020 s | 70.5 M |
| g2 (2, loads) | 12,198 | 24,395 | 0 | 24,395 | 0 | 0.340 s | 1,031 M | 0.061 s | 172 M |
| g3 (3, capacities) | 3,913,416 | 7,826,831 | 0 | 7,826,831 | 0 | 94.5 s | 282.0 G | 19.2 s | 49.5 G |
| g4 (4, loads) | 1,922,184 | 3,917,447 | 39,600 | 3,852,743 | 4,188 | 78.5 s | 234.9 G | 10.1 s | 27.4 G |

The trees are the same on g1 to g3, neither side failing; on g4 Gecode fails
4,188 times where Glasgow fails 39,600, its propagator being stronger there
than Glasgow's (which of Shaw's rules does it was not traced). On
equal trees Gecode runs 3.3 to 6.0 times fewer instructions. Glasgow through
MiniZinc is also slower per node than the bench (12 µs a node on g3 against
5.3 on instance 3: items as offset views, input order, solutions printed), not
separated further.

**The corpus.** Every MiniZinc Challenge model in the corpus that posts
`bin_packing*` (`/cluster/ciaran/claude/minizinc-benchmarks`, one instance per
model, the smallest data file; 2026's `gbac` has none), MiniZinc 2.9.7, 60 s,
proofs off, against Gecode 6.3.0 under the same limit (`corpus/`). All but
`kidney-exchange` post the load form; `team-assignment` posts one of each.
Whole models, objective search with other constraints: not search-identical,
and not dominated by this family.

| Model (instance) | Posted | Glasgow best | nodes | Gecode best | nodes |
|---|---|---|---|---|---|
| 2015 mapping (full2x2) | 1 load, 14 items, 4 bins | 1103 | 5.76 M | 1103 | 17.8 M |
| 2016 mapping (mesh2x2_1) | 1 load, 14 × 4 | 1060 | 7.17 M | 1060 | 17.7 M |
| 2018 mapping (full2x2_mp3) | 1 load, 28 × 4 | 1222 | 3.72 M | 1222 | 10.5 M |
| 2021 mapping (mesh2x2_2) | 1 load, 14 × 4 | 1040 | 5.15 M | 1040 | 14.5 M |
| 2016 gbac (reduced_UD10) | 15 load, 3–10 × 6 | 7645 | 1.02 M | 6653 | 11.5 M |
| 2017 gbac (reduced_UD4) | 16 load, 5–9 × 6 | 6572 | 0.26 M | 5132 | 4.01 M |
| 2020 gbac (reduced_UD5) | 31 load, 3–9 × 6 | 10618 | 0.26 M | 10725 | 4.52 M |
| 2017 steelmillslab (bench_13_0) | 1 load, 111 × 111 | 39 | 13,548 | 27 | 1.86 M |
| 2019 steelmillslab (bench_2_19) | 1 load, 111 × 111 | 70 | 3,164 | 70 | 1.46 M |
| 2018 team-assignment (data2_5_6), max | 1 load + 1 capacity, 30 × 6 | 931 | 16,809 | 962 | 1.39 M |
| 2022 team-assignment (data1_4_6), max | 1 load + 1 capacity, 24 × 6 | 2888 | 68,882 | 2948, optimal in 20.1 s | 1.34 M |
| 2019 kidney-exchange (3_20_0.40_3), max | 1 capacity, 20 × 20 | none | 0.96 M | none | 8.04 M |
| 2023 kidney-exchange (3_20_0.40_2), max | 1 capacity, 20 × 20 | 1160 | 0.82 M | 1386 | 4.85 M |
| 2025 ihtc-2024-marte (i01) | 8 load, 0–459 items × 100 or 300 bins | 8388 | — | 8155 | 0.33 M |

All minimise except where marked. Glasgow ties Gecode on the four `mapping`
instances and 2019 `steelmillslab`, is better on 2020 `gbac`, and worse on the
other seven that found a solution; neither solves 2019 `kidney-exchange`.
Glasgow explores 2.5 to 460 times fewer nodes. No run errored; on `ihtc` Glasgow
was not interrupted cleanly at 60 s and printed no statistics (two solutions,
64 s wall), and that model posts one `BinPacking` with no items. The #995-era
figures in `dev_docs/bin-packing.md` on main (13 models, 2022 `team-assignment` 2884
to 2887) were measured elsewhere and are not to be mixed with these.

**What the benchmarks do not exercise.** Holey item domains, views and
constants among the loads, repeated variables, large sizes (the bench's are 1
to 7), and the commitment that Stage 3 lacks.

### Proof performance

*Same build and machine; proofs written and checked on 2026-10-14, on an
otherwise idle machine (load under 1), solo and pinned to one core; VeriPB
3.0.2 with `--force-checked-deletion`; three proof-writing runs per cell
(median), VeriPB on the last proof, the cells re-timed three times within 1%
(`perf/proof/`, `perf/vr/`). "Flag `red`" counts the `red` lines naming a
`bpup_`, `bpdn_`, `bpat_` or `bpphantom_` flag: the `Top` flag definitions
(`PerCall`'s lazily written chain, split and terminal lines are `pol` and `rup`
lines, not counted there).*

| Instance | Configuration | Solve, proof on | Lines | Bytes | VeriPB | µs per line | Flag `red` |
|---|---|---|---|---|---|---|---|
| 1 (capacities) | `GAC`, `PerCall` | 0.075 s | 50,466 | 2.94 MB | 3.51 s | 69.4 | 3,114 |
| 1 | `GAC`, `Upfront` | 0.543 s | 148,857 | 22.18 MB | 19.88 s | 133.5 | 6,516 |
| 1 | `BC` | 0.045 s | 47,352 | 2.46 MB | 0.37 s | 7.8 | 0 |
| 2 (loads) | `GAC`, `PerCall` | 0.300 s | 198,408 | 16.35 MB | 20.83 s | 105.0 | 3,114 |
| 2 | `GAC`, `Upfront` | 3.645 s | 1,810,842 | 308.54 MB | 77.02 s | 42.5 | 6,516 |
| 2 | `BC` | 0.179 s | 184,301 | 13.98 MB | 2.97 s | 16.1 | 0 |
| 7 (pigeonhole, capacities) | `GAC`, `PerCall` | 0.060 s | 30,976 | 1.64 MB | 0.17 s | 5.5 | 1,320 |
| 7 | `GAC`, `Upfront` | 0.173 s | 62,742 | 7.31 MB | 1.02 s | 16.3 | 2,400 |
| 7 | `BC` | 0.050 s | 29,656 | 1.46 MB | 0.15 s | 5.1 | 0 |
| 7 | `GAC`, `PerCall`, Shaw | 0.010 s | 1,463 | 0.19 MB | 0.01 s | — | 1,320 |
| 8 (pigeonhole, loads) | `GAC`, `PerCall` | 0.064 s | 39,024 | 2.42 MB | 0.52 s | 13.3 | 1,320 |
| 8 | `GAC`, `Upfront` | 0.542 s | 247,020 | 50.37 MB | 3.11 s | 12.6 | 2,400 |
| 8 | `BC` | 0.053 s | 36,245 | 2.11 MB | 0.28 s | 7.7 | 0 |
| 8 | `GAC`, `PerCall`, Shaw | 0.010 s | 1,490 | 0.19 MB | 0.01 s | — | 1,320 |

Instances 5 and 6 are too small to time: their `PerCall` proofs are 0.20 and
0.22 MB, about ten times `BC`'s, almost all of it the flags; `Upfront`'s are
1.07 and 1.22 MB. All 60 proofs of the matrix (these, Shaw on 1, 2, 5, 6 and
`BC` with Shaw) verify with the right conclusions and counts.

- **`Upfront` against `PerCall`:** 4.5 to 20.8 times the bytes (7.5 on 1, 18.9
  on 2, 4.5 on 7, 20.8 on 8; 5.3 and 5.6 on 5 and 6), 3.7 to 6.0 times the
  checking time, and 2.9 to 12 times the proof-writing time. It loses on both
  axes, as [`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md)
  says. The design note's table (#995 era, measured elsewhere, not to be mixed
  with this one) agrees within a few percent on bytes and solve times; its
  `PerCall` checking times on instances 7 and 8 (0.21 and 0.61 s) are 17 to
  24% above these.
- **`GAC` against `BC` on the same tree:** in the capacity form `PerCall`'s
  proof is 1.07 times `BC`'s in lines and 1.20 in bytes on instance 1, but
  takes **9.5 times as long to check** (3.51 s against 0.37 s; 69 µs a line
  against 7.8): the 3,114 flag definitions (519 diagram nodes, three flags,
  two lines each) sit at `Top` for a `PerCall` Stage 3 that never infers in
  this form, and every enumeration RUP pays for them (#1349). On the pigeonhole the tax is small
  (0.17 against 0.15 s). In the load form, where Stage 3 does infer but does
  not change the tree on this bench, instance 2's proof is 1.17 times `BC`'s
  in bytes and 7.0 times its checking time; instance 8's, 1.15 and 1.9.
- **Shaw** collapses the pigeonhole proofs to 1,463 and 1,490 lines (from
  30,976 and 39,024) and their checks to 0.01 s; on instance 1, where it cuts
  nothing, it adds 483 lines (1%), and on instance 2 it never fires (the proofs
  are byte-identical).

**Own against shared, approximately.** As in [`knapsack.md`](knapsack.md):
`Off` lines minus (`Inferences` lines minus the family's `a` lines), which
slightly over-counts the family, since `Off` also carries shared literal
definitions that `Inferences` does not. On instance 1: 14,153 of 50,466 lines
under `PerCall` (28%), 112,544 of 148,857 under `Upfront` (76%), 11,039 of
47,352 under `BC` (23%); on 2, 41%, 94% and 37%; on 7, 44%, 73% and 42%; on 8,
54%, 93% and 51%. So under `PerCall` and `BC` the search's own lines (a
solution line per solution, backtracks) are most of the lines of these
enumerations, but under `PerCall` the family's `Top` flags dominate the
checking time: its µs per line is 4 to 9 times `BC`'s on the
enumerations.

**Assertion levels.** At `Inferences` (`GCS_ASSERTION_LEVEL=inferences`) the
strategy changes only the reasons in the assertions: instance 1's proof is
3.80 MB under `PerCall` and `BC` and 3.81 MB under `Upfront`, instance 2's
23.6, 21.8 and 25.5 MB, and each checks `UNDER ASSERTIONS` in at most 4.7 s.
The family's `a` lines are 32% of all `a` lines on instance 1 (5,199 of
16,171), 67% on 2 (65,178 of 97,405), 52% and 45% on 5 and 6, and 73% and 79%
on the pigeonholes; the rest are the search's. There is one wire form
(`binpacking`) for every rule.

**Every assertion level, both declaration styles** (the two fact-checks'
sweeps, at `86caad24` on 2026-10-14: 10,624 random enumerations over every
combination of strategy, consistency, Shaw, form, plain items and loads, `x +
c` and `−x + c` views and constants, and variables declared by range and by
value list, plus 2,400 more aimed at view and constant loads; every count
matches the brute force and VeriPB's own). `Off` verifies, and `Definitions`,
`Inferences` and `Backtracking` are accepted `UNDER ASSERTIONS`, everywhere.
At `Links`, 12 of the 544 satisfiable runs with range-declared variables in
the first sweep (all 12 in the load form with plain loads, from two instances;
0 of the 240 with value lists) and 18 in the second (all range-declared, with
a view load) are rejected at a `solx` line. In 8 of the first 12 it is the
first `solx`, on the solution-time `red` definition of a load's equality atom;
in the other 4 a later one, on an equality definition written during search
(2) or an asserted `bound_link` (2). That is #1210, open and generic: its own
repro (three range-declared variables, with no constraint, `LessThan`,
`AllDifferent`, or `LessThan` with an objective) is still rejected at
`86caad24` while its value-list twin is accepted; a range-declared variable is
needed in everything run, though not always enough (532 of the 544 runs
above are accepted). Views of a range-declared variable are rejected too:
under `BinPacking` (the view as a load), `NotEquals` and `AllDifferent` even
against a value-list partner, under `LinearEquality` and `Equals` only when
the partner is range-declared as well (this audit's comment on #1210). No
failure of #1330's kind either, because this family writes nothing above
`Off` but its assertions.

**Per root call, against the instance.** The root proof is the flags plus the
first call's lines. Over a grid of 10 to 40 items, sizes up to 5, 20 or 100,
and 2, 5 or 10 bins, each with a capacity or a load of a `1/m` share of the
total (`size/grid.txt`, root call only, at `Off`): `PerCall` writes 1,480 lines
(0.2 MB) at the smallest point and 1.86 M lines (693 MB) at the largest
capacity-form point, almost all of it flag definitions, while `Upfront`'s
root proof is 8.5 to 93 times that in lines (3.0 to 9.7 times in bytes) and passed a 4 GB cap at 40 items of sizes up to
100 over ten bins. The flags are `6 × Σ_b Σ_i |DAG_b[i]|` lines of up to `i`
terms each, so they grow with the number of distinct partial sums per layer,
which is what large sizes and many items make, not with the loads' declared
widths.

## Status, gaps, and next steps

### Proof-logging gaps

`None` for the inferences: every one is justified at `Off` under both
strategies, every assertion carries its reason, and no stage changes with
proofs on (Stage 4's choice of which bins to count is made from the load's
kind, not from whether a proof is written). One wrong-answer route has a
verified proof: XCSP3's condition form proves the mistranslated model
`UNSATISFIABLE` (#1345), which no checker of this family can catch, since
the mistranslation is in the `.scp` it starts from and `cake_pb_cp` has no
`binpacking` rule anyway.

### Known limitations

- **XCSP3 models with a single `<condition>` can be answered wrongly** when
  the items' domains skip a bin below the largest, or all start above 0, and
  the condition rejects an empty bin (`ge`, `gt` or `eq` with a positive
  operand, `ne` with 0, `in` above 0, or a variable operand under those)
  (#1345).
- **MiniZinc errors on `var opt` items over 1-based bins, on item domains
  reaching outside the bins and
  on loads declared with negative lower bounds; XCSP3 aborts on negative
  sizes, on negative constant limits and loads, on variable loads whose lower
  bound is negative, and on item domains outside the bins** (#1347).
- **An item is never committed to a bin by Stage 3**, only by Stage 2's bounds
  test, so `consistency::GAC` propagates less than per-bin GAC in the load
  form (#1346).
- **Nothing reasons across the loads**: the loads are never made to sum to the
  total size (#1348), and Stage 4, off by default, prunes items only.
- **The default spends time and proof on the constant-capacity form without
  changing the fixpoint**; pass `consistency::BC` there (#1349).
- **`Upfront` is slow with a large size or many reachable sums** (#1340),
  and bigger and slower to check than `PerCall` on every instance measured
  ([Proof performance](#proof-performance)).
- **A repeated variable propagates less than it could.**
- **Large reachable sums make the diagrams, and with proofs the `Top` flags,
  large**: six lines per node per bin at the root, whether or not an inference
  ever uses them.

### Next steps

1. **Fix XCSP3's condition form** (#1345): build the bins from the union of
   the items' domains with an offset, and post the condition only on loads of
   values some item can take. Small; removes the wrong answers and the
   negative-value `UNSUPPORTED`. Add a condition-form test with `ge`.
2. **Front ends** (#1347): post the standard range constraint on `bin[i]`
   (and `load[b] >= 0`) in Glasgow's MiniZinc redefinitions, which also
   rescues the refused `var opt` models (a fact-check's scratch copy of the
   library solves them all, matching Gecode and Chuffed); catch `InvalidProblemDefinitionException`
   around `solve_with` in the XCSP3 binary (shared with #1337), answer a
   negative constant limit or load as unsatisfiable, and clamp a variable
   load's negative values, which no solution takes. Small.
3. **Commit items in Stage 3** (#1346): mirror the include-support test for
   the exclude edge, under both strategies, with the justification's roles
   swapped; add a per-bin GAC check to the suite. Small to medium.
4. **Skip Stage 3 in the constant-capacity form** (#1349): `GAC` there
   should install what `BC` installs. Trivial; saves the diagrams, the
   per-call sweep and the `Top` flags, and cannot change the fixpoint (only
   `Upfront`'s sweep infers there, and only what Stage 2 infers next).
5. **Shaw's load coherence** (#1348): one `O(m)` pass in Stage 2 with a
   one-`pol` proof. Small.
6. **Fix `Upfront`'s interior-value pass** (#1340) by sharing
   `PerCall`'s interval loop, and close its temporary level on failure (a
   scope guard, as `Knapsack`'s next step 6; not filed). Small; or retire `Upfront`, which
   is worse on every axis measured and is kept for A/B measurement and for
   #200 (its design note's reason).
7. **Hint `Upfront`'s dead-state RUPs** (#497, an open draft PR whose
   prototype reached about 14% of the ceiling; `PerCall` writes no
   dead-state lemmas) and, to save a reconstructor Stage 4's enumeration,
   carry `α` in the hint. Per the arc's rule, whether either is needed is for
   the justifier to show.
8. **Sweep the large-domain lane wider:** an `Upfront` row with a large size,
   a capacity-form row and a proof-size row.
9. **Bring the out-of-stack text into line**:
   - `dev_docs/bin-packing.md` cites CP 2024 "§4" for the knapsack encoding
     (it is §3.3), still describes a `KnapsackUpfront` variant, calls Stage 3
     per-bin GAC without the commitment caveat, and names the removed
     `bounds_only` and `upfront_proof` constructor flags (six places) where
     the API is `with_consistency` and `with_proof_strategy`;
   - `bin_packing.cc:807–810` says the item-commitment direction "needs a
     separate argument involving all OTHER bins" (it does not; #1346);
     `:993–994` calls the per-call sweep per-bin GAC, and `:994–996` says the
     two strategies draw the same inferences and differ only in the proof;
     `:369–370` says
     `emit_bin_scaffolding` "Mirrors knapsack.cc", where the function now
     lives in `knapsack_upfront.cc:177`;
   - `bin_packing.hh:20–25` and `:174–175` claim per-bin GAC, and `:104–106`
     per-bin GAC on the item variables; `:106–129` describes the removed
     `bounds_only` and `upfront_proof` selectors; `:38–39` and `:180–183` say
     the proof strategy has no effect with proof logging off (it picks the
     Stage 3 code path: 60 s against 0.1 ms in [Interval
     efficiency](#interval-efficiency)), and `:37–38` and `:181–182` that it
     never changes the inferences (it changes them within a call, not the
     fixpoint); `:124–125` speaks of "joint chains", which `k = 1` does not
     have;
   - `bin_packing_test.cc:228–233` says Stage 3 achieves per-bin GAC and
     strengthens only the load form's load pruning (it prunes items' value
     `b` too), and `:160–164` says the edge-of-range shapes' rows cannot be
     written with a proof, where the rows are written and verify and the
     throws come from `GAC`'s Stage 3 ([Overflow](#robustness-and-limits)).

## Prior art

**Propagation.** Shaw (*A Constraint for Bin Packing*, CP 2004, LNCS 3258,
648–662) defines the constraint with load variables and gives its rules, which
this family follows in part. Stage 2 is his §2.5 "basic" propagation: load
maintenance (`loads[b]` between the packed and the possible sizes) and single
item elimination and commitment. The third of his four basic rules (after
Pack All and load maintenance), load and size coherence (the loads sum to the
total size), which he calls "[the] only rule which communicates information
between different bins" (aside from the implicit one that an item packed in
one bin leaves the others), is not implemented (#1348). His §3
reasons about one bin at a time and notes, citing Trick (*A Dynamic
Programming Approach for Consistency and Propagation for Knapsack
Constraints*, CP-AI-OR 2001; Annals of OR 118, 2003), that GAC on the single
bin is achievable, with three rules: commit an item every packing uses,
eliminate one none uses, and remove load values no packing reaches. Stage 3 is
that, by Trick's programme, minus the commitment rule (#1346); Shaw himself
uses a cheaper incomplete test (`NoSum`, over "neighboring subsets") instead
of the programme. His §4 adapts Martello and Toth's L2 bound (*Lower Bounds and
Reduction Procedures for the Bin Packing Problem*, Discrete Applied
Mathematics 28(1):59–70, 1990) to a partial assignment, by turning it into a
fixed-capacity instance with one item per bin to "top up" its capacity
(§4.1). **Stage 4 is not that
construction**: it is a family of rounded counting bounds, one per threshold,
each a single cutting-planes derivation, which shares L2's idea (count the
items above a size threshold against how many each bin can hold) and adds
domain-awareness (an item that can only go in some bins pays `c_i (|D_i| − 1)`)
and shaving, the construction of item rules from a pruning rule that Shaw's
§3.4 takes from Gent and Walsh (IJCAI 1997). `dev_docs/bin-packing.md` and the
header call it "in the family Shaw (CP 2004) §4 describes", which is the right
strength of claim. Gecode's `binpacking` propagator implements Shaw's rules,
coherence and L2 included (`gecode/int/bin-packing/propagate.cpp` in 6.3.0).

**Cardinality.** Schaus, Régin, Van Schaeren, Dullaert and Raa (*Cardinality
Reasoning for Bin-Packing Constraint: Application to a Tank Allocation
Problem*, CP 2012, LNCS 7514, 815–822), Pelsser, Schaus and Régin
(*Revisiting the Cardinality Reasoning for BinPacking Constraint*, CP 2013,
LNCS 8124, 578–586) and Derval, Régin and Schaus (*Improved Filtering for the
Bin-Packing with Cardinality Constraint*, Constraints 23:251–271, 2018) add
per-bin cardinality variables and filter them jointly with a global
cardinality constraint, or by a flow. This audit and its fact-check checked
their bibliographic details and abstracts, not their full texts. Nothing here has cardinality variables; Stage
4's counting is internal to one derivation.

**Certification.** Stage 3's derivation is the CP 2024 method (Demirović et
al., §3.3, "Knapsack as a Constraint"; McIlree's thesis, §5.2.2) at one
coordinate, as for `Knapsack`. Neither the paper nor the thesis mentions bin
packing, and this audit found no earlier certified bin-packing propagator.
What is this family's own: `PerCall`'s arrangement, flags for every node at
`Top` up front and each state-independent chain, split and terminal line
written at `Top` on first use, with every inference a bare RUP that walks the
diagram backwards by unit propagation, and an explicit refutation only for a
terminal in a hole (the arrangement that
[`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md),
in its version on main at `86caad24`, credits for this family's per-call
default; the note in this document's base predates #995); Stage 4's cutting-planes
certification of an L2-style counting bound, with the shaving hypothesis
discharged by the closing RUP; and Stage 2's rules, which are plain RUP. The
upfront arrangement is claimed once, in [`regular.md`](regular.md#prior-art),
and its phantom states in [`knapsack.md`](knapsack.md#prior-art); the copy here
keeps the per-coordinate phantom closing rule (`:552–575`) and cannot need the
joint-only case.

## Further reading

- [`bin-packing.md`](../bin-packing.md): the long design note: the staging
  (Stage 1, the checker it started as, is superseded), Stage 3's two proof
  strategies and the argument for why `PerCall`'s RUPs close, the hand-run
  mutation results for Stage 3 and Stage 4, Stage 4's derivation in full, and
  its benchmark tables from the #995 and #209 era. Some of its text is stale
  (next step 9).
- [`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md):
  upfront against per-call for `Regular`, `MDD`, `Knapsack` and `BinPacking`,
  and why this family's per-call strategy wins both axes.
- [`knapsack.md`](knapsack.md): the original of the `Upfront` copy, its rules 3
  to 7, and [`dev_docs/knapsack.md`](../knapsack.md), the upfront scaffold line
  by line.
- [`integer-ranges.md`](../integer-ranges.md): what the overflow behaviour is
  allowed to be.
