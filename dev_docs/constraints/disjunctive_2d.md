# `Disjunctive2D`: rectangles that may not overlap

> **Maturity** production (the pairwise rule); experimental (the cumulative
> relaxation, off by default and reachable from the C++ API only) ·
> **Audited** 2026-10-04 at `7e1c4178` ·
> **Open issues** #975 (the k-D scope position), #976 (the scheduling
> tracker), #868 (cross-solver comparison; this document gives one, by hand),
> #833 (the large-domain policy, through the projection's horizon arrays),
> #1223 (an overflow in `Cumulative`'s overload check, which the projection
> runs), and from this audit #1253 (a size that is also a position gives
> proofs VeriPB rejects), #1250 (the pairwise rule's overlap test), #1251
> (MiniZinc `diffn` with negative sizes), #1252 (the projection's wake-ups) and
> #1234 (presolvers over a projection donor above `AssertionLevel::Off`, shared
> with `cumulative.md`). See [Next steps](#next-steps). PR #1232 (merged
> 2026-10-04) made two of this family's coverage checks seed-independent.
> Tracked under #871.

`Disjunctive2D` is `diffn`: rectangles with variable origins and constant or
variable sizes, no two of which may share area. It has one OPB encoding: a
reified "before" flag per ordered pair and axis, and a separation clause per
pair. Every inference is justified against that encoding, except where a size
variable is also a position (#1253). By default the only
propagation is a pairwise rule. Behind `Disjunctive2DRules` it carries the 2-D
**cumulative relaxation**, which projects the rectangles onto one axis and
reasons about the `Cumulative` the projection implies. The relaxation comes in
two certified forms. Route B certifies time-tabling with a per-firing
comparator-network certificate. Route A adds the overload check, edge-finding
and TTEF, with a flagged capacity row per time point derived inside the proof.
The projection can also run `Cumulative`'s own propagator over each axis, the
whole certified ladder, and every axis that fits is published as a donor for
the three scheduling presolvers. No capacity row ever reaches the OPB. The
design and every derivation are in
[`disjunctive-proof-logging.md`](../disjunctive-proof-logging.md), which stays
as the long note; this document audits it.

Six things to know before touching it.

- **A size that is also a position gives proofs VeriPB rejects**, with default
  rules and from MiniZinc (`diffn([3,3],[1,yb],[2,yb],[2,yb])`). The answers
  are right. The pairwise push captures its position literals before the push
  lands, but reads each size's lower bound from the state inside the
  justification, so when the size is the pushed position it cites a bound the
  reason does not support. Route B's admission test counts shared positions but
  not sizes that are positions, so it admits the same shape and its certificate
  is rejected too. #1253.
- **The default rule is weaker than "pairwise".** Two rectangles count as
  overlapping on an axis only when **both** have a mandatory part there and the
  parts intersect. The certificate needs only `ub(pos_i) < lb(pos_j) +
  lb(size_j)` and `ub(pos_j) < lb(pos_i) + lb(size_i)`. So a rectangle whose
  every placement covers another's compulsory part, but which has no mandatory
  part of its own, is never pushed. Two 3×3 squares, one fixed at `(3, 4)` and
  one with `x ∈ [1, 4]` and `y ∈ [2, 5]`, cannot be placed at all, and the root
  fixpoint is the posted domains. The wider test certifies with the same pols,
  and a prototype of it passes every Disjunctive2D test. Its search effect is
  large on shikaku (312 → 10 recursions on `human --autotable`) and small on
  square packing. #1250.
- **Gecode's `nooverlap` is much stronger than the default here.** Under the
  same static branching through MiniZinc, Gecode searches 4.3M nodes where
  `fzn-glasgow` searches 41.5M on one square packing, and Gecode fails a 28-in-25
  area packing at the root where `fzn-glasgow` searches 109,043 nodes. No
  frontend can turn the relaxation on, and with it on, under the same
  branching, the same instances close in 1 to 9,221 recursions (an enumeration
  of 4,608 packings is the largest).
- **Route B and route A are proof designs as much as propagators.** Route B's
  certificate is per firing, at `Temporary`, so its proofs grow with the number
  of firings: 751 MB on a 4,608-solution enumeration. The projection caches a
  capacity row per time point at `Top` and cites it from every rule: 43 MB on
  the same enumeration (route A, which caches too, writes 546 MB). But the
  cached rows appear to make those proofs **slower** to check, 111 s and 141 s
  against route B's 54 s; the mechanism is untested. Smaller is not faster
  here.
- **The relaxation is admitted from the model, never the state.** Membership,
  the resource window, the declared size floors and whether a row's network
  fits are all settled in `prepare()`. That keeps proofs-on and proofs-off runs
  drawing the same inferences. There is one exception, and it is in the
  presolvers' use of the projection. At any assertion level above `Off`,
  `InferredDisjunctive` and `InferredCumulative` install nothing over a
  projection donor, though they do with proofs off. `CumulativeStrengthening`
  aborts the solve with an exception wherever it would strengthen something,
  and otherwise posts nothing, as it does with proofs off. #1234.
- **`cumulative_projection` inherits `Cumulative`'s horizon arrays.** The
  default pairwise rule passes the large-domain audit as `Clean`. The
  projection's propagator allocates an array over the time axis's span on every
  call: 8.4 GB for four rectangles 2²⁸ wide side by side, and `std::bad_alloc`
  at 2⁴⁰. Only the time axis's span matters, so tall rectangles projected onto
  y trip it too. The audit row
  never turns the projection on.

## What it is

### Semantics

`Disjunctive2D(xs, ys, widths, heights)` says that rectangle `i` occupies
`[xs[i], xs[i] + widths[i]) × [ys[i], ys[i] + heights[i])` and that every pair
is separated in at least one direction:

```
xs[i] + widths[i] ≤ xs[j]  ∨  xs[j] + widths[j] ≤ xs[i]  ∨
ys[i] + heights[i] ≤ ys[j]  ∨  ys[j] + heights[j] ≤ ys[i]
```

- **Strict, the default** (`with_strict(true)`): every rectangle takes part,
  including one of zero width or height. A zero-width rectangle inside another
  is a violation, as MiniZinc's `diffn` and XCSP3's `zeroIgnored = false` say.
- **Non-strict** (`with_strict(false)`): a pair is exempt when either rectangle
  has zero width or zero height (`diffn_nonstrict`, `zeroIgnored = true`). A
  rectangle whose width or height has an upper bound of 0 is dropped at
  `prepare()`.
- **Optional rectangles** (`Disjunctive2D(xs, ys, widths, heights,
  presences)`): rectangle `i` takes part only when `presences[i] = 1`. An absent
  rectangle occupies nothing and its origin is unconstrained. A presence must be
  a `{0, 1}` variable or the constant 0 or 1, or the constructor (constants) or
  `prepare()` (variables) throws `InvalidProblemDefinitionException`. A constant
  1 encodes exactly as the non-optional form, and a constant 0 drops the
  rectangle entirely.
- **Sizes must be non-negative.** A negative constant throws in the
  constructor, and a variable whose declared lower bound is negative throws in
  `prepare()`. MiniZinc's standard library does not require this (see
  [Concrete constraints](#concrete-constraints-and-frontend-coverage)).
- **Degenerate shapes.** Arrays of different lengths throw. With fewer than two
  rectangles left after the drops, `prepare()` returns false and nothing is
  installed (the `{}` and single-rectangle fixtures in `disjunctive_2d_test`).
  Constant origins are allowed: they have no bound to push, and a placement
  that would have needed one is refuted as an overlap.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Disjunctive2D` (strict) | ✓ `fzn_diffn` → `glasgow_diffn`[^mzn] | ✓ `noOverlap` 2-D with `zeroIgnored = false`, constant or variable lengths[^xcsp] | ?[^gcspy] | ✓ `disjunctive2d_strict` | default rules only from every frontend |
| `Disjunctive2D` (non-strict) | ✓ `fzn_diffn_nonstrict` → `glasgow_diffn_nonstrict` | ✓ `noOverlap` 2-D with `zeroIgnored = true` | ?[^gcspy] | ✓ `disjunctive2d` | |
| optional `Disjunctive2D` | `unsupported`: `diffn` takes no `var opt` origins | `unsupported`: XCSP3 has no optional `noOverlap` | ?[^gcspy] | ✓ `disjunctive2d_optional`, `disjunctive2d_strict_optional` | API and `.scp` only |
| k-D `diffn_k`, `diffn_nonstrict_k` | `decompose`: the standard library's pairwise disjunction of reified linear inequalities[^k] | `unsupported` for k ≠ 2 (`report_unsupported`, citing the closed #146)[^xcsp] | — | — | out of scope (#975) |
| reified `diffn` | `decompose`: the standard library's `fzn_diffn_reif` | n/a | — | — | |
| `Disjunctive2DRules` (the relaxation, the projection) | `unsupported`: no flag reaches it | `unsupported` | — | not recorded: `.scp` carries no rule selection | C++ API and `examples/squares` only |

[^mzn]: `minizinc/mznlib/fzn_diffn.mzn` and `fzn_diffn_nonstrict.mzn` bind
both forms; `fzn-glasgow` posts `Disjunctive2D{xs, ys, widths, heights}` with
default rules. A size whose domain reaches below zero is accepted by
MiniZinc's standard-library `diffn` and refused by `Disjunctive2D`: on
`var -1..2` widths, Chuffed (the standard decomposition) and a brute force of
the library's predicate find 1,224 solutions, Gecode finds 657 (it restricts
sizes to be non-negative), and `fzn-glasgow` reports `=====ERROR=====`
("widths must be non-negative"). #1251. The zero-width strict case agrees
across all three (3 solutions on the probe `zero.mzn`).

[^xcsp]: `xcsp/xcsp_glasgow_constraint_solver.cc`, the two
`buildConstraintNoOverlap` overloads for constant and variable lengths. Each
raises an unsupported error if any origin or length list is not of size two.
Covered by the `no_overlap_2d` and `no_overlap_2d_var` XCSP3 tests;
`no_overlap_var` is the 1-D form, which goes to `Disjunctive`.

[^gcspy]: `gcspy` binds nothing in this family, nor in `Cumulative` or
`Disjunctive`.

[^k]: Checked on a 3-D model of three boxes in `{0, 1}³`: `fzn-glasgow` and
Chuffed both find 188 solutions, and the FlatZinc `fzn-glasgow` receives is
18 `int_lin_le_reif` and 3 `bool_clause`.

### Options

`with_strict(optional<bool>)`, default `true`. It changes the **OPB model**,
and has to: it is part of the constraint's meaning. Non-strict mode adds a
zero-size escape flag for every variable size, whatever its bounds, because
`cake_pb_cp` adds one for every variable-size argument, and a gated escape
changed a labelled row's content (#482).

`with_rules(Disjunctive2DRules)`. Every field selects propagation strength
only. None changes the OPB, and none changes the solutions:

| Field | Default | Rules | Note |
|---|---|---|---|
| `cumulative_relaxation` | off | `relaxation-overflow`, `relaxation-push-lower`, `relaxation-push-upper` | route B: time-tabling on each axis's projection |
| `relaxation_overload` | off | `relaxation-overload` | route A |
| `relaxation_edge_finding` | off | `relaxation-edge-finding-*` | route A |
| `relaxation_time_table_edge_finding` | off | `relaxation-ttef-*` | route A; reaches what edge-finding reaches |
| `relaxation_max_span` | `nullopt` | caps the three route A rules | declines any window wider than the cap, proofs on or off (#1098) |
| `cumulative_projection` | `nullopt` | `projection` | `optional<CumulativeRules>`: runs `Cumulative`'s propagator, with those rules, on each axis |

The pairwise rule and the strict-mode zero-area leaf check are always on. They
are what makes the propagator a checker.

**Why everything else is off by default.** Route B's sweep is cubic in the
rectangles per call and is paid whether or not it fires: the header records
1.74× wall clock, proofs off, on an instance where it prunes 0.4% (not
re-measured here). Route A's certificates are linear
in a window's span (#1098), which is why its cap exists. And no frontend has a
benchmark that wants any of them yet. Under the MiniZinc model's static
branching, the squares benchmarks below take 41.5 million recursions with the
pairwise rule and 203 with route B. Under `examples/squares`' own search the
same instance takes 14,875 and 29. So this is a default worth revisiting once a
frontend can reach it.

`with_proof_mutation(Disjunctive2DProofMutation)` is a test hook
(`gcs/constraints/innards/disjunctive_2d_mutations.hh`). It corrupts route A,
route B or the projection's row certificate. All but one leave the inference
alone. `EdgeFindingOneTooFar` infers a bound one unit further than the
certificate reaches (`disjunctive_2d.cc:2170-2177`). So the header's claim that
"none of them changes the inference" (`disjunctive_2d_mutations.hh:30`) is
wrong, which is an out-of-stack comment fix.

There is no `with_consistency()`: the family has no `consistency::` tags.

### Variable kinds and views

Positions, sizes and presences are `IntegerVariableID`s, and so may be
constants and views. The pairwise rule accepts all of them: its certificates
cite order-literal definitions, which views have. What the relaxation admits
is narrower, and is settled per rectangle and per axis in `prepare()`
(`disjunctive_2d.cc:357-417`). Both positions and any variable size must be
**plain variables**, because route B names their literals in a guard and
weakens with them. The resource-axis position must be non-negative, with
`ub + floor < 2⁴⁰`. The resource-axis size needs a declared floor of at least
1. A presence must be a plain variable that no other rectangle shares, and a
position must be one no other rectangle uses. A rectangle that fails any test
takes no part in the relaxation on that axis, which only weakens it. The
projection then also needs a positive declared time-axis size, and an axis
whose resource window fails `ComparatorNetwork::fits_optional_tasks` (from
zero, ending at 2³¹ or later) runs no route A rule and no projection.

The proof handles everything the propagator accepts, with one exception: a
size variable that is also a position, its own or another rectangle's (#1253).
The pairwise push and route B then write proofs VeriPB rejects. No rule is
weakened when proofs are on.

### Reification

None. MiniZinc's `fzn_diffn_reif` decomposes. No reified form is wanted that
this audit knows of; it did not survey the corpus for reified `diffn`.

### Relation to other families

- **Into this family.** MiniZinc `diffn`, `diffn_nonstrict`; XCSP3 2-D
  `noOverlap`; `.scp` `disjunctive2d*`. Nothing decomposes into it.
- **Child constraints.** None. With `cumulative_projection` the constraint
  installs `Cumulative`'s **propagator** (`propagate_cumulative`), one per
  axis, over a `CumulativeInputs` it builds itself. That is not a posted
  `Cumulative`: there is no `Cumulative` OPB anywhere.
- **Shared code.**
  - `innards::ComparatorNetwork` (`gcs/innards/proofs/comparator_network.hh`),
    with 1-D `Disjunctive` ([`disjunctive.md`](disjunctive.md), which owns its
    description). Route B uses the pinned-duration mode with guarded separations
    (`assume_with_guarded_separations`). Route A and the projection use the
    optional-task mode (`add_optional_task`, `add_optional_separation`) with its
    parking rows. The one fact taken from it is the lemma that **pairwise-disjoint
    intervals inside a window have total length at most the window**, at unequal
    lengths.
  - `propagate_cumulative`, `CumulativeInputs`, `cumulative_task_window`,
    `prepare_cumulative_overload_check`, `cumulative_flag`,
    `ensure_cumulative_flags_defined` and `per_time_{before,after,active}_says`,
    with `Cumulative` ([`cumulative.md`](cumulative.md)). The projection defines
    its flags with the same three statements a start-checkpoint `Cumulative`
    uses.
  - `publish_cumulative_donor` and `PublishedCumulativeDonor`
    (`gcs/constraints/cumulative/donor_view.hh`), owned by `cumulative.md`.
  - `window_energy::derive_guarded_window_energy` and `window_energy_bound`, with
    `Disjunctive`'s edge-finding and `Cumulative`.
  - `task_presence`, with `Disjunctive` and `Cumulative`.
- **Presolvers.** None rewrites a `Disjunctive2D`. But `CumulativeStrengthening`,
  `InferredCumulative` and `InferredDisjunctive` read each axis's projection as a
  **donor** (#973, #1136), whether or not `cumulative_projection` is set. See
  [A projection as a presolver donor](#a-projection-as-a-presolver-donor) and the
  three presolver documents.
- **Reachability.** Every frontend reaches the pairwise rule. Only the C++ API
  and `examples/squares` reach the relaxation.
- **The family split.** The template's provisional list put this in
  `disjunctive.md`. It has its own document because the relaxation, its two
  routes and the projection are as large as the 1-D family. The two share the
  encoding's shape, the pairwise certificate and the comparator network.

## The proof model

### OPB encoding

For every unordered pair `{i, j}` of active rectangles, writing `x`, `y`, `w`,
`h` for positions and sizes and `p` for a presence:

```
bx_{i,j}  ⇔  x_i + w_i ≤ x_j            (and bx_{j,i}, by_{i,j}, by_{j,i} likewise)
bx_{i,j} + bx_{j,i} + by_{i,j} + by_{j,i}
    [ + zw_i + zh_i + zw_j + zh_j ]      (non-strict, each variable size)
    [ + [p_i = 0] + [p_j = 0] ]          (optional rectangles)        ≥ 1

zw_i  ⇔  w_i ≤ 0,   zh_i  ⇔  h_i ≤ 0       (non-strict, each variable size)
```

Each `⇔` is `add_two_way_reified_constraint` (two rows) or
`create_proof_flag_fully_reifying`. A constant size folds into the right-hand
side, as in `x_i − x_j ≤ −w_i`. A variable size stays as a term, and its bound
row cancels it in a justification. No proof-only `end = pos + size` variable
exists.

The encoding is **definitional**: it is the `diffn` predicate, and nothing in
it is a consequence. Its size is `4 · C(n, 2)` reified inequalities (two rows
each, so eight rows per pair) plus `C(n, 2)` clauses. Each inequality has as many terms as its operands have
bits, so the encoding is quadratic in `n` and logarithmic in domain width. No
row mentions a time point. The relaxation's capacity rows are not in the OPB
and cannot be: they would be a second encoding, which `cake_pb_cp` could not
re-derive from the `.scp` (the one-encoding rule).

### Labels

- `@x[id][i_j][bx][r]` and `@x[id][i_j][by][r]` name the forward halves
  (`flag → pos_i + size_i ≤ pos_j`). Every pairwise pol cites one by name
  (`pol @x[_1][0_1][bx][r] …`). Route B, route A and the projection's row
  deriver cite them as `forward_line`s.
- `@c[id][i_jsepal1]` is the separation clause. Route B adds it into each
  pair's derived clause; the pairwise rules' closing RUP finds it unnamed.
- `@x[id][i][zw][…]` and `@x[id][i][zh][…]` are the escape flags' definitions;
  rules pin the flags rather than citing the rows.

The names match `cake_pb_cp`'s (`bx`, `by`, `zw`, `zh`, `sepal1`), which is
what lets a proof cite them after the chain re-derives the OPB.

### Cake conformity

`cake_pb_cp` parses `disjunctive2d` and `disjunctive2d_strict` (its `strct`).
Four SCP chain cases run at strictness `none`:
`disjunctive2d_sat`, `disjunctive2d_unsat`, `disjunctive2d_var_sat` (one
variable width, non-strict) and `disjunctive2d_strict_sat` (a zero-width
rectangle inside a wider one, 67 solutions against 81 non-strict). They stay at
`none` because the ordering rows reference the operands' bit encodings, which
still differ from cake's eager encoding (#358). The optional forms have **no
cake encoder**. Their `constraint_type()`s, `disjunctive2d_optional` and
`disjunctive2d_strict_optional`, are named apart so that the gap is a miss,
not a silent mismatch.

The chain lanes run default rules only, since an `.scp` carries no rule
selection. This audit ran the chain by hand (the probe writes the `.scp`, then
`cake_pb_cp`, `veripb --elaborate` and the cake core check) on one instance per
rule. That covered a pairwise contradiction, both pushes, non-strict variable
sizes, the zero-area leaf, route B's overflow and push, route A's overload,
edge-finding and TTEF, and the projection under time-tabling and the overload
check. **Every one verified at both steps.** So the relaxation's in-proof rows
are derivable from cake's OPB as well as ours, though no suite lane says so.

### Proof-time state

- **In the OPB:** the before flags, the escape flags and the clauses above.
  Nothing else.
- **Introduced in the proof, at `Top`, never deleted.**
  - Route A's activity flags. Each is `red` over the time-axis order literals
    (and the presence, for an optional rectangle), with all three or four halves
    emitted, so it is fixed by unit propagation on any solution. They are minted
    by `create_proof_flag("d2act")` and so are **named by a counter**
    (`f[84][d2act]`), not by `(rectangle, time)`. An external tool cannot find
    one by name, only by reading its definition.
  - The flagged row per time point (`row_at`).
  - The guarded window energies.
  - The declared-floor units `size ≥ floor` and `~escape`.
  - The floor-cancelled separation rows (`separation_at_floor`).
  All are keyed in a `RelaxationOverloadCache` the propagator captures, and all
  are valid for the rest of the proof.
- **The projection's flags.** These are named, not minted. `define_proof_model`
  publishes a flag family that answers for `Cumulative`'s keys (`cb`, `ca`,
  `cact`) at position `axis · n + i`, for the times in each projected task's
  window. They appear as `v[id][pos_t][cact]`. An install initialiser publishes
  the definer, which emits the three `red` definitions on first lookup, as a
  start-checkpoint `Cumulative` does (#1111), and a derived-line family per axis
  (`projx`, `projy`). That family derives the capacity row at `t` the first
  time something cites it and caches it at `Top`. **Both are published only at
  `AssertionLevel::Off`** (`disjunctive_2d.cc:706`). See #1234
  and [A projection as a presolver donor](#a-projection-as-a-presolver-donor)
  for what that does to a presolver.
- **At `Temporary`:** every pairwise pol, route B's whole certificate
  (including the comparator network's fresh wires), and route A's per-firing
  energies and pins. All are deleted on backtrack. None is needed later, since
  every later firing rebuilds its own.
- **The literal layer.** Route B states each member's time bounds at
  `t − len + 1` and `t`, and route A's flags and energies cite literals at
  window edges. Both mint order atoms the encoding had no use for, each with two
  `red` rows and a pin, at `TopAndCore`. Some fall outside the domain, such as
  `i[_1][ge-1]` in the overload probe.
- **Dangling when proofs are off.** `_before_x`, `_before_y`, `_clause_lines`
  and `_zero_w` / `_zero_h` are filled by `define_proof_model`, so with proofs off
  they are empty. The propagator reads them only inside justifications, which
  then never run. The relaxation's caches are touched only inside
  justifications too.

## The implementation

### Initialisation and global data

`prepare()` is `O(n)` plus two `std::map`s over the positions and presences. It
resolves presences, size snapshots, the active set, the escape set, the
relaxation's members per axis, the resource windows, the declared floors and
whether each axis's row network fits. It also builds each axis's projection
`CumulativeInputs`. That last build is `O(n)` unless `cumulative_projection`
has the overload check on: then `prepare_cumulative_overload_check` sizes a
prefix array by the **time axis's declared span** (`cumulative.cc:500-512`).
`define_proof_model` writes the `O(n²)` encoding.

`install_propagators` publishes each fitting axis as a donor (always), installs
the projection propagators (when asked) and the projection's initialiser (when
a projection resolved), then the main propagator.

No root cost dominates on a packing-shaped instance. The projection's prefix
array is the root cost that does dominate on a wide time axis; see
[Interval efficiency](#interval-efficiency).

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| main | `on_bounds`: every active rectangle's `x`, `y`, and each variable `w`, `h`; `on_instantiated`: each variable presence | derived | `pairwise-*`, `zero-area-leaf`, `relaxation-*` | always; the relaxation rules by `Disjunctive2DRules` | not claimed | until backtrack, after a contradiction |
| projection, one per axis | `on_bounds`: that axis's projected starts | derived | `projection` (`Cumulative`'s rules) | `cumulative_projection` set, and the axis's window fits | not claimed (`Cumulative`'s) | as `Cumulative` |
| projection initialiser | — | — | none (definitions, derived rows) | a projection resolved on either axis; a logger at `AssertionLevel::Off` | n/a | n/a |

- **Self-disabling.** The main propagator returns `DisableUntilBacktrack` after
  each of its contradictions, and `Enable` otherwise.
- **Idempotence.** It never returns `EnableButIdempotent`, so it claims nothing.
  The push loop recomputes each pair's mandatory parts afresh but does not
  revisit pairs it has passed, so a push late in a pass can create work for an
  earlier pair. This audit did not build an instance showing a second call
  doing more.
- **The projection does not wake on presences.** Its triggers are the projected
  starts only. A posted `Cumulative` also wakes on `on_instantiated` for each
  presence (`cumulative.cc:919-922`), because a task joins the profile only
  once present. So an optional rectangle that becomes present is not seen until
  some start bound moves. On the `sharp` fixture with every rectangle optional,
  branching on presences first, the projection takes 37,245 recursions and 4
  failures. With the trigger added it takes 37,240 and 0. #1252.

### Mutable state and incrementality

No backtrackable state. The main propagator recomputes every mandatory part,
every route B event list and every route A window from the current bounds on
each call. Nothing is maintained, and a sweep (Beldiceanu and Carlsson's, or an
incremental profile) would be the change that buys it. The only persistent
state is proof-only: `RelaxationOverloadCache` and the projection initialiser's
`FloorCache`. Both hold `Top` lines that stay valid for the whole proof, so
they need no restore. The projection propagator's state is `Cumulative`'s.

### Interior values and optional pruning

**What this family offers.** None. It installs no optional-interior-pruning
pair.

**What this family observes.** Nothing. **The family's whole vocabulary is
bounds.** Every rule reads `lower_bound`, `upper_bound`, `bounds` or
`has_single_value`. None reads a hole, and none is woken by one. The projection
runs `Cumulative`'s propagator, which `cumulative.md` records as bounds-only
too. The declarations are the triggers' own, and they tell the truth. So a
`Disjunctive2D` keeps nobody's interior pruning alive.

### Robustness and limits

- **Unbounded domains.** Every position is bounded under the integer range
  policy (inputs within `±(2⁶⁰ − 1)`). A probe with `x` origins near `2⁵⁹`,
  `y` origins near `−(2⁶⁰ − 1)` and widths of `2⁵⁹` enumerates 96 solutions, and
  its proof verifies. The
  pairwise rule's arithmetic is a bound plus a size, at most `2⁶¹`. Route B
  admits a resource position only if `ub + floor < 2⁴⁰`. The route A rows and
  the projection need the resource window to pass `fits_optional_tasks`, which
  for a window from zero means ending before 2³¹.
- **Negative values and zero.** Negative positions are fine: the
  `disjunctive_2d_test` fixtures `neg` and `neg_wide` cover them. Negative sizes
  throw (above, and #1251). Zero sizes are the strict / non-strict split. In
  strict mode a zero-area rectangle has no mandatory box, so the pairwise rule
  skips it, and `zero-area-leaf` catches one inside another once both are
  fixed. A zero-size rectangle is skipped on the axis it spans nothing on, and
  the relaxation drops a rectangle whose declared floor is 0 on the axis that
  needs it.
- **Degenerate shapes.**
  - Fewer than two rectangles: nothing is installed.
  - An aliased position (two rectangles sharing `x`): the pairwise rule takes
    it, captures every position bound before a push lands and cites the
    captured literals, and `disjunctive_2d_test`'s `dup` lane enumerates it. The
    relaxation excludes both rectangles.
  - **A size that is also a position** is not handled. The push does not
    capture size bounds, and route B does not count sizes as uses, so both
    write proofs VeriPB rejects (#1253). An aliasing fuzz
    (`tmp/fd-sched/factcheck/disjunctive_2d/alias/alias.cc`) gives one or
    two rejections in every 40 to 150 aliased instances.
  - A constant origin: no push, and the overlap is refuted instead
    (`constant_origin` fixture).
  - A presence shared between rectangles: the pairwise rule takes it, and the
    relaxation excludes it.
- **Overflow.** The pairwise rule cannot overflow inside the policy. Route B's
  load total is at most `n · 2⁴⁰`. Route A forms `H · (b − a)` with
  `product_if_representable` and its sums with `sum_if_representable`, and
  declines a window whose supply is past `Integer` (#1083). Every product past
  that gate is at most the supply. The projection runs `Cumulative`'s overload
  check, whose profile prefix sum can overflow (#1223). Through a projection
  that needs a time-axis span above 2³², since the resource window is capped
  near 2³¹. At that span the horizon arrays exhaust memory first, so this audit
  could not reach #1223 that way.

### Interval efficiency

1. **The propagation side.**
   - **Pairwise.** `O(n²)` per call, `O(1)` per pair. It reaches for `State`'s
     per-value iterators nowhere.
   - **Route B.** Per axis: event points `O(n)`; the overflow pass is
     `O(n²)`; the push pass tests at most the event points inside each member's
     own length, each at `O(n)`, so `O(n³)` per call. No value is walked.
   - **Route A.** Per axis, every pair (earliest start, latest completion),
     `O(n²)` windows. The overload test is `O(n)` per window, and edge-finding
     and TTEF are `O(n)` candidates × `O(n)` profile entries per window, so
     **`O(n⁴)` per call** with TTEF on. The edge-finding threshold is read off
     the window-energy lemma's shape in closed form, so no time point is
     walked; walking the candidates would cost the axis's width on every
     call.
   - **The projection: a horizon walk.** It is `propagate_cumulative`, which
     allocates `mand_load` over the current span of the tasks' windows on every
     call (`cumulative.cc:2001-2002`) and walks it. With overload on (the
     `CumulativeRules` default) its `prepare` also sizes a prefix array by the
     declared span.
     - Four rectangles fixed side by side on `x`, each `2^k` wide, with
       `cumulative_projection` and the overload check off: RSS is 12.6 MB at
       `k = 16`, 529 MB at 24, 8.4 GB and 13 s at 28, and `std::bad_alloc` at 40.
     - The same instance under route A or route B, or with no rules, stays at
       about 5 MB at `k = 40` (4.7 MB on a rerun, 6.3 MB on the first run).
     - The time axis need not be `x`. Heights of `2³⁸` projected onto `y` throw
       `bad_alloc` at the first call.
     - This is `Cumulative`'s `KnownTrip` (#833), not new code. But the
       `Disjunctive2D` audit row cannot see it.
2. **The reason side.**
   - **Pairwise.** `generic_reason` over the pair's positions and variable
     sizes, plus their presence literals. It is deferred, so with proofs off
     nothing is built, and it materialises **one literal per bound and one per
     gap**: per run, not per value. The gaps are never used by the certificate,
     which reads only bounds. `bounds_reason` would be smaller on holey domains.
   - **Route B and route A.** Their `ExplicitReason`s are built before the
     inference, with proofs on or off. Route B's has four to six literals per
     member. Route A's has two or three per rectangle it counts: two bounds and
     a presence. For edge-finding and TTEF, the pushed rectangle contributes one
     bound (its other end) and a presence. Both are `O(set)`, never width.
3. **The proof side.**
   - **Pairwise.** A firing is four `pol` derivations and one closing RUP,
     whatever the width. On the root contradiction probe the proof has 8 `pol`
     lines: the four derivations, and four literal-layer `pol`s (each followed
     by `core id -1`). The latter are order-chain links between two order
     literals on one variable (`make_pol_chain_line`,
     `names_and_ids_tracker.cc:1384-1388`), and the derivations do not cite them.
     Each line has the operands' bits as terms.
   - **Route B.** The network is `O(|S|³)` in the set, and logarithmic in the
     window through the wire width. Separately, each new `(variable, time)` pair
     mints an order atom.
   - **Route A: linear in the window's span.** A flagged row, and so a network,
     per time point cited. `energy_under_reason` emits one RUP per value at each
     window edge, over the rectangle's length. TTEF's pins are one per profile
     rectangle and time point.
     - This is #1098. The only answer is `relaxation_max_span`, a cap decided
       from the window alone. It changes the inferences, which is why it is off
       by default.
     - No form is chosen by width. There is one form, and it is per time point.
   - **The projection.** As `Cumulative`, over rows this family derives at
     `O(m³)` per time point.
4. **The audit lane.** `gcs/large_domain_audit_test.cc:770` has one row,
   `Disjunctive2D`, `Expect::Clean`: two rectangles with wide positions on both
   axes, sizes that are singleton variables `[1, 1]` (`narrow(p, 2, 1_i, 1_i)`),
   and default rules. It has no row in the proof-size
   case. **Not varied:**
   - the rules: no relaxation, and no projection, which would be `KnownTrip`;
   - sizes that range over more than one value, which put a size term into
     every ordering row and a size literal into every pairwise reason;
   - presences;
   - non-strict mode;
   - holey domains, whose gaps the reasons carry.

   One row with `cumulative_projection` would have shown the horizon array.

So the answer is: **fine at any width** for the default rule on the propagation,
reason and proof sides; fine at any width for route B and route A propagation;
**linear in the span** for route A's proofs; and **linear in the span with
proofs off** for the projection.

## Inference catalogue

Facts true of every rule:

- **One wire form.** Every assertion this family owns carries
  `hints::Disjunctive2D{originator}`, the constraint ID and nothing else:
  `::disjunctive_2d:((constraint_id _1))`. No rule has a subhint.
- **The projection's rules are `Cumulative`'s.** They carry `hints::Cumulative`,
  with `Cumulative`'s subhints and the `Disjunctive2D`'s constraint ID as
  originator (`::cumulative:((constraint_id _1) (subhint overload))`, measured;
  a time-tabling assertion has no subhint, `::cumulative:((constraint_id _1))`).
  They are catalogued in `cumulative.md`. The one entry below covers what is
  different about running them here.
- **Reconstruction, for every rule here, is `search`, and the search is short.**
  Thirteen rules share one hint. A reconstructor tells them apart by the
  conclusion's literal (none, a position bound, or a presence) and by the
  reason's shape. Pairwise reasons give both bounds of exactly two rectangles'
  variables. Route B's give tight time-axis literals at `t − len + 1` and `t`.
  Route A's give `pos ≥ a` and `pos < b − len + 1` per contained rectangle. It
  then tries the matching fixed procedure. Every procedure's data (the pair, the
  set, `t`, the window `[a, b)`, `H` from the model) is in the reason or the
  model. Nothing solver-side is needed. A subhint per rule would make every one
  `hinted`.
- **Conflicts.** Every contradiction here is an explicit `contradiction()`, so
  its assertion is `¬reason`. Every push asserts `attempted literal ∨ ¬reason`.
  Both were checked against `a` lines at `AssertionLevel::Inferences`.

### Rule: pairwise-overlap

- **Infers** — a contradiction.
- **Fires when** — the main propagator's first pass finds two present
  rectangles whose mandatory boxes intersect on both axes. The mandatory part on
  an axis is `[ub(pos), lb(pos) + lb(size))`.
- **Strength** — `partial`: pairwise intersection of compulsory parts. It is
  not `bounds(Z)` even on two rectangles. Over 1,500 random two-rectangle
  instances, 24 non-failed roots have an unsupported bound (`bz2d.cc`, seed 1).
  The instance in the summary is unsatisfiable and the root does not fail. #1250
  widens the test to the forbidden-region condition.
- **Algorithm** — `O(n²)` pairs, `O(1)` each.
- **Why it is true** — in every placement a rectangle covers its mandatory box,
  so two intersecting boxes are two rectangles sharing a cell.
- **Proof technique** — `pol`, four of them: for each axis and direction, the
  before flag's `[r]` row, plus the order-literal definitions of `pos_i ≥
  lb(pos_i)`, `pos_j < ub(pos_j) + 1` and, for a variable size, `size_i ≥
  lb(size_i)`. Saturated, each leaves `¬before` under the reason. Then the
  framework's closing `RUP`, over the separation clause with every disjunct
  false. In non-strict mode each escape is first pinned false by a `RUP` under
  the reason, since the reason states `size ≥ 1`. The derivation is ours ("justify
  directly against the declarative encoding", `disjunctive-proof-logging.md`).
  Its licence is the pols' arithmetic and clause propagation.
- **Reason** — `generic_reason` over `x_i, y_i, x_j, y_j` and every variable
  size of the two, plus `p = 1` for a present optional rectangle. That is two
  literals per unfixed variable plus one per gap, and one `eq` literal per
  fixed variable. It is not minimal: the sizes' upper bounds and any gaps go
  unused.
- **Assertion** — `¬reason`. Measured on two 2×2 squares over `{0, 1}²`:
  `a 1 ~i[_1][ge0] 1 i[_1][ge2] 1 ~i[_2][ge0] 1 i[_2][ge2] … >= 1::disjunctive_2d:((constraint_id _1));`
- **Hint** — `hints::Disjunctive2D`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `search`, as the preamble: pick the pairwise
  procedure from the reason's two rectangles, then four fixed pols.
- **Proof size** — four `pol` derivations and one RUP, constant in width: 8
  `pol` lines plus the RUP on the probe.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` No lane corrupts the pairwise derivation. The
  design note records a one-off check, not re-run here: deleting these pols
  failed `disjunctive_2d_test`'s `d1` lane. It also records that in the
  presence-falsification role (below) the pols were never load-bearing on the
  test shapes.

### Rule: pairwise-absent

- **Infers** — `p_k = 0` for an undecided optional rectangle `k`.
- **Fires when** — `pairwise-overlap`'s condition holds and exactly one of the
  pair is undecided. With both undecided nothing is inferred, and the pair is
  left to whichever presence is decided first.
- **Strength** — `partial`, as above.
- **Algorithm** — as above. The scan of `k` against later rectangles stops once
  `k` is absent.
- **Why it is true** — if `k` were present, the pair would overlap.
- **Proof technique** — as `pairwise-overlap`: the same four `pol`s, then the
  closing `RUP` leaves the six-way clause with `k`'s `[p_k = 0]` disjunct.
- **Reason** — as `pairwise-overlap`. The present partner's `p = 1` is in it,
  and `k`'s presence is not.
- **Assertion** — `[p_k = 0] ∨ ¬reason`. Measured:
  `a 1 ~i[_5][b0] 1 ~i[_1][eq0] 1 ~i[_2][eq0] 1 ~i[_3][ge0] … >= 1::disjunctive_2d:…`.
  The conclusion is the presence's single bit.
- **Hint** — `hints::Disjunctive2D`.
- **Offline reconstructibility** — `search`, as `pairwise-overlap`.
- **Proof size** — as `pairwise-overlap`, plus a proof comment (the marker the
  optional test counts).
- **Gaps** — `None.`
- **Tightness** — `Not shown`, and on the test shapes the pols are not
  load-bearing: with the pair's bounds in the reason, unit propagation refutes
  the four flags from their reification rows unaided (design note, not re-run).

### Rule: pairwise-push-lower

- **Infers** — `pos_i ≥ min(blk_hi, ub(pos_i) + 1)` on the free axis, where
  `blk_hi = lb(pos_j) + lb(size_j)` is the blocker's mandatory end.
- **Fires when** — the main propagator's second pass: both rectangles present,
  their mandatory parts intersect on one axis (the forced axis), the blocker `j`
  has a mandatory part on the other (free) axis, and `i` at its current lower
  bound would overlap that part. A zero-size `i` on the free axis, and a
  constant `pos_i`, are skipped.
- **Strength** — `partial`, as `pairwise-overlap`. #1250's wider forced-axis
  test applies here too.
- **Algorithm** — `O(1)` per ordered pair and axis, `O(n²)` per call.
- **Why it is true** — the pair cannot separate on the forced axis. With `pos_i
  ≥ cur_lo > ub(pos_j) − lb(size_i)`, `i` cannot end before `j` starts on the free
  axis. So `j` precedes `i`, and `pos_i ≥ pos_j + size_j ≥ blk_hi`.
- **Proof technique** — `pol`, four:
  - two refuting the forced axis's before flags, as in `pairwise-overlap`;
  - one refuting `before_{i,j}` on the free axis from `pos_i ≥ cur_lo`, a
    literal captured before the push lands;
  - one folding `before_{j,i}` onto the target's definition row.

  Then the closing `RUP`. The comments in `disjunctive_2d.cc` and the design
  note say "six pols"; the code emits four.
- **Reason** — `generic_reason` over both rectangles' positions and variable
  sizes, plus presence literals. The pushed position's own bounds are in it.
- **Assertion** — `[pos_i ≥ target] ∨ ¬reason`. Measured, `x_B ∈ [1, 5]` pushed
  to 2: `a 1 i[_3][ge2] 1 ~i[_3][ge1] 1 i[_3][ge6] 1 ~i[_4][eq0] 1 ~i[_1][eq0] 1 ~i[_2][eq0] >= 1::disjunctive_2d:…`.
- **Hint** — `hints::Disjunctive2D`.
- **Offline reconstructibility** — `search`. The pair is in the reason; which
  axis is forced is a choice of two.
- **Proof size** — four `pol`s and one RUP, constant in width and in the
  blocker's size.
- **Gaps** — **A rejected proof** when a size variable is also a position
  (#1253). The justification reads `size ≥ lb(size)` from the state after the
  push has landed, so if the size is the pushed position, the pol cites a bound
  the reason does not support. Positions are captured, sizes are not
  (`disjunctive_2d.cc:940-941`). The answers stay correct.
- **Tightness** — `Not shown`, by a lane. The design note's one-off check above
  covers the push role too.

### Rule: pairwise-push-upper

- **Infers** — `pos_i ≤ max(blk_lo − lb(size_i), lb(pos_i) − 1)`, where `blk_lo
  = ub(pos_j)`.
- **Fires when** — as `pairwise-push-lower`, with `i` at its current upper bound
  overlapping the blocker's mandatory part. The two are exclusive per call: the
  lower push is tried first.
- **Strength**, **Algorithm**, **Reason**, **Hint**, **Proof size**, **Gaps**,
  **Tightness** — as `pairwise-push-lower`.
- **Why it is true** — the mirror: `j` cannot precede `i`, so `i` precedes `j`.
- **Proof technique** — the mirror's four `pol`s, then `RUP`.
- **Assertion** — `[pos_i < target + 1] ∨ ¬reason`. Measured, `x_B ∈ [−3, 1]`
  pushed to −2: `a 1 ~i[_3][ge-1] 1 ~i[_3][ge-3] 1 i[_3][ge2] … >= 1::disjunctive_2d:…`.
- **Offline reconstructibility** — `search`, as `pairwise-push-lower`.

### Rule: zero-area-leaf

- **Infers** — a contradiction.
- **Fires when** — strict mode only: a present, fully fixed rectangle with zero
  width or height, and a present, fully fixed other rectangle, are not
  separated.
- **Strength** — `checker` for strict zero-area rectangles. Before both are
  fixed, nothing is inferred about them.
- **Algorithm** — `O(n²)` per call, over fixed rectangles.
- **Why it is true** — strict `diffn`: a zero-area rectangle still may not lie
  inside another.
- **Proof technique** — `RUP` (`JustifyUsingRUP`). Every before flag of the pair
  is false by its reification under the fixed values, so the clause fails.
- **Reason** — `generic_reason` over the pair's variables, all fixed.
- **Assertion** — `¬reason`. Measured, a zero-width rectangle at `(1, 1)` inside
  a fixed 3×3: `a 1 ~i[_3][eq1] 1 ~i[_4][eq1] 1 ~i[_1][eq0] 1 ~i[_2][eq0] >= 1::disjunctive_2d:…`.
- **Hint** — `hints::Disjunctive2D`.
- **Offline reconstructibility** — `offline` once the rule is known; `search`
  under the shared hint.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: relaxation-overflow

- **Infers** — a contradiction.
- **Fires when** — `cumulative_relaxation` (route B), on either axis as time.
  At some event point `t`, the members known present whose time-axis mandatory
  parts cover `t` are two or more, and their resource-axis floors sum to more
  than the window they span, `max(ub(r) + floor) − min(lb(r))`.
- **Strength** — `partial`: time-tabling on the projection, over the mandatory
  set, with each resource size at its declared floor. Brute force over 1,500
  three-rectangle instances still finds 74 roots with an unsupported bound.
- **Algorithm** — per axis, `O(n)` event points × `O(n)` per load, `O(n²)`.
- **Why it is true** — the members all cover `t`, so no two can be separated on
  the time axis. By the separation, every pair is separated on the resource
  axis. Intervals pairwise disjoint inside a window have total length at most
  the window (the comparator network's lemma), and each rectangle is at least
  its floor tall.
- **Proof technique** — `pol` + `sorting network` + `RUP`.
  - **Per pair:** two `pol` refutations of the time-axis before flags from the
    tight literals `pos ≥ t − len + 1` and `pos < t + 1`. These cancel to a
    clause because the literals are stated tightly. They are added to the pair's
    `sepal1` clause and weakened with literal axioms up to the whole guard. That
    gives the pair's resource-axis separation under the guard.
  - **Then:** `ComparatorNetwork`, pinned-duration mode, with
    `assume_with_guarded_separations`. It sorts the set's resource positions
    and telescopes to "the window is at least as tall as its contents". Each
    separation row is handed over at the floor (`separation_at_floor`,
    saturated). Each escape is pinned under the reason as well as carried in
    the guard. The closing `RUP` reads the conflict off the guarded row.
  - **Licence:** #730's construction, verified in simulation and then in
    `comparator_network_test`, and the guarded-separation discipline of #982
    (a clause carries the guard at 1, a row at `big()`). The argument is ours.
- **Reason** — per member: the tight time literals, its resource bounds, a
  variable time-size's `size ≥ len`, and `p ≠ 0`. That is four to six literals
  per member, an `ExplicitReason`. Every literal is one the certificate
  cites; whether a smaller reason would do was not checked.
- **Assertion** — `¬reason`. Measured, three 3×3 rectangles over `x ∈ [0, 2]`,
  `y ∈ [0, 5]`:
  `a 1 ~i[_1][ge0] 1 i[_1][ge3] 1 ~i[_2][ge0] 1 i[_2][ge6] … >= 1::disjunctive_2d:…`.
- **Hint** — `hints::Disjunctive2D`.
- **Offline reconstructibility** — `search`: the reason gives the set, the
  axis, `t` and the window; the network is fixed by them.
- **Proof size** — `O(|S|³)` lines per firing, at `Temporary`, plus two
  pair-refutation `pol`s and a weakening per pair. That is logarithmic in the
  window, through the wire width. Not measured per firing here. (The design
  note's `1.4 KB·n³` is route A's flagged row, not this certificate.)
- **Gaps** — **A rejected proof** when a size variable is also a position.
  `prepare()` counts shared positions (`position_uses`, `disjunctive_2d.cc:359-365`)
  but not sizes, so such a rectangle is admitted, and its network certificate is
  rejected (#1253).
- **Tightness** — Shown. `emit_nothing` (the control), `skip_refutation` and
  `skip_guard_weakening` are each rejected on `sharp`. `skip_presence_guard` is
  rejected on `sharp` with presences fixed to 1. `skip_resource_floor` and
  `resource_skip_floor_escape_pins` are rejected on `sharp` with heights over
  `[h, h + 2]`.
  `skip_escape_pins` is rejected on a non-strict instance with two escapes in
  one firing; one escape, or a size whose bound forces a bit, passes and says
  nothing. All 23 registered lanes were re-run for this audit, and every one was
  rejected.

### Rule: relaxation-push-lower

- **Infers** — `pos_j ≥ t + 1` on the time axis, for the largest blocked `t`
  within `j`'s length of its lower bound.
- **Fires when** — route B: `j` is a present member whose own mandatory part
  does not cover `t`, and adding it to the set at `t` overflows. Only the
  range's ends and the event points' edges are tested, since the verdict is
  constant between event points.
- **Strength** — `partial`, as `relaxation-overflow`.
- **Algorithm** — `O(n)` candidate times × `O(n)` per load, per member: `O(n³)`
  per call per axis.
- **Why it is true** — `j` occupying `t` overflows the window, so `j` cannot
  cover `t`, and starting at or before `t` within its length would cover it.
- **Proof technique** — as `relaxation-overflow`. `j`'s upper tight literal,
  `pos_j < t + 1`, is not in the reason: it is the negated conclusion, so the
  guarded row carries it and the closing `RUP` reads the push off it. The conclusion literal is
  strictly inside the domain, so a push never empties it.
- **Reason** — as `relaxation-overflow`, less the pushed member's
  `pos < t + 1`.
- **Assertion** — `[pos_j ≥ t + 1] ∨ ¬reason`. Measured on the `push` fixture,
  `x_2` pushed past `t = 2`, with its reason literal `x_2 ≥ 0` (`t − len + 1`)
  and no upper one:
  `a 1 i[_5][ge3] 1 ~i[_1][ge2] 1 i[_1][ge3] 1 ~i[_2][ge0] 1 i[_2][ge6] … 1 ~i[_5][ge0] 1 ~i[_6][ge0] 1 i[_6][ge6] >= 1::disjunctive_2d:…`.
- **Hint**, **Offline reconstructibility**, **Proof size**, **Gaps** — as
  `relaxation-overflow`.
- **Tightness** — The `push`, `push_at_zero` and `push_transposed` fixtures
  verify and fire. No mutation targets the push form alone.

### Rule: relaxation-push-upper

- **Infers** — `pos_j < t − len + 1`, for the smallest blocked `t` at or after
  its upper bound.
- Every other field — the mirror of `relaxation-push-lower`. The negated
  conclusion is `pos_j ≥ t − len + 1`, which is what the reason leaves out. The
  assertion is `[pos_j < t − len + 1] ∨ ¬reason`.

### Rule: relaxation-overload

- **Infers** — a contradiction.
- **Fires when** — `relaxation_overload` (route A), on an axis whose window fits.
  Some window `[a, b)` (an earliest start and a latest completion among the
  present members with positive declared time-axis floors), no wider than
  `relaxation_max_span`, contains rectangles whose `Σ floor_t · floor_r`
  exceeds `H · (b − a)`. `H` is the model's resource extent.
- **Strength** — `partial`: the overload check on the projection, at the floors.
- **Algorithm** — `O(n²)` windows × `O(n)`.
- **Why it is true** — at each time point the rectangles active there are
  pairwise separated on the resource axis, so their heights sum to at most `H`.
  Summed over `[a, b)`, the window supplies `H · (b − a)`, and each contained
  rectangle uses at least `floor_t · floor_r` of it.
- **Proof technique** — `redundance`, `sorting network`, `RUP sequence`, `pol`.
  - **`redundance` (once per `(i, t)`):** activity flags
    `act ⇔ pos ≥ t − len + 1 ∧ pos < t + 1 [∧ p = 1]`, `red` at `Top`.
  - **`sorting network` (once per `t`, at `Top`):** the flagged row
    `Σ h_i·act_{i,t} ≤ H`, from `ComparatorNetwork`'s optional tasks. An inactive
    rectangle is a zero-height dummy parked at the window's top, and each
    pair's `¬act_i ∨ ¬act_j ∨ before ∨ before` is a `RUP` after two pair
    refutations.
  - **`RUP sequence` (per firing):** each contained rectangle's energy, from the
    flags' backward rows telescoped over `[a, b)` plus edge literals under the
    reason, one `RUP` per value at each edge.
  - **`pol`:** the rows and `height ×` energies, summed.
  - **Licence:** the network as above. The time-indexed overload certificate is
    1-D `Disjunctive`'s (#737) with heights.
- **Reason** — per contained rectangle `pos ≥ a`, `pos < b − len + 1`, and
  `p = 1`.
- **Assertion** — `¬reason`. Measured on seven 2×2 in 5×5:
  `a 1 ~i[_1][ge0] 1 i[_1][ge4] … 1 ~i[_13][ge0] 1 i[_13][ge4] >= 1::disjunctive_2d:…`.
- **Hint** — `hints::Disjunctive2D`.
- **Offline reconstructibility** — `search`. The window and the set are in the
  reason. A reconstructor mints its own activity flags, which Appendix C
  allows.
- **Proof size** — `O(m³)` per new time point's row (`m` members able to cover
  `t`), cached. Per firing, `(b − a)` row citations plus `O(len)` edge `RUP`s
  per contained rectangle: **linear in the span** (#1098).
- **Gaps** — `None.`
- **Tightness** — Shown. `overload_emit_nothing`, `overload_skip_energy` and
  `overload_skip_row` are each rejected on `area`, and
  `overload_skip_resource_floor` on `area` with heights over `[h, h + 2]`.
  `skip_presence_conjunct` is rejected on five unit squares in a box of four,
  branching on presences first. `skip_size_floor` and `skip_floor_escape_pins`
  are rejected on `area` with widths over `[w, w + 2]`, because over `[2, 3]`
  unit propagation fixes a bit and everything verifies.

### Rule: relaxation-edge-finding-lower

- **Infers** — `pos_j ≥ T`, for a rectangle `j` starting inside a window `[a, b)`
  that its contents leave too little room for.
- **Fires when** — `relaxation_edge_finding` or TTEF on, in the same sweep as
  `relaxation-overload`. `j` has exactly one time-axis end inside the window,
  here the start, and the contained energy plus `h_j ×` `j`'s clipped energy
  for a start below `T` exceeds the supply.
- **Strength** — `partial`: edge-finding on the projection, at the floors. The
  threshold is the strongest push the cited row supports. It can go past the
  textbook `a + ⌈rest / h_j⌉`.
- **Algorithm** — `O(n)` candidates per window, with the threshold in closed
  form from `window_energy_bound`'s shape and checked once, so `O(n³)` per call
  per axis (`O(n⁴)` with TTEF's profile).
- **Why it is true** — as `relaxation-overload`, with `j`'s guaranteed energy
  inside the window for any start below `T` added.
- **Proof technique** — as `relaxation-overload`, plus `j`'s **guarded window
  energy** (`derive_guarded_window_energy`, cached at `Top`), times `h_j`, with
  its conclusion guard left standing. The sum derives the push, and the closing
  `RUP` reads it.
- **Reason** — as `relaxation-overload`, plus `j`'s other end (`pos_j ≥ a`) and
  its presence.
- **Assertion** — `[pos_j ≥ T] ∨ ¬reason`. Measured on `ef_lb`:
  `a 1 i[_7][ge3] 1 ~i[_1][ge0] 1 i[_1][ge3] 1 ~i[_3][ge0] 1 i[_3][ge3] 1 ~i[_5][ge0] 1 i[_5][ge3] 1 ~i[_7][ge0] >= 1::disjunctive_2d:…`.
- **Hint** — `hints::Disjunctive2D`.
- **Offline reconstructibility** — `search`, as `relaxation-overload`. `T` is
  the conclusion.
- **Proof size** — as `relaxation-overload`, plus one guarded energy per
  `(rectangle, window, guards)`, cached.
- **Gaps** — `None.`
- **Tightness** — Shown on `ef_lb`: `edge_finding_one_too_far` and
  `edge_finding_drop_pushed` are rejected.

### Rule: relaxation-edge-finding-upper

- **Infers** — `pos_j < L`, for a rectangle ending inside the window.
- Every other field — the mirror of `relaxation-edge-finding-lower`, on `ef_ub`.
  The reason carries `pos_j < b − len_j + 1`.

### Rule: relaxation-ttef-lower

- **Infers** — as `relaxation-edge-finding-lower`, with the mandatory-part load
  of the rectangles the window does not contain counted too, less the pushed
  rectangle's own.
- **Fires when** — `relaxation_time_table_edge_finding`. With nothing contained,
  it is time-tabling: the `ttef_lb` fixture goes 0 → 3 → 4.
- **Strength** — `partial`; subsumes the edge-finding rules.
- **Algorithm** — `O(n)` profile per candidate: `O(n⁴)` per call per axis.
- **Why it is true** — as edge-finding. Each profile rectangle is active
  throughout its mandatory part, which its bounds fix.
- **Proof technique** — edge-finding's, plus one `RUP` pin `act_{c,t} ≥ 1` per
  profile rectangle `c` and time point of its mandatory part, times `h_c`.
- **Reason** — edge-finding's, plus both bounds and the presence of every
  profile rectangle.
- **Assertion** — `[pos_j ≥ T] ∨ ¬reason`. Measured on `ttef_lb`:
  `a 1 i[_7][ge3] … 1 ~i[_5][ge1] 1 i[_5][ge4] >= 1::disjunctive_2d:…`, where
  `x_2 ∈ [1, 3]` is the profile rectangle.
- **Hint**, **Offline reconstructibility** — as edge-finding.
- **Proof size** — edge-finding's plus one pin per profile rectangle and time
  point, so linear in the span again.
- **Gaps** — `None.`
- **Tightness** — `ttef_one_too_far` and `ttef_drop_pushed` are rejected. The
  latter runs on `ttef_pushed_matters`, because on `ttef_lb` propagation closes
  the push unaided. **The pins are never load-bearing.** The unregistered lane
  `ttef_drop_pins` verifies when re-run here, as the design note's survey found
  (0 of 199 instances). They are emitted so that the closing RUP is handed its
  facts.

### Rule: relaxation-ttef-upper

- **Infers** — `pos_j < L`, the mirror. Every other field as
  `relaxation-ttef-lower`, on `ttef_ub`.

### Rule: projection

- **Infers** — whatever `Cumulative`'s propagator infers over the projection:
  time-tabling bounds and conflicts, the overload checks, edge-finding and its
  forms, not-first / not-last, presence falsification. The rules are
  `cumulative.md`'s catalogue, under `CumulativeRules`.
- **Fires when** — `cumulative_projection` is set, the axis's window fits, and
  at least two of its members have a positive declared time-axis floor
  (`disjunctive_2d.cc:472-478`). It wakes on the projected starts' bounds only
  (#1252).
- **Strength** — `partial`, as each `Cumulative` rule, over tasks of constant
  length and height (the declared floors) on a constant capacity `H`.
- **Algorithm** — `Cumulative`'s, including its horizon arrays (see
  [Interval efficiency](#interval-efficiency)).
- **Why it is true** — the projection is a `Cumulative` implied by the
  separations: a rectangle at its floors lies inside the real one, so the
  floored rectangles are pairwise disjoint and inside the window whenever the
  real ones are. At each time point the active ones are separated on the
  resource axis, so their floors sum to at most `H`.
- **Proof technique** — `Cumulative`'s certificates, unchanged, over flags and
  rows this constraint supplies. The flags are defined by `redundance`
  (`red`, on first lookup) with `Cumulative`'s statements. The capacity row at
  `t` is derived on first citation, at `Top`, by `ComparatorNetwork`'s
  optional tasks:
  - per member, two bridging `pol`s from the bit-defined `before` / `after`
    flags to order literals (`~before ∨ ~[pos ≥ t + 1]`);
  - per pair, two refutation `pol`s and a `RUP` clause;
  - the network's sort and sum;
  - an `ia` restating its endgame as exactly the row `Cumulative`'s citers sum.
- **Reason** — `Cumulative`'s (whole scope).
- **Assertion** — `Cumulative`'s. Measured on `area` with `CumulativeRules{}`:
  `a … >= 1::cumulative:((constraint_id _1) (subhint overload));`.
- **Hint** — `hints::Cumulative`, originator the `Disjunctive2D`. A
  reconstructor reading it has to know the projection: positions `axis · n + i`,
  floors, `H`, and the members. All of these are settled from the model, so
  they are recomputable.
- **Offline reconstructibility** — as `Cumulative`'s rules, once the projection
  is recomputed from the model: `search` at worst.
- **Proof size** — `Cumulative`'s, plus one network per time point cited,
  cached.
- **Gaps** — `None.` #1234 concerns presolvers, not this rule. At
  `AssertionLevel::Inferences` the projection's own assertions verify `UNDER
  ASSERTIONS`.
- **Tightness** — `projection_row_too_strong`, `projection_skip_bridge`,
  `projection_skip_refutations`, `projection_skip_size_floor` and
  `projection_skip_resource_floor` are rejected. The rules' own lanes are
  `Cumulative`'s.

### A projection as a presolver donor

This is not an inference of this constraint, but it is this family's
behaviour, and `cumulative.md` points here for it.

`install_propagators` publishes as a `PublishedCumulativeDonor` every axis whose
window fits and which has at least two members with a positive declared
time-axis floor, with proofs on or off and whether or not
`cumulative_projection` is set. It publishes rather than recomputes because a
presolver sees constraints as posted, against a state initialisers may already
have tightened. A donor carries:

- the flag-key positions `axis · n + i`;
- the starts;
- the floors as lengths and heights;
- the presences, padded with constant 1 when any member is optional;
- `H`;
- the key `CumulativeDonorKey{id, "projx" | "projy"}`.

One `Disjunctive2D` is two donors under one ID. Positions that are no task of
that axis are holes. `disjunctive_2d_presolver_test` checks all three
presolvers over projections against brute force, proofs on and off, and runs
one mutation per presolver over a projection's rows.

**At assertion levels above `Off` the presolvers fail over a projection**
(#1234). The row family and
definer are not published at those levels.
- **`InferredDisjunctive` and `InferredCumulative` decline.** On a strip of three
  2×2 squares, `InferredDisjunctive` posts one clique with proofs off and at
  `Off`, and none at `Definitions`, `Inferences` or `Backtracking`.
  `InferredCumulative` posts 5 cuts against 0. At `Inferences`,
  `InferredDisjunctive` reports `declined_by_install = 1` and
  `InferredCumulative` reports 5, one per cut
  (`tmp/fd-sched/factcheck2/disjunctive_2d/bars/probe5.cc`). Every proof verifies.
- **`CumulativeStrengthening` throws.** On the presolver test's `bars` instance
  (three 1×2 bars, `x ∈ [0, 2]`, `y ∈ [0, 3]`), it posts one derived constraint
  with no proof and at `Off` (816 solutions). At `Definitions`, `Inferences`
  and `Backtracking` the solve throws `unexpected problem: cumulative strengthening: the donor has no
  capacity row at time 0, which cannot happen for a constraint derived over all
  of its tasks` (`cumulative_strengthening.cc:512`). It throws at `Links`
  too, as `cumulative_strengthening.md` measures. It throws **only where it
  would strengthen something**. On `strip` it posts nothing at any level, with
  proofs off as well, and its proof verifies at `Definitions`, `Inferences`
  and `Backtracking`.
- **At `Links`** the consistency check (`tmp/fd-sched/factcheck/crossdoc2/d2/runs.txt`)
  finds the two declining presolvers declining as above: on `strip`,
  `InferredDisjunctive` reports `declined_by_install = 1` and
  `InferredCumulative` reports 5; on `bars`, `InferredCumulative` reports 1.
  Every one of these proofs is rejected at `Links`, for the unrelated #1210.

For a posted `Cumulative` donor, #1234 finds the proof rejected
outright. Here the presolver's output, or whether the solve completes at all,
depends on the proof options.

## Evidence

### Tests

- **Enumeration lanes.** `disjunctive_2d_constraint_{strict,nonstrict}`
  enumerate 13 hand-written and 35 random instances, plus variable-size and
  aliased cases, against a brute-force oracle. They run with proofs off and on,
  and VeriPB checks every proof. They use plain `solve_for_tests`: the family is
  not GAC, so there is no per-node GAC check.
  `disjunctive_2d_optional_constraint_{strict,nonstrict,falsify}` do the same
  for optional rectangles, the last counting falsification markers.
- **Relaxation lanes.** `disjunctive_2d_relaxation` runs every fixture with a
  **control**, the same instance one rule down, which must not reach the bound.
  Then the random sweeps: `…_search` 24 instances and `…_overload_search`,
  `…_edge_finding_search`, `…_ttef_search` and `disjunctive_2d_projection_search`
  16 each. These enumerate against brute force and verify every proof.
- **23 mutation lanes** (`disjunctive_2d_relaxation_mutation_*`), all rejected
  when re-run for this audit. `disjunctive_2d_presolver` covers the donors.
- **Probes.**
  - `route_a_probe_test`: the flagged row, derived outright.
  - `route_b_probe_test`: a guarded certificate, with a satisfiable control one
    unit looser that must fail to conclude.
  - `kd_relaxation_probe_test`: the 2-, 3- and 4-axis recursion. Nine instances
    verify and nine satisfiable controls are rejected. This is the evidence #975
    rests on.
  - the example lanes `squares`, `squares_relaxation`, `squares_projection`
    and `shikaku` (each verified), the MiniZinc `diffn`, `diffn-rotate` and
    `diffn-nonstrict` lanes against Gecode, the XCSP3 `no_overlap_2d{,_var}`
    lanes, and the four SCP chain cases.
- **Runtime caps.**
  - **The default policy:** every registered lane runs under
    `GCS_TEST_MAX_SOLUTIONS=300` and `GCS_TEST_MAX_RECURSIONS=1500` unless it
    clears them, and a truncated solve checks soundness and a partial proof
    only.
  - **They fire here.** In `disjunctive_2d_test` 16 of the 118 solves per mode
    expect more than 300 solutions, so they are truncated. In the optional test
    it is 10 of 42 in each of the strict and non-strict modes; the `falsify`
    mode's solves print no expected count. The six relaxation lanes clear both
    caps; the CMake comment says their instances are bounded by construction and
    that the test fails loudly if a cap fires. Two of the four Ubuntu CI jobs
    build with caps off.
  - **This audit's runs:** the binaries were run directly (`--seed=1` unless
    stated), with the caps set by hand where stated.
- **Seeding.** Every lane takes `--seed=N` and prints its seed. Two coverage
  checks were seed-dependent: `disjunctive_2d_presolver` needed an optional
  instance in its sweep, and `disjunctive_2d_relaxation`'s
  `optional_undecided_relaxation` needed a firing. **PR #1232** (merged
  2026-10-04) makes both hold for every seed. Measured elsewhere, not by this
  audit: the stress run behind that PR made 455,520 runs of the 111 disjunctive
  lanes (`tmp/disj-stress/main/results.tsv`), and found the two checks failing
  about 0.6% and 0.3% of the time.
- **Real instances.** None is ported into a data-driven test. `examples/squares`
  and `examples/shikaku` are the benchmarks, with one lane each (two more
  for `squares`'s relaxation and projection).

**What the tests do not cover.**

- **Sizes aliased to positions.** No lane posts a size that is also a position,
  which is how #1253's rejected proofs survived. The `dup` lane shares a
  position between two rectangles only.

- **Strength.** No lane compares the pairwise rule against a forbidden-region
  bound, which is how #1250's gap survived. The controls check that a rule
  fires, not what it misses.
- **The pairwise derivation.** It has no mutation lane at all.
- **Assertion levels.** Nothing runs at any assertion level above `Off`. Under
  `GCS_ASSERTION_LEVEL=inferences`, `disjunctive_2d_relaxation_test` stops at its
  first fixture, because it counts proof-comment markers that assertions do not
  write. `disjunctive_2d_presolver_test` stops on #1234's
  failure.
- **The chain.** No chain lane runs a relaxation rule. This audit's manual chain
  says they would pass.
- **Wide domains.** The large-domain row is default rules only. Nothing runs
  the projection on a wide axis.
- **Frontends.** No frontend lane exercises zero sizes in MiniZinc against the
  standard library rather than Gecode, or negative sizes.
- **Wake-ups.** No test measures the projection's triggers (#1252).

### Benchmarks and examples

- `examples/squares` (`--relaxation`, `--relaxation-overload`,
  `--relaxation-edge-finding`, `--relaxation-ttef`, `--projection
  default|all|<rules>`, built-in `tight`, `loose`, `area`, `perfect21`, or
  `--sizes --width --height`) is where every rule is reachable.
- `examples/shikaku` has variable sizes and default rules.
- **CPU.** Square packings around 6×6 with mixed sizes, enumerated or refuted.
  With the relaxation off and the MiniZinc model's static branching,
  `3³,2³,1³ in 7×6` is 41.5M recursions and four minutes, so a good stress for
  the pairwise rule. Under `examples/squares`' own search it is 14,875.
- **Proofs.** `3,2,2,2,1⁴ in 5×5` enumerated (4,608 packings) is the right size:
  every arm is under 13 s to solve and 2.5 minutes to verify, and the proofs
  span 35 to 751 MB.
- **`perfect21`** must never run without `--timeout`.
- **The corpus.** MiniZinc Challenge `diffn` models reach only the pairwise
  rule. This audit did not survey them.

### CPU performance

**Against Gecode** (#868), through MiniZinc 2.9.7, on the model `mzn/sq.mzn`
with `int_search(x ++ y, input_order, indomain_min)`. Both solvers ran serially
on core 60 on 2026-10-05. Gecode is the 6.3.0 bundled with MiniZinc, posting
its own `nooverlap`, and `fzn-glasgow` posts the pairwise rule. The columns are
each solver's own `nodes` and `failures` statistics, which are not defined
identically, so read them as orders of magnitude. These are two strengths
compared under one static branching, not one search tree.

| instance | Gecode nodes / failures / time | `fzn-glasgow` nodes / failures / time |
|---|---|---|
| `area`: 7×2 in 5×5 | 0 / 1 / 0.13 ms (root failure) | 109,043 / 109,042 / 0.52 s |
| 5×2 in 5×5 | 399 / 200 / 0.6 ms | 8,603 / 8,602 / 35 ms |
| 3,2,2,2,1⁴ in 5×5 (enumerate) | 200,875 / 95,830 / 0.61 s | 526,155 / 515,881 / 3.2 s |
| 3²,2⁴,1² in 6×6 | 267,777 / 133,889 / 0.43 s | 1,643,255 / 1,643,254 / 8.7 s |
| 3³,2³,1³ in 7×6 | 4,304,721 / 2,152,361 / 7.5 s | 41,539,667 / 41,539,666 / 239 s |

Gecode's `nooverlap` sees 2.6 to 22 times fewer nodes than the default rule,
and refutes `area` with no search.

**Within GCS, by arm, under the same branching.** `fzn-glasgow` maps
`indomain_min` to the binary `value_order::smallest_in()` (`x = min` or
`x ≠ min`, `fzn_glasgow.cc:1325`). The probe `sqio_in.cc` posts the same model
in C++ with that branching. It reproduces `fzn-glasgow`'s pairwise counts
exactly (109,043, 8,603 and 526,155 recursions) and runs each rule arm under it.
Proofs were off, `GLIBC_TUNABLES` was pinned, and the build was `7e1c4178`
(Release, GCC 15.2) on fataepyc-08, 2026-10-05. The pairwise column ran with
other cells alongside, one per core, on an otherwise quiet machine. The four
rule columns are the best of three serial runs on core 60. **Recursions are
the comparison.** The route A arm is `cumulative_relaxation`,
`relaxation_overload` and `relaxation_time_table_edge_finding`, without
`relaxation_edge_finding`. With `relaxation_edge_finding` also on, the
counts are identical (1, 55, 9,221, 67 and 197).

| instance | pairwise | route B | route A (with route B) | projection, default | projection, all |
|---|---|---|---|---|---|
| `area`: 7×2 in 5×5 | 109,043 / 0.55 s | 55 / 1.1 ms | 1 / 0.16 ms | 1 / 0.18 ms | 1 / 0.19 ms |
| 5×2 in 5×5 | 8,603 / 35 ms | 55 / 0.8 ms | 55 / 1.1 ms | 55 / 0.5 ms | 55 / 0.7 ms |
| 3,2,2,2,1⁴ in 5×5 (enumerate) | 526,155 / 2.8 s | 9,221 / 0.20 s | 9,221 / 0.38 s | 9,221 / 0.12 s | 9,221 / 0.22 s |
| 3²,2⁴,1² in 6×6 | 1,643,255 / 8.6 s | 71 / 2.1 ms | 67 / 1.9 ms | 71 / 0.8 ms | 29 / 0.6 ms |
| 3³,2³,1³ in 7×6 | 41,539,667 / 234 s | 203 / 7.5 ms | 197 / 7.3 ms | 203 / 2.2 ms | 153 / 2.8 ms |

GCS's relaxation arms see far fewer nodes than Gecode, but no frontend can turn
them on. With the multi-way `smallest_first()` instead (`sqio.cc`, 2026-10-04,
under load) the pairwise counts are 97,021, 7,677, 550,504, 1,976,221 and
52,520,046. The relaxation arms are similar in size but not the same trees.
Under `examples/squares`' own `dom_then_deg` search the pairwise rule takes
14,875 recursions on 7×6, not 41.5M (see the proof table below). #1250's
wider pairwise test is the obvious first step to closing the default gap. It
changes these square packings little, since a square rarely covers another's
compulsory part without one of its own.

**On variable sizes** (`examples/shikaku`, its own `dom_then_deg` search,
recursions): `small` 23, `small --autotable` 19, `human` 2,270,
`human --autotable` 312. With #1250's prototype these are 9, 1, 2,793 and 10.
The `human` row grows because the heuristic branches differently once domains
are smaller.

**What these benchmarks do not exercise.**
- Optional rectangles.
- Variable sizes in the relaxation.
- Non-strict mode.
- Anything wide.

Under the static branching, route A beats route B by a few recursions on 6×6
and 7×6 (67 against 71, 197 against 203). The projection with every
`Cumulative` rule on is smaller again (29 and 153). The design note attributes
the projection's 6×6 gain under the example's own search to the knapsack rung
alone; that split was not re-measured here.

### Proof performance

All figures below are at `7e1c4178`, fataepyc-08, 2026-10-04, using
`examples/squares` with its own `dom_then_deg` search and `--prove`. Proofs are
checked by `veripb --force-checked-deletion`; every one verified. The verification
times were taken with 24 VeriPB processes running at once, one per core. The
recursions and sizes match the design note's table exactly.

| instance | pairwise | route B | route A | projection, default | projection, all |
|---|---|---|---|---|---|
| `area` | 101,221 rec / 145.4 MB / 19.9 s | 53 / 12.9 MB / 0.8 s | 1 / 2.26 MB / 0.2 s | 1 / 2.28 MB / 0.2 s | 1 / 2.28 MB / 0.2 s |
| 9×2 in 5×7 | 19,158,497, proofs off (165 s) | 637 / 328.2 MB / 19.4 s | 1 / 4.63 MB / 0.3 s | 1 / 4.65 MB / 0.3 s | 1 / 4.65 MB / 0.3 s |
| 3,2,2,2,1⁴ in 5×5, 4,608 packings | 40,297 / 34.7 MB / 10.1 s | 10,513 / 751.1 MB / 53.7 s | 10,513 / 546.4 MB / 141.5 s | 10,513 / 62.3 MB / 126.3 s | 10,513 / 43.2 MB / 111.4 s |
| 3²,2⁴,1² in 6×6 | 11,313 / 7.62 MB / 1.6 s | 225 / 64.6 MB / 4.2 s | 225 / 37.9 MB / 2.6 s | 265 / 10.4 MB / 1.4 s | 29 / 8.36 MB / 0.6 s |
| 3³,2³,1³ in 7×6 | 14,875 / 10.6 MB / 2.3 s | 29 / 12.5 MB / 0.8 s | 29 / 9.60 MB / 0.7 s | 29 / 5.01 MB / 0.4 s | 29 / 5.98 MB / 0.5 s |

**Size and checking time come apart.** On the enumeration, route B's 751 MB
verifies in 54 s, and route A's 546 MB and the projection's 43 to 62 MB take
111 to 141 s. A proof-size table alone would rank these arms backwards for
checking. **A hypothesis, not tested here:** route B's certificates are
`Temporary` and deleted at once, while route A's and the projection's rows are
cached at `Top`, so their live database keeps growing and every RUP propagates
over more of it.

**Own lines against shared layers.** These counts come from the script
`classify.py` (lines and bytes per class). It counts as the literal layer the
`red` definitions of `ge` and `eq` atoms and their unit pins, and as search
each `rup` after a backtrack comment and each `solx`. Everything else that
derives is this family's own, including `Cumulative`'s certificates under the
projection.

| proof | own | literal layer | search | deletions |
|---|---|---|---|---|
| `area`, pairwise | 118.5 MB (81%) | 0.02 MB | 12.2 MB | 13.1 MB |
| `area`, route B | 12.7 MB (98%) | 0.01 MB | 0.0 | 0.2 MB |
| 6×6, pairwise | 5.35 MB (70%) | 0.02 MB | 1.39 MB | 0.69 MB |
| 6×6, route B | 63.4 MB (98%) | 0.02 MB | 0.01 MB | 1.0 MB |
| enumeration, pairwise | 23.5 MB (68%) | 0.02 MB | 7.35 MB | 2.9 MB |
| enumeration, route B | 735.7 MB (98%) | 0.03 MB | 2.3 MB | 12.1 MB |
| enumeration, projection all | 39.5 MB (91%) | 0.03 MB | 2.3 MB | 1.0 MB |

At these widths (domains of at most six values) the literal layer is
negligible: under 400 lines per proof. The family's own derivations are 68% to
98% of the bytes. This was not measured at wider domains, where the pairwise
rule's own lines stay constant per firing and the layer grows with each new
bound.

**At `AssertionLevel::Inferences`** (`GCS_ASSERTION_LEVEL=inferences`, same
instances, same commit):

| proof | size: `Off` → `Inferences` | `a` lines in total | carrying `disjunctive_2d` | carrying `cumulative` | check time: `Off` → `Inferences` |
|---|---|---|---|---|---|
| `area`, pairwise | 145.4 MB → 70.7 MB | 517,614 | 416,392 (80%) | 0 | 19.9 s → 1.8 s |
| `area`, route B | 12.9 MB → 48.7 KB | 246 | 192 | 0 | 0.8 s → 0.05 s |
| 6×6, pairwise | 7.62 MB → 4.44 MB | 31,094 | 19,780 (64%) | 0 | 1.6 s → 0.16 s |
| 6×6, route B | 64.6 MB → 371 KB | 2,022 | 1,796 | 0 | 4.2 s → 0.06 s |
| 6×6, route A | 37.9 MB → 288 KB | 1,658 | 1,432 | 0 | 2.6 s → 0.06 s |
| 6×6, projection all | 8.36 MB → 20.4 KB | 108 | 8 | 70 | 0.6 s → 0.05 s |
| enumeration, pairwise | 34.7 MB → 22.5 MB | 129,999 | 85,094 (65%) | 0 | 10.1 s → 1.6 s |
| enumeration, route B | 751.1 MB → 10.2 MB | 45,585 | 30,464 | 0 | 53.7 s → 1.2 s |
| enumeration, route A | 546.4 MB → 9.8 MB | 43,565 | 28,444 | 0 | 141.5 s → 1.2 s |
| enumeration, projection all | 43.2 MB → 9.5 MB | 39,921 | 6,078 | 18,722 | 111.4 s → 1.2 s |

All are `s UNDER ASSERTIONS`. The pairwise rule's assertions save least
(35% to 51% of the bytes), since its derivations are a few `pol`s each. The
relaxation's save 78% (the projection's enumeration, whose `Cumulative`
assertions remain) to 99.8%.
Every `disjunctive_2d` assertion has one wire form, so the split by wire form
is the table's two columns.

## Status, gaps, and next steps

### Proof-logging gaps

- **A rejected proof when a size variable is also a position** (#1253). The
  pairwise push and route B both write certificates VeriPB rejects. The answers
  are correct, and the shape is reachable from MiniZinc. This is the one place
  where an inference is made and not certified.
- Otherwise, every inference is justified, no `a` line is emitted at
  `AssertionLevel::Off`, and no rule is weakened when proofs are on. The
  relaxation's membership, windows and floors are settled from the model so that
  proofs-on and proofs-off runs agree.
- **The proof options change what the presolvers do with a projection**
  (#1234). Above `Off`, two of them install nothing, and
  `CumulativeStrengthening` throws wherever it would strengthen something. That
  is not a gap in this constraint's own proof.

### Known limitations

- "VeriPB rejects my `diffn` proof": a size shares a variable with a position
  (#1253).
- "My `diffn` model searches far more than Gecode": the default rule is
  pairwise over compulsory parts only, and narrower than that (#1250). No
  frontend reaches the relaxation.
- "`fzn-glasgow` errors on my `diffn`" with a size that can be negative
  (#1251).
- "Optional rectangles from MiniZinc": not possible, since there is no
  `var opt` `diffn`. Use the API or `.scp`.
- "My 3-D packing is slow": `diffn_k` decomposes (#975).
- "`cumulative_projection` runs out of memory": on a wide time axis it
  allocates the span on every call (#833).
- "My proof is huge with `relaxation_overload`": the certificate is linear in
  the window's span. Set `relaxation_max_span`, which also changes the
  inferences (#1098).
- An undecided optional rectangle blocks nothing and is pushed nowhere. There is
  no conditional-bounds store.

### Next steps

0. **Fix the aliased-size proofs** (#1253). Capture each size's lower-bound
   literal with the position literals before the push, and count sizes as uses
   in route B's admission test. Cheap, and it is the only rejected proof this
   audit found.
1. **Widen the pairwise overlap test to the forbidden-region condition**
   (#1250). It is two lines per loop, plus a non-strict `size ≥ 1` gate for
   the escape pins, and no proof change. Measured:
   - Across eight random shapes, the roots with an unsupported bound fall by
     10% to 57%.
   - The fall is largest on constant sizes, strict or non-strict: 114 → 54 for
     three strict rectangles, 14 → 6 for two non-strict ones. It is smaller with
     variable sizes: 41 → 30 and 146 → 103 strict, 10 → 9 and 61 → 51
     non-strict.
   - Shikaku `human --autotable` goes from 312 recursions to 10.
   - Every test and proof passes.

   Cheap, and it buys the default rule.
2. **Make the projection wake on presences** (#1252). One loop. It buys a
   little propagation with optional rectangles.
3. **Settle the assertion-level behaviour with `cumulative.md`**
   (#1234). The same gate decides both, and
   whichever fix lands there should cover `disjunctive_2d.cc:706`.
4. **Add a subhint per rule.** Thirteen rules under one wire form make every
   rule `search`. A `(subhint …)` field would make them `hinted`. Cheap.
5. **Give the large-domain audit a row with `cumulative_projection`** (and with
   variable sizes and presences). It would pin the horizon trip as
   `KnownTrip`. Cheap.
6. **Let a frontend turn the relaxation on.** Under the MiniZinc model's static
   branching, on packings it is the difference between minutes and
   milliseconds, and it is certified. This is a decision
   for Ciaran (`fzn-glasgow` flags; #901's question one family over).
7. **Use `bounds_reason` for the pairwise rules.** The certificate reads only
   bounds, and the generic reason carries every gap. Cheap; it makes the
   reasons smaller on holey domains, and needs a proof diff to confirm nothing
   else read the gaps.
8. **Decide negative sizes in MiniZinc** (#1251): post `size ≥ 0` as Gecode
   does, decompose, or document.
9. **A span-flat certificate for route A** remains open (design note, open
   follow-ups). The cap is the only answer today.
10. **A cake encoder for the optional forms**, which waits for the next batch of
    requests to cake upstream, as `cumulative_optional` does.
11. **Fix the stale comments**: "six pols" per push, in the code and the note,
    is four.

## Prior art

- **The propagation.**
  - Pairwise reasoning on compulsory parts is the classical starting point for
    non-overlapping rectangles. Beldiceanu and Carlsson's sweep (CP 2001)
    works over forbidden regions, and the `geost` kernel (Beldiceanu,
    Carlsson and others, CP 2007) takes it to `k` dimensions.
  - Gecode's `nooverlap` is the comparison point above.
  - `cumulative` (Aggoun and Beldiceanu, 1993) and `diffn` (Beldiceanu and
    Contejean, 1994) both come from CHIP, and posting a `cumulative` per axis
    as a redundant constraint is the usual strengthening of `diffn`. Route B and
    route A run that projection inside the constraint rather than as posted
    redundant constraints.
- **The certification.** As far as this audit knows, no earlier work certifies
  `diffn` reasoning in a proof system.
  - The pairwise certificate is ours.
  - The relaxation's certificates rest on the comparator-network construction
    of #730. That is ours, in this tree, and is as yet unpublished.
  - The derived-row approach is novel in the sense that matters for the paper:
    no capacity row is in the model, and the cumulative relaxation is
    **derived per time point inside the proof** from the definition of
    non-overlap.
- **k dimensions.** #975 records the scope position. A slice point on every
  axis but one leaves the last axis's separation, so the argument carries (the
  probe verifies 3-D and 4-D). But it costs one slice per tuple of points on the
  other `k − 1` axes, `O(horizon^{k−1})`. That is #780's explosion one
  dimension up, so k-D is not implemented.

## Further reading

- [`disjunctive-proof-logging.md`](../disjunctive-proof-logging.md), section
  "2D non-overlap". It covers the encoding, the pairwise justifications,
  optional rectangles, route B's four lessons (guarded separations, tight
  bounds, the escape pin, model-decided membership), route A's parking rows
  and the quadratic constants (#1082), the time-axis gate (#1083), the span
  cap (#1098), edge-finding's closed-form threshold, TTEF's never-load-bearing
  pins, the variable-size floors on both axes, the projection (#973) and the
  donor. Everything above is audited against it. Its tables were re-measured
  here and match.
- [`cumulative-proof-logging.md`](../cumulative-proof-logging.md): the two
  `CumulativeInputs` fields the projection added, and what `Cumulative`'s
  certificates cite.
- [`cumulative.md`](cumulative.md) for the projection's rules, and
  [`disjunctive.md`](disjunctive.md) for `ComparatorNetwork` and the 1-D form.
- #972 (route B), #984 (route A, optional rectangles, variable sizes), #974
  (optional rectangles), #973 and #1136 (projection donors), #975 (k-D),
  #980 (the k-D probe), #1098, #1082, #1083.
