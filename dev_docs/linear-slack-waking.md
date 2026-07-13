# Slack-based waking for linear inequalities

`ReifiedLinearInequality` normally wakes on every bound change of every term
(`on_bounds` triggers) and then sweeps. For a long constraint most of those
wakes cannot propagate anything: the constraint is quiet until the slack
`value - min_possible` drops below the largest per-term potential. Slack-based
waking uses the refined-watch API to wake only when a *covering* subset of the
terms moves — the pseudo-Boolean "watch enough to cover the slack" scheme.

## The scheme

For `Sum(coeff_i x_i) <= value`, after the forward sweep reaches its fixpoint:

- each term's **potential** is `|coeff_i| * (ub_i - lb_i)` — the most it can still
  raise the lower sum (positive coefficients contribute via their lower bound,
  negative via their upper);
- at the fixpoint every potential is `<= slack`, so with
  `margin = slack - max_potential (>= 0)` we watch the largest potentials down
  until the unwatched ones sum to within the margin. Then no combination of
  unwatched moves can drop the slack below `max_potential`, so none can enable a
  propagation, and none can violate the constraint — only a *watched* term's
  min-contribution bound moving can, and that is exactly the literal watched
  (`x_i >= lb_i + 1` for a positive coefficient, `x_i <= ub_i - 1` for a negative
  one). See `rearm_linear_slack_watches` in `constraints/linear/propagate.cc`.

The sweep only ever *tightens* the opposite bound to the one it watches (a
positive-coefficient term is written on its upper bound, watched on its lower),
so a propagator never fires its own watch. Only the wake condition changes: the
inferences, search tree, and proof are exactly the coarse propagator's, woken
only when a covering term moves. `linear_test`'s internal veripb check passes on
the slack path (the `linear_constraint_*_slack` ctest variants force it on).

## Integration

Only the direction that is *decided at install* — an unconditional inequality,
or a half-reified one already fixed — takes the slack path; it bypasses the
reified dispatcher and installs the sweep directly with `scope_only` triggers
(so degree/adjacency still see the variables — see `refined-triggers.md` and
issue #506) plus dynamically-armed refined watches (#505's `clear_watches` +
`watch`). The genuinely-undecided reified case, and equality, keep the coarse
path.

## When it is worth it — measured

`examples/linear_slack_bench` posts long, loose `Sum <= budget` constraints with
mismatched coefficients and enumerates to a solution cap; the tree is identical
whichever path runs, so it isolates per-node propagator cost. Toggle with
`GCS_LINEAR_INCREMENTAL_THRESHOLD` / `GCS_LINEAR_SLACK_WATCH_THRESHOLD`.

Representative run (`--vars 400 --budget-num 85 --cap 5000`), incremental vs slack:

| sumlen | incremental | slack   | props (inc → slack) |
|-------:|------------:|--------:|--------------------:|
|     60 |     ~0.02 s |  ~0.02 s | ~100k → ~60k        |
|    100 |     0.033 s | 0.031 s | 133k → 10k          |
|    200 |     0.061 s | 0.022 s | 344k → **437**      |
|    300 |     0.104 s | 0.027 s | 530k → 900          |

So the wall-clock win is real but **confined to very long, genuinely loose
inequalities** (roughly `sumlen >= ~128`), where it reaches 2.8–3.9x. The catch,
and why this is not on by default:

- **Wake count is not the bottleneck the incremental propagator has.** The
  incremental sweep folds instantiated terms, so its per-wake cost is already
  tiny; cutting the wake *count* by 6–20x buys nothing when each saved wake was
  nearly free. Slack only wins once the constraint is long enough that even the
  folded sweep, run once per bound event, costs more than slack's rare wakes.
- **The per-wake re-arm is `O(n log n)`** (sort the potentials, clear, re-arm the
  cover). On a constraint that turns *tight* during search — waking often — this
  loses badly (measured ~5x slower than incremental at `sumlen 200`, budget 55%).
- The install-time covering-set-size heuristic (`linear_slack_cover_size`)
  estimates from the *initial* bounds, which does not predict a constraint that
  is loose at the root but tight in parts of the tree. A generous cover cap (50%)
  admits such constraints and loses; a tight cap (**15%**, the default) admits
  only the constraints that stay loose throughout and win.

## Defaults and how to enable

- `GCS_LINEAR_SLACK_WATCH_THRESHOLD` — minimum term count; default
  `SIZE_MAX`, i.e. **off**. Recommended opt-in value: `128`.
- `GCS_LINEAR_SLACK_WATCH_COVER_PERCENT` — maximum covering-set size as a
  percentage of the term count; default `15`.

It ships off because the win is narrow (constraints with 128+ terms are rare) and
a mis-engagement loses on a frequently-waking constraint.

## Incremental covering-set maintenance — explored, does not help

The obvious next step is to stop rebuilding the cover from scratch each wake.
Down a branch the slack only falls and potentials only shrink, so the cover only
ever needs to *grow*: re-arm the watches that fired and top the cover up along a
term order fixed at install (by initial potential), reading the watched set back
from the (backtrack-consistent) watch index — no sort, no clear, and nothing
extra to trail. This was prototyped and measured (identical trees, proofs still
verify). **It does not close the cliff, and makes the tight case worse:**

| case (sumlen 200, vars 400) | rebuild | incremental | inc. propagator |
|---|---:|---:|---:|
| loose (budget 85%) | 0.023 s / 437 wakes | 0.023 s / 437 | 0.061 s |
| tight (budget 55%) | 0.46 s / 97k wakes | **1.10 s / 309k** | 0.062 s |

Two things this taught us:

- **The cliff is driven by wake *count*, not the sort.** A tight constraint
  genuinely needs a large cover, so it wakes often, and each wake pays the refined
  watch machinery plus an `O(n)` sweep — already more than the incremental
  propagator's cheap folded coarse wake. A refined-watch wakeup is itself about
  **8x** the cost of a coarse-trigger wakeup (≈38 ns vs ≈4.5 ns for equivalent
  both-bounds coverage, measured by `examples/wake_cost`: identical tree, identical
  wake count, trivial propagator body) — the extra going on `test_literal`
  evaluation, the payload inbox, and the backtrackable watch-index edits that the
  static coarse triggers do not need. No cover bookkeeping changes that;
  slack-waking is fundamentally a wake-*elimination* technique that only wins when
  wakes are rare (loose constraints), where far fewer, dearer wakes still beat many
  cheap ones.
- **A sort-free cover is a non-minimal cover.** The rebuild's per-wake sort by
  *current* potential buys the *minimal* cover; a fixed initial-potential order
  watches large-initial-but-now-small terms and misses small-initial-but-still-
  large ones, so it covers with *more* watches → 3x the wakes here. Keeping the
  cover minimal needs current-potential selection, i.e. the sort — there is no
  sort-free minimal cover, and the refined-watch API offers only add and
  clear-all, no remove-one, so even "un-watch the stale ones" reduces to a rebuild.

So the rebuild (current implementation) is the better simple version, and the
right mitigation for the cliff is the engagement heuristic *not* turning slack on
for tight constraints — which the 15% cover cap already does. A folded per-wake
sweep (`propagate_linear_incremental` instead of the stateless one) would cut the
`O(n)` sweep cost, but only helps in *deep* search (where the active set is small)
and does nothing for the refined-watch per-wake overhead, so it is unlikely to
move slack-waking into the tight regime; it is not worth the two-backtrackable-
structures integration on this evidence. Tracked as the open direction for #507,
but de-prioritised by these measurements.
