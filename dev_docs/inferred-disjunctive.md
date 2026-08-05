# Inferring `Disjunctive` constraints across resources

Two tasks conflict when *some* resource cannot hold both at once. A set of tasks
conflicting pairwise can have at most one of them running at any time — and when
different pairs of that set conflict on *different* resources, that is an
inference no single posted `Cumulative` can make.

`InferredDisjunctive`
([`gcs/presolvers/inferred_disjunctive.hh`](../gcs/presolvers/inferred_disjunctive.hh))
finds those sets and posts each as a capacity-one derived `Cumulative`. It is the
first stage of Sidorov (CP 2026), restricted to capacity one and unit
coefficients — which is what keeps every certificate polynomial, and where his
own data says most of the value is. The general lifted case, with non-unit
coefficients, is [`InferredCumulative`](inferred-cumulative.md).

## What it does

Tasks are identified by **start variable**, so the same task on two resources is
one node of the conflict graph. Each candidate pair is grown into a maximal
clique taking longest-duration first (the unit-coefficient reading of Sidorov's
lifting order), cliques are ranked by total duration, and anything subsumed by an
accepted clique or smaller than three members is dropped.

Three is the floor because a two-task "clique" is just a conflicting pair, which
the resource witnessing it already rules out — posting one adds a propagator that
cannot infer anything new.

Both budgets (`N_cover`, `N_out` in the paper) count what they drop.
A budget that quietly swallowed every candidate is indistinguishable, from the
outside, from a conflict graph with nothing in it.

## Time-table neutrality, again

As with [capacity strengthening](cumulative-strengthening.md), the inference
cannot change a time-table verdict: a conflicting pair is already kept apart by
whichever resource witnesses it, so the inferred constraint's profile reasoning
is redundant. It therefore ships with **time-tabling off**, and the test asserts
node-for-node equality with it turned back on.

What is new is the *energy* argument over the whole clique. Three pairwise
incompatible tasks of length two need six units of a five-slot window, and no
single resource's capacity row says that. The fixture family refutes exactly
there.

## The certificate

Per time point, over the clique members whose window covers it:

1. **The pairwise at-most-one**, out of its witnessing resource's capacity row:
   weaken every other task away, saturate, divide. This is
   [`build_am1_from_row`](../gcs/innards/proofs/am1_from_row.hh) over the two of
   them, shared with the `Cumulative` strengthening presolver, which wants the
   same program over a single donor. The divisor comes out as the margin
   `c_u + c_v - C` on its own, and no side condition on `c_u, c_v <= C` is
   needed — saturation caps both coefficients at that margin and the division
   rounds them back to one. A pair summing to *exactly* the capacity does not
   overshoot, which the utility refuses outright rather than deriving: nothing
   later in the proof can catch a pair that does not conflict.

   Two members is not a special case of that routine but its smallest one, and
   where several of a clique's members share a witnessing row, recovering their
   whole sub-clique in one step instead of pair by pair is the proof-size fix
   [#666](https://github.com/ciaranm/glasgow-constraint-solver/issues/666) is
   about.
2. **The bridge**, where the witness is not where a task's flags live — which is
   the normal case, since a clique's pairs are witnessed by different resources.
   `recover_conjunction_flag_bridge` carries it across, cached per
   `(task, resource)` rather than per pair. The carry *continues the same `pol`*
   as step 1 rather than starting another: the bridges go on the stack, each
   cancelling its task's term, and one saturation clears up after all of it.
3. **The merge**, `recover_am1_from_pairs`, whose pinned output *is* the
   unit-height capacity-one row the derived constraint needs. No separate step
   is required to turn one into the other.

Nothing reaches the OPB; the byte-diff test enforces it.

## Proof size

Measured on the three-task family over five time points: **251 lines, 11 KB, 139
`pol` steps** — about 28 `pol` per time point for a three-clique.

The shape is `O(k²)` pair derivations plus `O(k)` bridges plus `O(k)` merge steps,
**per time point**, so the whole thing is multiplied by the horizon. At eight
members and a horizon of a thousand that is order 10⁵ lines per clique, and every
one of them is emitted at `ProofLevel::Top`, where it never dies and taxes every
later unhinted RUP — the `table_layout15` pathology.

Only the pinned per-time row needs to outlive the recipe. Deriving the
intermediates at `Temporary` and forgetting them after each row, or inlining a
whole time point into a single `pol` so they never enter the checker's database
at all, is the fix. Neither is done yet, and it is the first thing to do before
this is pointed at a real instance.

## Testing it

The fixture family is built so that no single donor could make the inference: k
tasks, k resources, pair `(i, j)` conflicting only on resource `(i + j) mod k`,
every resource posted over all k starts with zero demand for non-members. A root
refutation there cannot be one of the donors doing the work, and
`bridges_derived` being non-zero says the certificate genuinely spanned
resources.

- **The differential**: three tasks of length two into five time points — root
  refutation with the presolver, search without, proof verified.
- **The sharp twin**: one more unit of horizon, satisfiable, all six solutions
  matching brute force. An inferred constraint has to be harmless where it is not
  decisive.
- **Solution preservation** at three shapes, against brute force.
- **Neutrality**, as node-for-node equality under time-tabling alone.
- **Budgets**, on a two-disjoint-edges fixture where the drops are real rather
  than an artefact of there being no candidates.
- **The capacity bound itself**, asserted as six on the differential fixture —
  which is also *why* it refutes, three length-two tasks needing six units of a
  five-unit horizon — and as zero where nothing was posted, so a stale bound
  cannot masquerade as a derived one.
- **End to end from a file**, as the `rcpsp_dzn_inferred` example test:
  `examples/rcpsp/sample.dzn` is built so each conflicting pair is witnessed by a
  different resource, and its proof is VeriPB-checked like every other example.
- **Mutations**, on a fixture carrying a *camouflage* task — a fourth task on a
  capacity-two resource where every pairwise demand sums to exactly two, so it is
  compatible with everything by exactly one unit. Honestly it stays out of the
  clique; the mutations force the issue:

  | mutation | what it corrupts |
  |---|---|
  | `ClaimRhsZero` | claims no member may run at all |
  | `BridgeWrongTask` | bridges a task onto the *other* task's flags, so the at-most-one is about a task nothing cornered |
  | `IncludeNonConflicting` | grows the clique with the camouflage task, inventing the conflict record — exactly where an off-by-one in the conflict test lands |

  VeriPB rejects each. All three corrupt the *conclusion* rather than the route,
  which is what a conflict-shaped derivation requires: the route is where it
  forgives everything.

## The Pack / Pack-d cross-check

Sidorov's §5.1 says "no less than twelve of the instances in Pack and Pack-d
collections can be closed immediately by using one of the lifted cumulative
constraints, with the capacities varying between one and three". Twenty of those
lifted constraints have capacity one, which is what this presolver infers, and
for those his capacity bound `L = sum_i d_i pi_i / pi_0` collapses to the
clique's total duration — `InferredDisjunctiveStats::largest_capacity_bound`.

The instances are the MiniZinc benchmarks' `rcpsp/data_pack` and
`rcpsp/data_pack_d`, read with `--dzn`. On all twenty capacity-one targets this
presolver reports **exactly the bound the paper does**, under his own budgets
(`N_cover = 100`, `N_out = 5`, the defaults here):

| collection | instances | `L` reproduced |
|---|---|---|
| Pack | 4, 5, 8, 9, 11, 13, 16, 23, 28, 29 | 10 / 10 |
| Pack-d | 8, 9, 12, 15, 16, 17, 18, 20, 24, 43 | 10 / 10 |

Eleven of the twenty have `L` equal to the best known makespan, so the bound
closes the instance with no search at all. Give the presolver the makespan
variable, with `with_makespan`, and that bound is *derived* rather than
reported: see [certified makespan bounds](certified-makespan-bounds.md), which
carries the argument and the sweep over both collections.

Two things about the comparison are worth writing down, because both are easy to
get wrong and neither is visible from the paper:

- His logs record the bound **unrounded** — the rational `sum_i d_i w_i / r` to
  three decimal places, not its ceiling. Capacity-one rows are integral either
  way, so a naive comparison looks right and then fails on every non-unit
  capacity. His own reporting script compares the unrounded value, which is why
  the paper's counts are conservative: twenty Pack/Pack-d instances close on that
  comparison and thirty-six close with the ceiling.
- The standard `rcpsp.mzn` posts redundant pairwise non-overlap constraints for
  conflicting pairs. His preprocessor does not, and neither does `--dzn`: they
  are a modelling choice of that file rather than part of the instance, and
  posting them would hand the presolver conflicts it is supposed to find.

## Not done

- The general lifted case, with non-unit coefficients, is
  [`InferredCumulative`](inferred-cumulative.md), and it spans resources too ---
  by a weight per resource in its knapsack programme rather than by merging
  at-most-ones, which is scale-free and so stops working as soon as a
  coefficient is not one.
- Budget-robustness sweeps on larger instances.
- The proof-size work above.

<!-- vim: set tw=72 spell spelllang=en : -->
