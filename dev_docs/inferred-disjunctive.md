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

That is a **divergence from Sidorov's pipeline, and a deliberate one**: his
binary covers are exactly two-task cliques, and he keeps them. Where a
conflicting pair has no common neighbour, its `L = d_u + d_v` can top the
ranking and be the constraint his `L` is reported from, and ours would have
nothing there. It costs nothing on the twenty cross-check targets, whose cliques
run to ten members and more, and `with_minimum_clique_size(2)` turns it off — but
whether two is worth posting *in general* is a measurement question, and the
measurement is the artefact rerun that has not happened. That is issue #707,
rather than something guessed at here.

Cliques are also dropped when one posted capacity-one resource already contains
every member: that constraint is the resource's own, and reporting its bound as
`largest_capacity_bound` would report a number the model already had. It is the
unit-coefficient case of the `pi <= d` dominance test `InferredCumulative` runs,
and of Sidorov's L4. Only *exact* domination drops a clique — cliques here are
maximal, so one reaching past the resource keeps a member the resource has no
term for.

Both budgets (`N_cover`, `N_out` in the paper) count what they drop, separately:
they bound different costs in different units, and one counter for both is one
no accounting identity can be written against. A budget that quietly swallowed
every candidate is indistinguishable, from the outside, from a conflict graph
with nothing in it.

A task demanding **more than a resource has** is kept here, where
`CumulativeStrengthening` declines the donor over it and `InferredCumulative`
gives it no column on that row. Three answers to one question, and this is the
lax one: such a task can never run at all, so every clique it pads is padded
with a duration nothing will ever occupy, and `largest_capacity_bound` reads
higher than it should. It only arises on a donor that cannot be satisfied — its
own propagator says so at the root — so what is really going on is that the
whole model is infeasible, and the number is being read off a run that has
already lost. The discovery-side `c_j <= C` filter the other two have was never
implemented here.

Candidate pairs are ordered by their own `least_length` sum before the candidate
budget takes a prefix, so what the budget keeps is the best pairs rather than the
first ones by variable creation order. His `C2` filter retains the top ones by
bound too. It matters more than it looks: forty of the hundred and ten Pack
instances have more than a hundred conflicting pairs, so the cross-check below
goes through that cap.

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
   whole sub-clique in one step instead of pair by pair would make the file
   smaller — see Proof size, where the measurement and the reason it is not done
   both are.
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
members and a horizon of a thousand that is order 10⁵ lines per clique.

**None of them stays in the database.** Only the pinned per-time row is ever cited
again, so the bridges and the pairwise at-most-ones go one proof level deeper than
the caller's, the merge induction one deeper again, and both are forgotten on the
way out — the same dance `recover_am1` and `derive_lifted_cover_cut` do, and for
the same reason. Emitting them at `Top` instead is what
[#666](https://github.com/ciaranm/glasgow-constraint-solver/issues/666) was
about: the `table_layout15` pathology, where a bloated live database cost twelve
times at the root rather than at deletion time.

Measured on `k`-cliques in which every pair has its own witnessing resource, so
the bridges are at their worst:

| k | time points | `pol` emitted | live before | live after |
|--:|------------:|--------------:|------------:|-----------:|
| 3 | 6 | 78 | 84 | 6 |
| 4 | 8 | 256 | 264 | 8 |
| 5 | 10 | 580 | 590 | 10 |
| 6 | 12 | 1092 | 1104 | 12 |

One line per time point survives rather than one per pair per time point, and it
costs two `del` lines per time point — about 0.3% more proof.

The **file** is another matter, and it is unchanged by this. On a real Pack
clique (`pack008`, ten members over three resources) a time point emits 72 `pol`
of bridges and pairwise at-most-ones and 14 of merge induction. Recovering a
whole sub-clique in one step where members share a witnessing row would cut the
at-most-ones by about a factor of two on the published Pack targets — 1897
pairwise lines across the twenty of them become 881 — but it needs an induction
over sub-clique premises rather than pairwise ones, which is a new derivation
rather than a rearrangement of this one. Since the cost this file was paying was
the database and not the bytes, it is not done.

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

- Two-member cliques, as above: allowed by the knob, off by default, and the
  default wants measuring rather than arguing about (#707).
- The general lifted case, with non-unit coefficients, is
  [`InferredCumulative`](inferred-cumulative.md), and it spans resources too ---
  by a weight per resource in its knapsack programme rather than by merging
  at-most-ones, which is scale-free and so stops working as soon as a
  coefficient is not one.
- Budget-robustness sweeps on larger instances.
- The proof-size work above.

<!-- vim: set tw=72 spell spelllang=en : -->
