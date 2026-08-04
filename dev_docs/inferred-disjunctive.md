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
own data says most of the value is. The general lifted case is issue #549.

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
   weaken every other task away, saturate, divide by the margin
   `c_u + c_v - C`. No side condition on `c_u, c_v <= C` is needed — saturation
   caps both coefficients at the margin and the division rounds them back to one.
   A pair summing to *exactly* the capacity has margin zero and correctly yields
   nothing.
2. **The bridge**, where the witness is not where a task's flags live — which is
   the normal case, since a clique's pairs are witnessed by different resources.
   `derive_conjunction_flag_bridge` carries it across, cached per
   `(task, resource)` rather than per pair. The carry *continues the same `pol`*
   as step 1 rather than starting another: the bridges go on the stack, each
   cancelling its task's term, and one saturation clears up after all of it.
3. **The merge**, `derive_clique_from_amos`, whose pinned output *is* the
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

## Not done

- Sidorov's Pack/Pack_d cross-check (his §5.1, instance lists in the zenodo
  logs), which would say whether the cliques found here match the ones his
  capacity-bound metric reports.
- Budget-robustness sweeps on larger instances.
- The proof-size work above.

<!-- vim: set tw=72 spell spelllang=en : -->
