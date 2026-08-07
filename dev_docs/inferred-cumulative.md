# Inferring `Cumulative` constraints by lifting cover inequalities

A resource of capacity five cannot hold three tasks of demand two, because six
does not fit into five. That much its own capacity row says. What the row does
*not* say is what happens when a fourth task, of demand five, is added: it fills
the resource on its own, so it excludes any two of the others at once — and the
inequality recording that,

```
    2a + b + c + d ≤ 2
```

holds at every occupancy point the row allows and at no rational relaxation of
it. It is a *lifted cover inequality*, and deriving it takes an integrality
argument the row alone does not contain.

`InferredCumulative`
([`gcs/presolvers/inferred_cumulative.hh`](../gcs/presolvers/inferred_cumulative.hh))
finds such inequalities and posts each as a derived `Cumulative` whose heights
are the coefficients and whose capacity is the right-hand side. It is the second
stage of Sidorov (CP 2026); the first, capacity one and unit coefficients, is
[`InferredDisjunctive`](inferred-disjunctive.md).

## What the cut is worth

Energy. The tasks in a cut need `Σ_i d_i π_i` units of a resource supplying `π₀`
per time step, so no schedule containing them can be shorter than their ratio —
Sidorov's `L`, reported as `InferredCumulativeStats::largest_capacity_bound`, and
the only output of this presolver that means anything without running a search.

For the example above, with the big task of length three and the small ones of
length five, that is `21 / 2 = 10.5` against the donor row's own `45 / 5 = 9`. A
horizon of ten satisfies the resource and not the cut, which is exactly the
fixture the test refutes at the root.

Give the presolver the makespan variable, with `with_makespan`, and it derives
that ratio rather than only reporting it: see
[certified makespan bounds](certified-makespan-bounds.md), which is where the
argument, its mutations and the RCPSP artefact live.

The ratio is also the *only* thing a cut can buy, which is why it is what covers
and constraints are both ranked by. Note that it is not used as a filter: the
published procedure discards a constraint only when a model row dominates it
term by term, and adding a ratio test of our own would mean posting a different
set of constraints from the paper's.

## Time-table neutrality, again

As with [capacity strengthening](cumulative-strengthening.md) and the
[capacity-one stage](inferred-disjunctive.md), the inference cannot change a
time-table verdict — and here the argument is a one-liner. A cut is *valid*:
every 0/1 point the rows it is lifted from allow satisfies it. So no set of tasks
that fits under those resources at one time point fails under the cut at that
time point,
and time-tabling, which only ever reasons about one time point, can reach nothing
new. It therefore ships with **time-tabling off**, and the test asserts
node-for-node equality with it turned back on.

What is new is the *window* argument, where the two constraints supply and
consume at different rates and the ratio is what decides.

## Finding the cut: Sidorov's Algorithms 1 and 2, unchanged

The constraints are the published procedure's, not ones chosen for being easy
to prove. That is the whole point: a reproduction whose inferences differed from
the paper's could not be compared against its published bounds, however good the
inferences were.

**Algorithm 1, cover enumeration.** Every pair of tasks whose demands overshoot
the capacity is a cover. For each pair that does *not*, the pair plus the
longest-duration task big enough to push it over is one too. Those are ranked by
the capacity bound of their own cover inequality, `Σᵢ dᵢ / (|C| − 1)`, and the
best `N_cover` kept. Then the "long covers": for each distinct demand `v`, the
smallest `k` with `k·v > C`, taking the `k` longest and the `k` shortest tasks of
that demand — these are added *after* the budget, so the budget caps the short
families only.

**Algorithm 2, lifting.** Start from `Σ_C xᵢ ≤ |C| − 1`. Take the remaining
tasks longest duration first, and give each the largest coefficient that keeps
the inequality valid: `π₀ − v*`, where `v*` is the most the current left-hand
side can weigh once that task is forced to run. The right-hand side never moves,
which is what makes the ratio climb. A cover already inside the support of
something lifted earlier is skipped, since lifting it again would re-derive the
same constraint (the paper's Example 12). Constraints a model row already
dominates are discarded, and the best `N_out` by capacity bound are kept.

Budgets are the paper's: `N_cover`, `N_out`, and `N_calls` against the lifting
subproblems, which are the bottleneck. The defaults here are 100, 5 and 2·10⁴,
with the capacity cap effectively off — but those are not one configuration of
his. `N_cover = 100` and `N_out = 5` are the main experiments'
(`gourd/scheduling.toml`), which run *unbudgeted* on calls; `N_calls = 2·10⁴` is
Appendix C's termination variant. So our default is the main configuration's
cover and output budgets under Appendix C's call budget, which is a combination
his experiments did not run.

That matters for one thing in particular, below.

### The early stop we do not have

`lifting.py` abandons a cover's remaining lifting calls when its *optimistic*
elastic lower bound — what it would come to if every remaining task lifted in at
coefficient one — cannot beat the worst bound already in a full pool. We have no
counterpart, and which direction that costs depends on the budget:

- **Unbudgeted on calls**, which is his main configuration, it makes us lift
  covers he abandons. Those covers can only produce a constraint at least as
  good as what he kept, so this is a second unattributed reason our `L`
  sometimes *beats* his, beside the Algorithm 1 representative bug the notes
  above do attribute.
- **Under a call budget**, which is what our default has, it makes us spend
  budget on hopeless covers and so possibly end *weaker* than he would.

Implementing it verbatim would be wrong: the estimate is an upper bound only
while the unlifted coefficients stay at most one, which holds at `π₀ = 1` and
not in general — `lhs[next] = rhs - v*` can reach `rhs`. So a correctly gated
version is issue #703 rather than a line to copy, and the paper is silent on the
rule, which is why nothing here has resolved the mismatch in either direction.

### Zero-demand cover members

Definition 6 and `collect_row_cover_sets` both admit a cover member demanding
nothing of the row the cover is built from, and so do we. In his representation
that is a zero entry of a dense `A`; in ours it is a task with no term in that
donor's row, which is the same statement about the load. Such a member's own
`z` cannot be zero-demand either way, since it has to exceed the room left,
which is never negative.

### Every resource at once

**The lifting subproblem is Equation 4's**, constrained by every posted
resource's row rather than by the donor's alone. That is what makes the lifting
cross-resource, and it matters because more constraints on the subproblem mean a
*smaller* answer, and so a *larger* coefficient: the task being lifted excludes
more, and the inequality says more.

A cover still belongs to one resource --- Algorithm 1 enumerates them per row,
and a set that fits under every resource is nobody's cover --- but the cut lifted
from it need not be a consequence of that row, or of any single row. The
[two-resource fixture](../gcs/presolvers/inferred_cumulative/inferred_cumulative_test.cc)
is the smallest case: the cover belongs to the second resource, the coefficient
comes from the first, and neither row on its own implies the result.

So the presolver runs **once over the whole problem** rather than once per
posted constraint, which is what the reference implementation's single demand
matrix does, and the budgets follow: the cover budget applies to each resource's
short families and then again across all of them, and the subproblem budget, the
visited-cover rule and the output limit are one each rather than one per
resource.

**Two places where the paper and its implementation disagree**, both since
resolved by Konstantin Sidorov by email (2026-08-05), and both in the same
direction: *longest first*.

- Algorithm 2 step L3 says to lift `arg min dᵢ`, shortest duration first, while
  the implementation sorts by duration *descending*. **The paper has the typo**;
  the intent is the longest unlifted task. Lifting assigns coefficients greedily,
  so bringing in the tasks with the biggest effect on the bound first keeps them
  out of the subproblem's objective while it is still small — a later task meets
  a larger `v*` and so gets a smaller coefficient. That the order matters at all
  is not an artefact of doing several resources: **lifting is sequence-dependent
  even over a single row** (Zemel 1978). Which order is best is a heuristic
  question, and depends on what will consume the constraint downstream.
- Algorithm 1 picks "the longest task among the ones satisfying …", and the code
  compares a duration against an array *index* when doing so. **The code has the
  bug**; the intended line reads `durations[ix] > durations[inv_A_longest[a]]`,
  which is what happens here.

That second one is not a formality, and it matters for how the comparisons in
this repository should be read. **The published results came from the shipped
line**, and over the Pack and Pack-d instances the two readings pick a different
representative on 306 of 314 resource rows. The ternary cover family that comes
out differs on 164 of those rows and on 103 of the 110 instances.

The difference runs one way. The shipped line's pick is **never longer** than the
intended one — shorter on 542 of the 922 (demand, row) pairs and equal on the
rest — so the corrected reading's best ternary cover is never worse, and is
better on 61 rows. A per-instance comparison against the paper's numbers is
therefore not a comparison over the same covers, and where this presolver's `L`
beats the published one that is a likely cause. It is also the one place where
reproducing the method as *described* means out-performing the artefact as
*shipped*, which is the opposite of the usual risk and worth saying out loud.

## The certified fraction, which is the number this exists to produce

Nothing is posted without a derivation. A constraint the published procedure
infers and this cannot derive would be **dropped and counted** as
`cuts_uncertifiable` — not weakened into something derivable, because a weakened
constraint is a different constraint and would quietly break the comparison the
exercise is for.

That number is **zero**, and it is zero by construction rather than by luck: the
certificate replays the same knapsack computation the inference already did, so
every constraint the procedure produces is one the proof reaches. The test's
twenty-five-instance verified sweep asserts it.

It was not always. The first version of this file went looking for a short
cutting-planes derivation of each constraint's *conclusion* — three shapes of
`pol`, an in-tree model of VeriPB's normalised-form arithmetic to predict where
they would land, and an `ia` pin to catch that model drifting — and refused about
one valid constraint in twenty-five. Every way of widening that search traded a
smaller tail for more of VeriPB's arithmetic reimplemented here, and none of them
emptied the tail.

## The certificate

A lifted cover cut is true because a knapsack optimum says so:
`Σ πᵢ aᵢ ≤ π₀` holds at every 0/1 point the rows *jointly* allow exactly when
`max { Σ πᵢ xᵢ : Σ c_{r,i} xᵢ ≤ C_r for every r }` is at most `π₀`. So rather
than deriving that conclusion, the proof derives the *computation*, in the
states-and-transitions shape of Demirović et al. (CP 2024) — and in its
**one-sided** form, the one their standalone knapsack solver uses, where a state
says "at least this much weight, at most this much profit" rather than "exactly
this much of each".

The same programme answers the lifting subproblem, which is not an economy but
the point: the inference and the certificate ask the same question of the same
rows, so a cut the procedure produces cannot be one the proof fails to reach.

`validate_lifted_cover_cut` builds the programme and answers the only question
worth asking of a candidate cut; `derive_lifted_cover_cut` emits it. Layer `i`
holds the (weights, profit) tuples the first `i` members can reach, with one
weight per resource. A successor either leaves the next member out, or takes it
and pays its demand on every resource — and **a successor that would overrun some
capacity is not created at all**. That is the only use a row gets, and it is
exactly what makes the cut a consequence of the rows.

Nothing here scales one row against another or adds them together, which is what
the sketch in [#673](https://github.com/ciaranm/glasgow-constraint-solver/issues/673)
assumed a multi-resource certificate would need. Each row is used exactly where
the single row was used: to say that one transition cannot happen.

Rows that cannot rule anything out — whose members' demands sum to no more than
the capacity — are dropped before the programme is built, since a weight bound
against one would be a flag per state saying nothing. Such a row admits every
subset of the members, so no derivation could have used it.

Each state carries an extension variable per resource for
`Σ_{j≤i} c_{r,j} a_j ≥ w_r`, one for `Σ_{j≤i} π_j a_j ≤ p`, and one for their
conjunction — and each transition an implication per half, emitted as a `pol`
that leaves its clause one unit propagation away and then the clause. Each layer then gets an at-least-one saying its states are
between them complete, by resolution over the layer before. At the end one more
flag reifies the cut itself; every final state contradicts it, since a state with
a profit above `π₀` is precisely what `validate_lifted_cover_cut` refuses; and
resolving those against the last layer's at-least-one leaves the flag true.

Nothing in that is a search, and nothing in it can fail. What it deleted is the
whole of the previous scheme: the `Normalised` model of VeriPB's arithmetic, the
divisor and copy-count search, the cover enumeration inside the planner, and the
backward planner the window edges needed.

### Carrying a row onto other flags

Each resource is a separately posted `Cumulative` with its own activity flags, so
its row speaks a different language from the members' own. `recover_bridged_row`
([`flag_bridge.hh`](../gcs/innards/proofs/flag_bridge.hh)) translates it: weaken
the row down to the members, then add `c_j` copies of each member's bridge, which
puts every flag in with both signs so all of them cancel and the constants leave
the right-hand side where it was. The bridges are
`recover_conjunction_flag_bridge`'s, three `pol` per member per row, since
`active ⇔ before ∧ after` needs its conjuncts crossed first.

The direction is the thing to get right and the types will not tell you: to turn
`Σ c_j b_j ≤ C` into `Σ c_j a_j ≤ C` the sum has to be able to grow, so each
`a_j` must imply its `b_j`. Backwards, nothing cancels. The result is pinned, so
that a bridge pointing the wrong way is refused there rather than several
thousand lines later, and the `BridgeWrongTask` mutation is the test.

Whichever resource the members' flags already come from needs no crossing at all,
so a single-resource cut emits none of this and pays nothing for the machinery.
The crossing is emitted a proof level deeper than the caller's and forgotten on
the way out, along with the rest of the working: at `Top` there would be three
`pol` per member per resource per time point and none of them would ever be
deleted, which is [#666](https://github.com/ciaranm/glasgow-constraint-solver/issues/666)
all over again.

### Dominated states, which is what keeps this small

A state taking no more of *any* resource while allowing no less on the cut says
everything another one does, so the other can go. What survives is an antichain.

Over one resource that antichain is a staircase running strictly upwards in both
coordinates, so **a layer holds at most one state per achievable profit** — and
since a state whose profit exceeds `π₀` would be a point breaking the cut, no
layer can be wider than `π₀ + 1`. That is the whole reason this is affordable,
and it is why the size below does not depend on the capacity at all. `π₀` is a
cover's size minus one, so it is two or three on the constraints the procedure
actually infers, where a capacity-indexed programme would have been as wide as
the resource.

Over several resources the frontier is a Pareto set and there is no such bound to
lean on: a layer can hold many states of the same profit, differing in which
resource they have spent. Measured on all 83 lifted constraints Sidorov publishes
for Pack and Pack-d, switching every resource on takes the widest layer from 4 to
14 and the largest programme from 111 states to 222 — the same order, not a
different regime, because lifting drives the coefficients up and so keeps `π₀`
small whatever the capacities are. But "measured" is not "bounded", so
`with_programme_state_budget` exists and a cut over it is dropped and counted
separately from one that does not hold. It is never reached in the test suite,
and the sweep asserts that.

The dropped states are never named in the proof. A transition landing on one is
emitted straight into the state that covers it, which is valid for the same
reason the drop was. With more than one resource a single state can cover *both*
branches of a transition, which cannot happen over one.

### Restricting to a time point

A derived `Cumulative` has one height per task and one capacity, so every time
point's row has to carry the *same* coefficients. At the edges of the window only
some of the cut's tasks have flags — and only those have terms in the rows there —
so the cut is simply restricted to them, which stays valid because
setting an absent task's flag to zero is a point the cut already covered.

The programme has to be built again over the members that are present, which is
cheap and always succeeds; a restriction of a valid cut is valid. Answers are
cached per distinct present set, so the middle of the window uses the one
discovery already built and only the edges build their own.

**Testing this needs deliberate effort, and it is easy to believe you have.** A
task whose start domain is `[0, horizon - length]` has the window
`[0, horizon - 1]` *however long it is*, so a fixture built the obvious way gives
every task the same window, every time point has every member present, and no
restricted programme is ever built.
`InferredCumulativeStats::restricted_rows_rebuilt` counts what actually was, and
the test asserts on it — both that the ragged-window fixtures do restrict, and
that the uniform ones do not, so it stays clear which is testing what.

The other half of that trap: with proofs **off**, no row is derived at all
(`install_derived_cumulative` only runs a recipe when there is a logger), so a
corpus that never asks for a proof exercises none of this whatever its windows
look like. The verified sweep is a separate pass for exactly that reason, and it
asserts a non-zero restriction count so it cannot quietly stop covering them.

## Proof size, which is what decided the design

Measured, since the estimate that nearly sank this was out by two orders of
magnitude. Over a single resource one derived row costs about **twelve and a half
lines per state**, and the states are `members × (π₀ + 1)`:

| members | capacity | `π₀` | states | lines | bytes |
|--------:|---------:|-----:|-------:|------:|------:|
| 4 | 15 | 2 | 12 | 147 | 10 K |
| 6 | 20 | 3 | 22 | 272 | 21 K |
| 8 | 20 | 3 | 30 | 374 | 30 K |
| 12 | 20 | 3 | 46 | 578 | 54 K |

**The capacity does not appear.** Issue #675 budgeted `O(|S|² · C)` per time
point — around `10⁶` lines per constraint at `|S| = 10`, `C = 20`, horizon 1000 —
because it assumed a programme per lifting step, indexed by residual capacity.
Neither is needed: one programme certifies the finished cut, and the frontier is
indexed by profit, which is bounded by the right-hand side.

Each further resource adds a weight variable per state — two more lines to define
it and two more per transition — and however many states the Pareto frontier
turns out to need. On the published Pack constraints that is about three times a
single-resource row for three resources, plus the crossing, which is a few lines
per member per row per time point and is lost in the noise beside the programme.

Over a horizon, a derived `Cumulative` costs one such row per time point. For
eight members and a capacity of twenty:

| rows | lines | bytes | veripb | peak RSS |
|-----:|------:|------:|-------:|---------:|
| 200 | 75 K | 7.1 MB | 0.10 s | 19 MB |
| 1000 | 375 K | 36 MB | 0.53 s | 65 MB |

Linear, and half a second of checking for a horizon of a thousand. Scaffolding is
emitted one proof level deeper than the caller's and forgotten on the way out —
extension variables included, since deleting a variable's two defining
constraints deletes the variable — so **only one line per time point survives**,
and the other 373 do not outlive the row they establish. That is what keeps the
checker's memory down, and it is also why a scale harness like this *understates*
what hinting is worth: against a model this bare, even a hint-free step has
little to propagate over. See below.

The rule agreed with this design still stands: **take the replay, and look for
something shorter only once proof size or checking time is demonstrably a
problem.** On these numbers it is not.

### Hints, and what they are actually worth

Every RUP the replay emits names the lines it needs (issue #676). A hinted step
propagates over the cited constraints alone; a hint-free one propagates over the
whole live database, so its cost is set by everything else the proof is standing
in — which, at the root of a real model, is the whole model.

What each step cites follows from what it is:

- A **transition** `¬S_prev ∨ <other branch> ∨ S_succ` cites the source's forward
  reification, which puts its halves in hand; the `pol` per half, each of which
  carries one bound from source to successor once the branch literal is fixed;
  and the successor's reverse reification, which turns the halves back into a
  state. The clause naming each half used to be emitted — one line per half per
  transition — and is now the hint instead, because that step was the only thing
  that ever wanted it. That is where the size saving comes from: **94 of a
  single-resource row's 468 lines**, so about a fifth.
- A **source's at-least-one over its successors** cites its two transitions, or,
  where a capacity rules the member out, the surviving transition together with
  the source's forward reification and the `pol` that does the ruling out.
  Unit propagation often reaches that conclusion through the rows in the database
  instead, but a hinted step is only allowed what it names.
- A **layer's at-least-one** cites the layer before's and every one of that
  layer's successor steps, which is the resolution it is doing.
- The **conclusion** cites the last layer's at-least-one and the per-state
  clauses contradicting the cut flag.

Measured over the same eight-member, capacity-twenty rows as above, in one
sitting, minimum of five, one verify at a time — as a two-by-two, since dropping
the half-clauses and hinting the steps are separable:

| horizon 1000 | lines | bytes | veripb | peak RSS |
|---|------:|------:|-------:|---------:|
| clauses, hint-free (as it was) | 469 K | 42 MB | 0.84 s | 196 MB |
| clauses, hinted | 469 K | 44 MB | 0.63 s | 69 MB |
| no clauses, hint-free | 375 K | 35 MB | 0.71 s | 195 MB |
| no clauses, hinted (as it is) | 375 K | 36 MB | 0.53 s | 65 MB |

So on a bare model the hints buy 25 % of the checking time and two thirds of the
checker's memory, and dropping the clauses buys 15 % more — worth having, and not
obviously worth the trouble.

**On a real model it is an order of magnitude.** The same comparison over the
root-refutation certificates the #672 sweep produces, where the standing database
is an entire RCPSP model rather than one row per time point:

| instance | before | after | bytes before | bytes after |
|---|-------:|------:|-------------:|------------:|
| `pack008` | 3.84 s | 0.59 s | 48 MB | 42 MB |
| `pack012` | 3.68 s | 0.54 s | 43 MB | 38 MB |
| `pack018` | 12.10 s | 1.34 s | 112 MB | 100 MB |
| `pack025` | 16.27 s | 1.48 s | 124 MB | 111 MB |
| `pack039` | 6.05 s | 0.74 s | 57 MB | 50 MB |
| `pack043` | 17.69 s | 1.24 s | 98 MB | 84 MB |

**Six to fourteen times faster to check, for a proof 12 % smaller.** The size is
not what did it: the hint-free replay was paying the model's whole constraint
database on every one of its RUPs, and the deletion that keeps the *scaffolding*
from accumulating cannot do anything about the model underneath it. Peak memory
is unchanged here, because on these instances it is the model that sets it.

`pack043` is the shape of it: 292,117 hint-free RUP steps became 94,022 hinted
ones, and the whole certificate is left with **419** steps that propagate over
the database, none of them the replay's. What remains is 287 K `red` lines
defining extension variables and 262 K `pol` lines, and neither of those ever
looks at anything it does not name.

The lesson generalises past this constraint: **the value of hinting is set by how
much is standing, not by how much is being emitted.** A derivation measured in
isolation and found not to need hints may well need them once it is running
inside a real proof.

Nothing checks the hints beyond veripb itself, and nothing needs to: a hint set
that misses a line its step needs is a step that does not check, so the existing
cases fail. Dropping the source's forward reification from the transition hints
makes the first fixture in `lifted_cover_cut_test` reject.

### One step that is not what makes it sound

The `pol` that rules a member out weakens the row's other tasks out of it first.
That weakening is for the checker's benefit, not for soundness: every term left
in adds its own demand to the degree, and the literals it leaves behind cannot
between them cover a degree they raised by more than they can reach, so the
member is forced out either way. What the sweep buys is that the step lands on a
two-literal clause rather than on something as wide as the donor.

So a mutation that skips a weakening cannot be caught, and there is no longer one
that tries. The mutation that replaced it builds the programme against capacities
one below the rows', so that its states claim a row rules out a member it does
not — which veripb refuses inside the replay rather than at the pin.

**That mutation needs a fixture the tightening actually changes, and over several
resources it is easy to build one where it does not.** Every state is a subset of
the members that fits; if no feasible subset sits exactly at a capacity, taking
one off every capacity leaves the whole programme identical and only changes
which row gets the blame for a kill — and the kill is still true, so veripb
rightly accepts. Worse, even a genuinely misattributed kill can survive, because
the other rows are in the database and unit propagation can reach the same
conclusion through them. This is the conflict-shaped-rule problem from #660
again: corrupting the *route* is not a test when a second route is true. The
two-resource fixture is chosen so that tightening forbids something, and the
corruption that is specific to several resources — carrying a row onto the wrong
member's flags — is `BridgeWrongTask`.

## What is not here

- Optional tasks — not because a derived `Cumulative` cannot reason over them,
  but because this presolver bridges flags between donors and a presence
  conjunct has to cancel across that bridge before it may.
- Lifting during search: a constraint lifted from a conflict does not propagate
  after backtracking, so this is root-level only.
- Variable durations and demands are **not** on this list. A demand enters a
  column at the value the task is guaranteed to make and a duration at the one
  it is guaranteed to occupy; what a variable one costs is at most that task's
  place on that resource, never the donor. See `cumulative_donor_view`.
- Nothing else: the lifting is Equation 4's, over every resource, and every
  constraint it produces is derived.
