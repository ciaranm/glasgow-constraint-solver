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
every 0/1 point the donor's row allows satisfies it. So no set of tasks that
fits under the donor at one time point fails under the cut at that time point,
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
subproblems, which are the bottleneck. The defaults here are what its
experiments used — 100, 5 and 2·10⁴, with the capacity cap effectively off.

### Where this deliberately differs

**The lifting subproblem is one resource, not all of them.** The paper's
Equation 4 constrains over every resource at once, which is what makes its
lifting cross-resource. Ours is a single donor row, because that is what the
certificate can reach. This is a restriction on *what is inferred*, not only on
what is proved, and it is
[#673](https://github.com/ciaranm/glasgow-constraint-solver/issues/673).

**Two places where the paper and its implementation disagree**, both resolved in
favour of the code, which produced the published results:

- Algorithm 2 step L3 says to lift `arg min dᵢ`, shortest duration first; the
  implementation sorts by duration *descending*.
- Algorithm 1 picks "the longest task among the ones satisfying …", but the code
  compares a duration against an array *index* when doing so. Ours takes the
  longest, as the paper says.

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
`Σ πᵢ aᵢ ≤ π₀` holds at every 0/1 point the row allows exactly when
`max { Σ πᵢ xᵢ : Σ cᵢ xᵢ ≤ C }` is at most `π₀`. So rather than deriving that
conclusion, the proof derives the *computation*, in the states-and-transitions
shape of Demirović et al. (CP 2024) — and in its **one-sided** form, the one
their standalone knapsack solver uses, where a state says "at least this much
weight, at most this much profit" rather than "exactly this much of each".

`validate_lifted_cover_cut` builds the programme and answers the only question
worth asking of a candidate cut; `derive_lifted_cover_cut` emits it. Layer `i`
holds the (weight, profit) pairs the first `i` members can reach. A successor
either leaves the next member out, or takes it and pays its demand — and **a
successor that would overrun the capacity is not created at all**. That is the
only use the donor's row gets, and it is exactly what makes the cut a
consequence of it.

Each state carries three extension variables — `Σ_{j≤i} c_j a_j ≥ w`,
`Σ_{j≤i} π_j a_j ≤ p`, and their conjunction — and each transition an
implication, emitted as a `pol` that leaves its clause one unit propagation away
and then the clause. Each layer then gets an at-least-one saying its states are
between them complete, by resolution over the layer before. At the end one more
flag reifies the cut itself; every final state contradicts it, since a state with
a profit above `π₀` is precisely what `validate_lifted_cover_cut` refuses; and
resolving those against the last layer's at-least-one leaves the flag true.

Nothing in that is a search, and nothing in it can fail. What it deleted is the
whole of the previous scheme: the `Normalised` model of VeriPB's arithmetic, the
divisor and copy-count search, the cover enumeration inside the planner, and the
backward planner the window edges needed.

### Dominated states, which is what keeps this small

A state taking no more of the resource while allowing no less on the cut says
everything another one does, so the other can go. What survives runs strictly
upwards in both coordinates, which means **a layer holds at most one state per
achievable profit** — and since a state whose profit exceeds `π₀` would be a
point breaking the cut, no layer can be wider than `π₀ + 1`.

That is the whole reason this is affordable, and it is why the size below does
not depend on the capacity at all. `π₀` is a cover's size minus one, so it is
two or three on the constraints the procedure actually infers, where a
capacity-indexed programme would have been as wide as the resource.

The dropped states are never named in the proof. A transition landing on one is
emitted straight into the state that covers it, which is valid for the same
reason the drop was.

### Restricting to a time point

A derived `Cumulative` has one height per task and one capacity, so every time
point's row has to carry the *same* coefficients. At the edges of the window only
some of the cut's tasks have flags — and only those have terms in the donor's row
there — so the cut is simply restricted to them, which stays valid because
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
magnitude. One derived row costs about **fifteen lines per state**, and the
states are `members × (π₀ + 1)`:

| members | capacity | `π₀` | states | lines | bytes |
|--------:|---------:|-----:|-------:|------:|------:|
| 4 | 5 | 2 | 12 | 175 | 11 K |
| 6 | 10…80 | 3 | 23 | 331 | 23 K |
| 8 | 10…80 | 3 | 31 | 457 | 33 K |
| 12 | 10…80 | 3 | 47 | 697 | 59 K |

**The capacity does not appear.** Issue #675 budgeted `O(|S|² · C)` per time
point — around `10⁶` lines per constraint at `|S| = 10`, `C = 20`, horizon 1000 —
because it assumed a programme per lifting step, indexed by residual capacity.
Neither is needed: one programme certifies the finished cut, and the frontier is
indexed by profit, which is bounded by the right-hand side.

Over a horizon, a derived `Cumulative` costs one such row per time point. For
eight members and a capacity of twenty:

| rows | lines | bytes | veripb | peak RSS |
|-----:|------:|------:|-------:|---------:|
| 200 | 91 K | 6.9 MB | 0.19 s | 49 MB |
| 1000 | 457 K | 35 MB | 0.99 s | 164 MB |

Linear, and a second of checking for a horizon of a thousand. Scaffolding is
emitted one proof level deeper than the caller's and forgotten on the way out —
extension variables included, since deleting a variable's two defining
constraints deletes the variable — so **only one line per time point survives**.
That is what keeps the checking cheap as well as the memory: live constraints tax
every later unhinted RUP, and there are 456 of them per time point that do not
outlive the row they establish.

The rule agreed with this design still stands: **take the replay, and look for
something shorter only once proof size or checking time is demonstrably a
problem.** On these numbers it is not.

### One step that is not what makes it sound

The `pol` that rules a member out weakens the donor's other tasks out of the row
first. That weakening is for the checker's benefit, not for soundness: every term
left in adds its own demand to the degree, and the literals it leaves behind
cannot between them cover a degree they raised by more than they can reach, so
the member is forced out either way. What the sweep buys is that the step lands
on a two-literal clause rather than on something as wide as the donor.

So a mutation that skips a weakening cannot be caught, and there is no longer one
that tries. The mutation that replaced it builds the programme against a capacity
one below the donor's, so that its states claim the row rules out a member it does
not — which veripb refuses inside the replay rather than at the pin.

## What is not here

- **Multi-resource lifting**
  ([#673](https://github.com/ciaranm/glasgow-constraint-solver/issues/673)). A
  cut mixing demands from two resources needs the two rows scaled against each
  other, and neither schema here reaches that. The capacity-one stage spans
  resources by merging *at-most-ones*, which works because an at-most-one is
  scale-free; non-unit coefficients are not, which is exactly where that trick
  stops. Sidorov solves those subproblems and so could we — the precedent for a
  nested solve is `gcs/presolvers/auto_table/auto_table.cc` — but the result
  would have to be posted uncertified, which is not a trade this plan makes.
- Optional tasks, variable durations or demands, and lifting during search
  (a constraint lifted from a conflict does not propagate after backtracking, so
  this is root-level only).
