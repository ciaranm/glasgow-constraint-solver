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
infers and this cannot derive is **dropped and counted** as
`cuts_uncertifiable` — not weakened into something derivable, because a weakened
constraint is a different constraint and would quietly break the comparison the
exercise is for.

Over the test's twenty-five-instance verified sweep, between 95% and 100% of
attempted constraints certify, depending on seed. The shortfall is real and is
the honest measure of the gap between the published method and a certified one.

## The certificate

Everything is one shape of `pol`, and which one depends on the numbers.

Writing the row in the complemented form VeriPB normalises it to,
`Σ c_i ~a_i ≥ Σ c_i − C`, and the cut as `Σ π_i ~a_i ≥ Σ π_i − π₀`:

1. **Nothing at all**, when `Σ π_i − π₀ ≤ 0` leaves a degree no 0/1 point can
   miss. One RUP.
2. **One `pol`**: weaken the row down to the members, saturate or not, divide.
   This is `build_am1_from_row` with the divisor *free* rather than fixed at the
   one giving unit coefficients, and it is what the overwhelming majority of
   inputs need.
3. **A cover, then one `pol` per lifted member**: `μ` copies of the row weakened
   to the support so far plus the new member, `ν` copies of the cut so far, and
   a division. This is where the non-unit coefficients the implementation
   currently reaches come from: `2a + b + c + d ≤ 2` from
   `5a + 2b + 2c + 2d ≤ 5` is one copy of each, over three.

### The operation this vocabulary is missing

`pol` has a fourth operation these three do not use: pushing a **literal axiom**
(`x ≥ 0`), which cancels against that literal's complement and so shaves *part*
of a coefficient where `w` can only remove all of it. `window_energy` already
uses it; this file does not, and it should.

With it, the example above is **one `pol`**, not a chain. Adding one copy of
`a ≥ 0` to the complemented row `5~a + 2~b + 2~c + 2~d ≥ 6` cancels one unit,
giving `4~a + 2~b + 2~c + 2~d ≥ 5`; dividing by two lands exactly on
`2~a + ~b + ~c + ~d ≥ 3`. Verified against veripb with an `e` (equality) check,
so it lands there exactly and not merely somewhere implying it:

```
pol 1 aa + 2 d ;
e 2 ~aa 1 ~bb 1 ~cc 1 ~dd >= 3 : -1 ;
```

So "non-unit coefficients need a chain" — which an earlier version of this file
asserted — is **false**. What is true is that the two families are
*incomparable*: over all four-member instances with demands at most five, 157
cuts are reachable by a chain and by nothing in the one-`pol`-with-shaving
family, and 40 go the other way. The chain is not redundant; it is also not the
only route to a non-unit coefficient.

Adopting shaving is
[#674](https://github.com/ciaranm/glasgow-constraint-solver/issues/674) — though
[#675](https://github.com/ciaranm/glasgow-constraint-solver/issues/675) argues
for going the other way entirely and proof-logging the lifting DP, which would
be complete by construction and would delete this whole search.

The result is pinned with an `ia`, which is the only thing that says the `pol`s
arrived where the plan predicted. Every step is sound whatever it is fed, so a
prediction that had drifted from VeriPB's real arithmetic would derive
*something* — just not the line the constraint goes on to cite. The pin also
normalises, so the caller gets the literal-exact inequality whatever shape the
last `pol` left behind.

### Restricting to a time point

A derived `Cumulative` has one height per task and one capacity, so every time
point's row has to carry the *same* coefficients. At the edges of the window only
some of the cut's tasks have flags — and only those have terms in the donor's row
there — so the cut is simply restricted to them, which stays valid because
setting an absent task's flag to zero is a point the cut already covered.

The route, though, has to be found again, and *this* is where the backward
direction earns its keep: `plan_lifted_cover_cut` searches for a derivation of a
cut it is handed rather than choosing one. It is asked only about genuine
restrictions — the full-support plan is the one discovery already grew, and is
seeded into the cache — and its answers are cached per distinct present set.

Over a corpus of random cuts and every subset of each, 40% of the restrictions
came out trivial, 58% needed one `pol`, 2% needed the full chain, and none was
unreachable. A time point it cannot answer declines the whole constraint.

**Testing this needs deliberate effort, and it is easy to believe you have.** A
task whose start domain is `[0, horizon - length]` has the window
`[0, horizon - 1]` *however long it is*, so a fixture built the obvious way gives
every task the same window, every time point has every member present, and the
planner is never asked anything. `InferredCumulativeStats::restricted_rows_planned`
counts what actually reached it, and the test asserts on it — both that the
ragged-window fixtures do restrict, and that the uniform ones do not, so it stays
clear which is testing what.

The other half of that trap: with proofs **off**, no row is derived at all
(`install_derived_cumulative` only runs a recipe when there is a logger), so a
corpus that never asks for a proof exercises none of this whatever its windows
look like. The verified sweep is a separate pass for exactly that reason, and it
asserts a non-zero restriction count so it cannot quietly stop covering them.

## Proof size

One `pol` per step of the plan per time point, plus the pin — against the
capacity-one stage's `O(k²)` per time point.

Measured on the four-task fixture over twelve time points, the presolve prefix is
**51 lines and 2.4 KB: 24 `pol`, 12 `ia`, and 12 `del`** — a cover and one
lifting step per time point.

The twelve `del` are the point. Scaffolding is emitted one proof level deeper
than the caller's and forgotten on the way out, so **only the twelve pinned lines
survive** and the twenty-four working ones do not — which is the fix
[#666](https://github.com/ciaranm/glasgow-constraint-solver/issues/666) asks for,
applied from the start rather than retrofitted. Live constraints tax every later
unhinted RUP, so a derived constraint over a real horizon has to leave one line
per time point behind, not one per step.

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
- **Certified makespan bounds**
  ([#672](https://github.com/ciaranm/glasgow-constraint-solver/issues/672)).
  `largest_capacity_bound` is a number the presolver computed, not a bound the
  proof establishes. Turning it into a refutation of `[M ≤ μ]` for each candidate
  `μ`, and shipping a table of RCPSP bounds each with its verified `.pbp`, is the
  headline deliverable of issue #549.
- Optional tasks, variable durations or demands, and lifting during search
  (a constraint lifted from a conflict does not propagate after backtracking, so
  this is root-level only).
