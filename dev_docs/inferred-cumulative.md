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

For the example above, with every task of length four, that is `20 / 2 = 10`
against the donor row's own `44 / 5 = 8.8`. A horizon of nine satisfies the
resource and not the cut, which is exactly the fixture the test refutes at the
root.

Where the ratio does **not** improve, the cut is dropped and counted. The donor
already said it better, and posting a second constraint to say it worse is a
propagator that cannot pay for itself.

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

## Finding the cut

Per posted `Cumulative`, over its tasks with a constant positive length and
demand, discarding any task whose demand alone exceeds the capacity (it can never
run, and would pad every cover it touched):

1. **Covers**, biggest demands first: start at each task in turn, take the
   next-biggest until the capacity is overshot, then drop anything whose removal
   leaves it still overshooting. Starting *further down* the list is what
   produces a cover of small tasks, and that is where the interesting cuts are —
   a big task lifted into such a cover takes a coefficient above one, which is
   the whole gain over the capacity-one stage.
2. **The cover inequality**, which is
   [`build_am1_from_row`](../gcs/innards/proofs/am1_from_row.hh)'s program:
   weaken the row down to the cover, saturate, divide by the margin.
3. **Lifting**, over the remaining tasks in descending demand, run *forward*:
   sweep the one-`pol` steps the certificate allows, see what each produces, and
   take whichever result argues about the most energy. A task no step improves
   on is left out.

Both budgets (`N_cover`, `N_out` in the paper) count what they drop.

## Forward, not backward

The textbook version of step 3 goes the other way. Sequential lifting (Padberg,
Zemel) computes the largest coefficient a task can validly take — the right-hand
side less the most the current support can weigh while still leaving that task
room to run, a knapsack — and *then* you go looking for a derivation of it.

That is the wrong way round here, because **the largest valid coefficient is not
the largest reachable one**. A lifted inequality's validity is coNP-hard to
decide, so nothing may be posted on the strength of the presolver's own
arithmetic; every cut has to arrive with a derivation. Asking the knapsack first
means asking for coefficients the arithmetic cannot deliver, discovering that by
failing, and stepping down until something works.

`grow_lifted_cover_cut` runs the arithmetic forward instead: every candidate
weighed is one that derives, so there is nothing to step down from and no
knapsack to run. It is also *stronger*, because a forward step may move the
coefficients already in the cut when that improves the ratio, which a lifting
step by definition cannot. On the test's sixty-instance corpus that is the
difference between 8 and 16 cuts carrying a non-unit coefficient, and between 76
and 108 members brought in.

The backward direction still exists and is still needed — but only where the cut
is *given* and not up for negotiation, which is the window-edge case below.

## What is not taken on trust

Growing a cut forward means predicting what each `pol` will produce, which means
an in-tree model of VeriPB's normalised form. That model could drift from the
real thing, so nothing relies on it being right: every cut ends in an `ia` pin
against the exact inequality claimed, and that check is veripb's. A drifted model
gives a **rejected proof** at that line, not an unsound row.

Separately, `lifted_cover_cut_test` checks the planner against a brute-force
oracle that needs no proof checker at all: a few thousand random claims, most of
them nonsense, with every occupancy point enumerated for any it accepts. About
700 are planned per seed, 120-odd with a non-unit coefficient, and none has ever
been invalid.

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
   a division. Non-unit coefficients live here and nowhere else. No single
   weaken/saturate/divide reaches `2a + b + c + d ≤ 2` from
   `5a + 2b + 2c + 2d ≤ 5`; one copy of each, over three, does.

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
