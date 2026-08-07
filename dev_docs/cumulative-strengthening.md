# Strengthening a `Cumulative` by integrality

A capacity is worth more than it says. The load on the resource at any one time
is a sum of the heights of the tasks running then, so it can only ever take a
value that is a *subset sum* of those heights — and a capacity that is not
itself such a value has room in it that nothing can use.

`CumulativeStrengthening`
([`gcs/presolvers/cumulative_strengthening.hh`](../gcs/presolvers/cumulative_strengthening.hh))
is the presolver that takes that room away. For each posted `Cumulative` it
computes

```
    kappa = max over t of  ( largest subset sum of { h_i : task i can run at t }
                             that is at most C )
```

— over the tasks that can run *beside something*, which is the subtlety the whole
thing turns on, and posts a
[derived `Cumulative`](cumulative-proof-logging.md#derived-cumulatives-an-implied-constraint-that-adds-nothing-to-the-model)
at a capacity of `kappa`. The donor stays posted and the OPB is untouched: each
per-time capacity row of the derived constraint is *proved* from the donor's row
for that time point, by [subset-sum strengthening](subset-sum-strengthening.md).

The rules are Schulz's pre-solving strengthenings, recapped by Cloutier and
Quimper (CP 2026, §2.3).

## The tasks that fill the resource, and why they are set aside

Call a task **full** when it cannot run beside any other task that consumes
anything: `h_i + h_j > C` for every `j ≠ i` with `h_j > 0` whose window overlaps
its own. Such a task occupies the resource whenever it runs, whatever its height
says.

A full task ruins the subset sum. It reaches `C` on its own, so the largest
reachable load *is* the capacity and `kappa = C` and nothing happens — a task of
height `C` in the model turns the capacity rule off entirely. Excluding the full
tasks from the sum is Schulz's refinement, and it is only sound if their own
heights come down to `kappa` as well, which is what the derived constraint does:

| | capacity | full task's height | every other height |
|---|---|---|---|
| donor | `C` | `h_i` | `h_j` |
| derived | `kappa` | `kappa` | `h_j` |

Both of Schulz's height rules arrive at that same table. His coefficient raising
— any `c_i` above `C − min_j c_j` can be raised to `C` — is the same set of
tasks, since `c_i > C − min{c_j : j ≠ i, c_j > 0}` says exactly that no other
task fits alongside; and his knapsack rule's "`c_i = C` can be reduced to
`kappa`" is what happens to those tasks once the capacity moves. So there is one
rule here, not two, and `CumulativeStrengtheningStats::tasks_raised` counts it.

Stating it as the pairwise test rather than as the minimum is deliberate. The
two conditions are the same, but the pairwise one is what the certificate needs
anyway — one at-most-one per pair, off the donor's own row — and it does not
need the empty-minimum case argued separately. Tasks whose windows cannot
overlap are left out of the test, which is a little more than the paper claims
and costs nothing: if they can never be active together, no row ever mentions
both.

The set is **not** computed per time point, even though fewer tasks can run at
one time point than over the whole horizon and the set would be larger for it. A
`Cumulative` has one height per task, not one per time point, so a task that
only fills the resource at some of them cannot be given a raised height at all.

When *every* task is full, `kappa` is a subset sum over nothing and comes out at
zero. That is not a strengthening but a disjunctive, and the donor is declined:
inferring those from conflict cliques is
[`InferredDisjunctive`](inferred-disjunctive.md)'s job.

## Why `kappa` is the right number, and why the max is the max

At a time point `t` the load is a subset sum of `{h_i : i can run at t}`. Any
feasible assignment keeps it at most `C`, so it is at most `kappa_t`, the largest
such subset sum that does not exceed `C`. Since `kappa_t ≤ kappa` for every `t`,
the single capacity `kappa` holds everywhere, which is what lets one derived
constraint — with one capacity — carry the whole strengthening.

Taking the *maximum* over time points is the weakest of the per-time bounds, and
that is not a concession: a derived `Cumulative` has one capacity, and the
strongest single number that is valid at every time point is exactly the largest
of them.

## Time-table neutrality is a tripwire, not a caveat

The strengthening cannot change a time-table verdict. A profile value is a sum of
heights, so it exceeds `kappa` exactly when it exceeds `C`:

- if a load exceeds `C` it exceeds `kappa`, since `kappa < C`;
- if a load is at most `C`, it is a subset sum at most `C` of that time point's
  heights, so it is at most `kappa_t ≤ kappa`.

The paper says the same thing in one line — "time tabling is unaffected since any
propagation detected after the pre-solving is detectable beforehand".

A **raised** height needs its own argument, because the profile really is
different: a full task contributes `kappa` to the derived profile and `h_i` to
the donor's. What saves it is that a raised task conflicts with everything, so
every verdict the raised height reaches is one the donor reaches too:

- if a full task's compulsory part covers `t`, the derived profile there is
  already `kappa` and pushes every other task out — and the donor pushes them
  out too, since `h_i + h_j > C` for each of them;
- if none does, the derived profile at `t` is a sum of unraised heights, and the
  argument above applies to it unchanged; a full task is then pushed out of `t`
  exactly when something else is compulsory there, which the donor also does.

The useful consequence is a *test*: with the energy rules off on both the donor
and the derived constraint, the search tree with the presolver must be
**node-for-node identical** to the one without it. Any difference means the
strengthening changed what the profile permits, which is the shape an unsound one
takes, and `cumulative_strengthening_presolver` asserts it on four fixtures —
two that only move the capacity and two that raise a height — before VeriPB gets
a say.

The same theorem, used the other way round, is why the derived constraints ship
with **time-tabling off**: every time-table inference a derived constraint could
draw is one the donor draws already, at every node, so running it is pure cost.
`with_rules` turns it back on, and the neutrality test has to, because with it off
the comparison would pass without `kappa` having been used for anything. (This is
the issue's "measure propagation redundancy" question, answered by proof rather
than by measurement. Retiring the *donor's* propagators is the other half of it,
and remains a separate follow-up: the donor's rows are the semantic anchor and
its time-tabling is the only thing drawing those inferences at all.)

So do not expect this presolver to make anything faster on its own. The benefit
arrives with energy reasoning, where a window's supply is the capacity times its
width, and *that* is not a sum of heights. The `pack` fixture is the
demonstration: seven unit-length tasks of height three, all able to run in
`[0, 3)`, against a capacity of eight. The strengthening takes the capacity to
six, which changes no profile verdict at all, but the window then supplies
`6 × 3 = 18` against the `21` units the tasks need, and the overload check
refutes at the root. At a capacity of eight it supplies `24`, and the solver
searches.

The heights half has its own demonstration, and it is a fixture the capacity
rule alone gets *nothing* on: five unit-length tasks of height three plus one of
height eight, all able to run in `[0, 3)`, against a capacity of eight. The tall
task reaches the capacity by itself, so `kappa` over every task is eight and the
capacity rule declines the donor outright. Setting it aside takes `kappa` to six
and brings its own height down with it, and the window then supplies `18`
against the `21` those six tasks need. The donor needs `23` against a supply of
`24`, and searches.

## What reaches the proof

Schulz states two capacity rules, and they arrive in the proof as the two
derivations `derive_subset_sum_strengthening` chooses between:

| rule | when it applies | derivation |
|---|---|---|
| gcd rounding | the heights share a factor `d` and `d·⌊C/d⌋` is the largest reachable load | two `pol` steps of Chvátal–Gomory rounding |
| knapsack capacity reduction | otherwise | the layered dynamic programme |

The presolver does not choose between them — the utility picks whichever reaches
the true largest subset sum, which is always at least as strong as rounding, and
reports which it took in `SubsetSumStrengthening::by_division`. What the
presolver does is *predict* the choice, using the same test, so that it can
budget: the dynamic programme costs three flags per state and a state per
reachable partial sum per item, per time point, and a donor whose derivation
would exceed `with_dynamic_programming_budget` is passed over entirely rather
than producing a great deal of proof for a strengthening worth one unit. The
rounding path is two `pol` steps and is not budgeted. `CumulativeStrengtheningStats`
counts rows both ways, and the budget fixture asserts the prediction agrees with
the choice — if it did not, the budget would decline the wrong donors.

### Every row lands on the declared capacity

A time point whose own `kappa_t` is below `kappa` yields a *stronger* row than
the derived constraint declared. The recipe does not hand that back. It closes
with an `ia` step against `Σ h_i·active_{i,t} ≤ kappa`, which is an implication
check and therefore syntactic.

Two things come of insisting on that. The rows are uniform, so the propagator's
`pol`s cancel against a known degree rather than against whatever each time point
happened to prove. And — the reason it is worth a line per time point — it is the
only thing in the proof that notices a derivation landing somewhere other than
where it claimed. A divisor that does not divide every height still divides
*soundly*; VeriPB accepts every step of that derivation and the resulting line is
true, it is simply not the line the derived constraint was told it had. The
`BogusDivisor` mutation is exactly that, and the `ia` step is what rejects it
("expected constraint is not syntactically implied by the constraint at the
hint"). Nothing else in the proof objects. This is
[the third net](subset-sum-strengthening.md#testing-it) the subset-sum utility's
own tests describe, applied at the point of use.

## Raising a coefficient, in cutting planes

The capacity half is one call to the subset-sum utility. The heights half is not,
and the reason is worth having written down, because the obvious derivation does
not work and it is not obvious why.

The row wanted at time `t`, over the full tasks `F` present and the rest `N`, is

```
    sum_{i in F} kappa·a_i  +  sum_{j in N} h_j·a_j  <=  kappa
```

It is implied by the donor's row alone. If a full task is active, everything else
is off and the left side is exactly `kappa`; if none is, the left side is a subset
sum of `N`'s heights that the donor keeps at most `C`, hence at most `kappa`. So
there is a derivation to find. The route is:

1. the pairwise **at-most-ones**, one per pair the full tasks are in, each
   [off the donor's own row](../gcs/innards/proofs/am1_from_row.hh) — weaken the
   others out, saturate, divide;
2. the full tasks **weakened out** of the row, leaving `sum_N h_j·a_j <= C`;
3. **subset-sum strengthening** of what is left, to `kappa_t`, then an `ia` step
   relaxing it to the declared `kappa` if the two differ;
4. each full task's coefficient **raised** from zero to `kappa`, in the row the
   last one left behind.

Step 3 has to happen before step 4 and not after: a raise keeps whatever right
hand side it is given and can raise a coefficient no higher, so a row left on a
smaller `kappa_t` would neither reach `kappa` nor pin to it.

### Why step 4 is a loop

Given the row `c·a_i + sum_k w_k·a_k <= R` and the at-most-ones tying `i` to each
`k`, one `pol` raises `c` by `k` while keeping `R`: take `lambda` copies of the
row, add each at-most-one weighted by its own `w_k`, scaled by `e`, and divide by
`lambda + e`, with `lambda/e = (T − c − k)/k` and `T = sum_k w_k`. Every
coefficient divides exactly; only the degree rounds, and it has `e·(T − R)` to
round through, so the step lands back on `R` exactly when

```
    k · (T − R)  <  T − c
```

That bound is the whole of it. When the rest of the row only just overshoots the
capacity — `T − R = 1` — one step raises all the way. When it overshoots by half,
the steps are of size one and the raise costs a `pol` per unit of `kappa`. And no
single `lambda`, `e`, divisor and set of weakenings does better: asking for the
whole raise at once forces `(k − 1)·(T − R − 1) < 1`, which is why the loop is
there and not a tidier one-shot. Hence `with_raise_budget`, which caps the lines
this may spend on a donor; `raise_steps()` computes the same sequence for the
budget and for the derivation, since a prediction that disagreed would decline the
wrong donors.

Two ends of the loop are not the loop:

- `T <= kappa` — everything else fits alongside — needs no division at all. The
  at-most-ones summed *are* the row, at a right hand side of `T`, which one `ia`
  step relaxes to `kappa`. So a time point like this pays for no subset sum
  either, and step 3 is derived lazily for that reason.
- `T = 0` — nothing else can run at `t` — has no row to raise into and no
  at-most-one to do it with. The claim is only that a flag is at most one, and
  it is RUP.

### What the pin catches, and what nothing catches

Every step above is sound whatever it is fed, so a wrong margin, a wrong step
size or a missing weakening all land on lines that are true and simply weaker
than intended. The row's closing `ia` step is what rejects them, and the
`RaiseTooFast` mutation is exactly that: one step past the bound, the degree
rounds down instead of up, and every later step compounds it.

What no proof can catch is the *set*. If a task that does not conflict with
everything is raised anyway, the derivation runs honestly and the row it lands on
is simply not implied by the donor — which VeriPB does reject, but only because
the conclusion is false, not because anything about the derivation was wrong.
`RaiseUnentitled` covers it, on the control fixture where the tallest task misses
the pairwise test by exactly one. `recover_am1_from_row` refuses a set that does
not overshoot the capacity outright for the same reason:
[it cannot be caught later](../gcs/innards/proofs/am1_from_row.hh).

Those at-most-ones all come off *one* donor row, which is the case where
recovering a whole set's bound in one step beats recovering its pairs. The
rule's own shape hides most of the win — the raise needs the individual pairwise
lines, one per step, so they cannot simply be replaced — but a time point where
only full tasks can run is exactly `sum_F a_i <= 1` and is one `pol`. Left for
the proof-size pass, with #666.

## Fixtures, and one that cannot be one

The sharpness fixtures are checked as arithmetic against
`largest_subset_sum_at_most` *before* any proof is involved, because a fixture
that has drifted makes every claim built on it a claim about something else.

- **gcd path**: heights `{2, 4, 6}`, `C = 13` → `kappa = 12`, by division.
- **dynamic programming path**: heights `{2, 6, 6}`, `C = 10` → `kappa = 8`.
- **raising**: heights `{5, 4, 2}`, `C = 6` → the five is raised to six, and the
  capacity does not move at all; its control, heights `{4, 4, 2}`, sits exactly
  on `C − min` and is not raised, so the whole donor is then declined.

The second is worth dwelling on, because the obvious reading gets it wrong. Those
heights have a gcd of two, so the gcd rule offers `2·⌊10/2⌋ = 10` — but the
largest load they can actually reach at or below ten is `2 + 6 = 8`, so the
answer is eight and only the dynamic programme gets there. Rounding by the gcd is
the whole answer only when the gcd's multiples are all reachable, which
`{2, 4, 6}` manages and `{2, 6, 6}` does not.

The textbook version of that fixture — heights `{6, 10, 4}` against `C = 13` — is
not one any more, and the reason is the heights half. The ten conflicts with both
of the others, so it is full: it is set aside, `kappa` is computed over `{6, 4}`
and comes to ten, and the derivation is a raise rather than a subset sum. A
fixture for the dynamic programme needs every task to fit beside *something*,
which is what `{2, 6, 6}` was chosen for.

The deep gap this rule is usually illustrated with — heights `{6, 10, 15}` against
`C = 14`, overall gcd one, answer ten — is a subset-sum fixture and **cannot be a
`Cumulative` fixture**: a task of height fifteen under a capacity of fourteen can
never run at all, so the constraint is infeasible before any strengthening is
considered. The presolver declines a donor with a *mandatory* task's height above
the capacity for that reason, and the test keeps the arithmetic assertion without
pretending it is an instance. An optional task of the same shape is a presence
about to be falsified rather than a donor that cannot be satisfied, so it is set
aside and the rest of the donor is strengthened as usual.

## Restrictions

Each is declined rather than worked around, and counted in
`CumulativeStrengtheningStats` so that a model drifting into one does not simply
stop being strengthened in silence:

- **An irreducible capacity**, which today means a capacity that is a *view*.
  Its reification is over its own bit vector, so the capacity's bound rows have
  nothing in the donor's row to cancel against and there is no order literal to
  resolve. An ordinary variable capacity is fine: the row is reduced against the
  bound the capacity has at presolve time, and that condition is discharged in
  the same `pol`.
- **A mandatory task whose guaranteed demand is above the capacity**, which
  makes the donor infeasible on its own — its own propagator's business, and
  not something to build a subset sum around. An *optional* task of the same
  shape says only that its presence is false, and is set aside instead.
- **A capacity too large to subset-sum over.** Unlike everything else here this
  is not about proof size: `kappa` is found with a bitset over the capacity's
  whole range, rebuilt at every time point, and that runs with proofs off too.
  A resource measured in thousandths would spend hundreds of megabytes deciding
  whether there was anything to be had. `with_subset_sum_capacity_limit` is the
  knob.
- **Every task full**, which makes `kappa` zero: a disjunctive rather than a
  strengthening, and inferring those from conflict cliques is what
  `InferredDisjunctive` does.
- **Nothing to gain** — the capacity is already the largest load the tasks can
  reach and no height moves either. The honest and common answer.
- **The dynamic-programming budget**, and separately **the raise budget** —
  different costs in different units, so a donor can want one and not the other.

Optional tasks are deliberately **not** on this list. The whole strengthening is
an argument about the donor's per-time rows, and an optional task's presence is a
conjunct inside its activity flag rather than a term beside it, so those rows are
the same shape either way and every subset sum, at-most-one and raise reads them
identically. What the presence changes is the reasons the derived constraint's
propagator gives, which `install_derived_cumulative` handles once it is told the
donor's presence arguments — see
[cumulative-proof-logging.md](cumulative-proof-logging.md). `InferredDisjunctive`
and `InferredCumulative` still decline, for a reason that is theirs rather than
this one's: they bridge flags between donors, and a presence conjunct has to
cancel across that bridge first.

Variable lengths and heights are deliberately **not** on this list either, and
nor is a variable capacity. `CumulativeDonorView`
([`donor_view.hh`](../gcs/constraints/cumulative/donor_view.hh)) reduces a donor
to the part of itself the argument can be made over, per *task*, and what is left
as a set-aside is a task that cannot be argued about at all: a height that is a
view, or one whose lower bound is zero. `donors_with_set_aside_tasks` counts the
donors that had one, because one strengthened over four of its five tasks
otherwise looks just like one strengthened in full.

An ordinary variable height is **converted** rather than set aside: its terms in
a row are the bits of a linearised contribution, and the row saying the
contribution is at least the height turns them back into a coefficient on the
activity flag, at the demand the task is guaranteed to make. That is not always a
gain here, and it is the one place in this presolver where the answer is a
judgement rather than a rule. `kappa` is the largest subset sum the capacity
allows, so adding a task can only push it up: heights `{3, 3}` under a capacity
of eight give six, and converting a fifth task at a guaranteed demand of one
gives seven — a unit of strengthening surrendered to gain one task's energy in
the overload check. Both are arithmetic and neither dominates, so the donor is
assessed both ways and the bigger reduction kept, with
`donors_better_off_setting_heights_aside` recording when the conversion lost.

Where *every* height is a variable — the multi-mode RCPSP shape, a task picking a
mode that fixes its duration and its demand — there is no "without" to lose to:
before conversion such a donor had no usable task at all and was declined
outright.

A variable **length** is not set aside at all. No length appears in a capacity
row, so the rows are the same rows; what it costs is the `after` pin, and the
donor's proof-only end proxy is what that goes through, published for the purpose
(#685). Such a task therefore keeps its term, its window and its mandatory part
— which is what earns it a place here, this presolver running the energy rules
alone and the (TTOC) profile term being the one that can count a task the
window-energy lemma cannot.

## Testing it

`cumulative_strengthening_presolver` is built out of the observation that almost
every check a presolver normally faces is passed just as well by a presolver that
declined every donor. It writes nothing to the OPB, removes no solution, and —
being time-table neutral — does not even change the search tree unless energy
reasoning is on. So:

1. **The stats block is a tripwire, not decoration.** Every fixture asserts the
   presolver fired, on how many donors, by how many units of capacity, on how
   many raised heights, and down which derivation.
   `CumulativeStrengtheningStats::rows_by_division` against
   `rows_by_dynamic_programming` is what stops a fixture drifting onto the other
   path without failing anything, and `tasks_raised` is the only record that the
   heights half ran at all — a raise can leave the capacity untouched, and a
   capacity reduction can raise nothing.
2. **The split, checked as arithmetic** before any proof, the same way `kappa`
   is: which tasks are full, and what `kappa` over the rest comes to. The rule
   turns on the pairwise test, and a fixture that has drifted over the boundary
   is a fixture for the other case.
3. **Neutrality**, asserted as node-for-node equality under time-tabling alone,
   on fixtures that raise as well as fixtures that do not.
4. **Two energy differentials**: the `pack` fixture, where the capacity rule is
   the only thing that refutes at the root, and the full-task pack, where the
   capacity rule gets nothing and only the raising refutes.
5. **Solution preservation** over a random corpus against brute force, with
   heights drawn against each instance's own capacity so that full tasks turn up
   — a fixed height pool gives instances that are declined outright, and covers
   the heights half only by accident. A second, smaller sweep runs the same
   instances with proofs on and veripb checking every one, which is where the
   raise arithmetic's odd corners get exercised.
6. **Negative controls**: a capacity that is already the largest reachable load
   is passed over, a task exactly on `C − min` is not raised, the OPB matches a
   run with no presolver byte for byte, and no marker comment appears in the
   proof at all.
7. **Mutations**, each corrupting the *conclusion* rather than the route to it,
   which is what a rule whose content is a number needs: `ClaimOneBetter` claims
   one below the largest reachable load, `BogusDivisor` rounds by a divisor that
   does not divide every height, `RaiseTooFast` takes one step past the bound the
   division survives, and `RaiseUnentitled` raises a task that does not qualify.
   VeriPB rejects each.

<!-- vim: set tw=72 spell spelllang=en : -->
