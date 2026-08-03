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

and, when `kappa < C`, posts a
[derived `Cumulative`](cumulative-proof-logging.md#derived-cumulatives-an-implied-constraint-that-adds-nothing-to-the-model)
over the same tasks with the same heights and a capacity of `kappa`. The donor
stays posted and the OPB is untouched: each per-time capacity row of the derived
constraint is *proved* from the donor's row for that time point, by
[subset-sum strengthening](subset-sum-strengthening.md).

The rules are Schulz's pre-solving strengthenings, recapped by Cloutier and
Quimper (CP 2026, §2.3).

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
propagation detected after the pre-solving is detectable beforehand". The useful
consequence is a *test*: with the energy rules off on both the donor and the
derived constraint, the search tree with the presolver must be
**node-for-node identical** to the one without it. Any difference means the
strengthening changed what the profile permits, which is the shape an unsound one
takes, and `cumulative_strengthening_presolver` asserts it on two fixtures before
VeriPB gets a say.

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

## Two deviations from the paper's rules

Both leave strengthening on the table; neither costs soundness or solutions.

**The per-time knapsack set is not restricted to `c_j < C`.** The paper's `kappa`
excludes tasks that fill the resource by themselves, which gives a smaller number
— a task with `c_j = C` reaches `C` on its own, so including it makes `kappa = C`
and the rule does nothing. Excluding it is only sound if those tasks' own heights
come down to `kappa` as well, which the paper's statement duly does ("all
consumption `c_i` such that `c_i = C`, as well as `C`, can be reduced to
`kappa`"). That changes the derived constraint's *coefficients*, and the
derivation for it needs at-most-one reasoning off the donor's row: if a task with
`c_j = C` is running, nothing else is, so the row's value is `kappa` either way.
That is the same machinery the coefficient-raising rule needs, and it is the
remaining half of issue #547.

**Coefficient raising is not implemented.** The paper's first rule — any `c_i`
above `C − min_j c_j` can be raised to `C`, because such a task can never run
beside another — changes heights for the same reason and needs the same
at-most-one derivation.

A note for whoever writes that half. The paper's condition takes the minimum over
*all* `j ∈ I`, task `i` included, which is sound but blunter than it needs to be:
what the argument actually requires is that `i` cannot run beside any *other*
task that consumes anything, i.e. `c_i + min{c_j : j ≠ i, c_j > 0} > C`. Issue
#547 states it that way, and that is the version to implement — with `c_i > 0`
guarded explicitly, since a zero-height task can always run beside anything and
the empty-minimum case would otherwise raise it to `C`.

## Fixtures, and one that cannot be one

The sharpness fixtures are checked as arithmetic against
`largest_subset_sum_at_most` *before* any proof is involved, because a fixture
that has drifted makes every claim built on it a claim about something else.

- **gcd path**: heights `{2, 4, 6}`, `C = 13` → `kappa = 12`, by division.
- **dynamic programming path**: heights `{6, 10, 4}`, `C = 13` → `kappa = 10`.

That second one is worth dwelling on, because the obvious reading gets it wrong.
Those heights have a gcd of two, so the gcd rule offers `2·⌊13/2⌋ = 12` — but the
largest load they can actually reach at or below thirteen is `4 + 6 = 10`, so the
answer is ten and only the dynamic programme gets there. Rounding by the gcd is
the whole answer only when the gcd's multiples are all reachable, which
`{2, 4, 6}` manages and `{6, 10, 4}` does not.

The deep gap this rule is usually illustrated with — heights `{6, 10, 15}` against
`C = 14`, overall gcd one, answer ten — is a subset-sum fixture and **cannot be a
`Cumulative` fixture**: a task of height fifteen under a capacity of fourteen can
never run at all, so the constraint is infeasible before any strengthening is
considered. The presolver declines a donor with a height above the capacity for
that reason, and the test keeps the arithmetic assertion without pretending it is
an instance.

## Restrictions

Each is declined rather than worked around, and counted in
`CumulativeStrengtheningStats` so that a model drifting into one does not simply
stop being strengthened in silence:

- **Optional tasks.** A derived `Cumulative` over an optional donor would need
  the donor's presence literals in every reason it gives; `DerivedCumulativeSpec`
  says the donor's `presences()` must be empty. This is the v1 bail-out issues
  #547–#549 are all specified to take.
- **Variable lengths, heights or capacity.** With a variable height the donor's
  row is over bit-linearised contribution flags rather than `height × active`, so
  a subset sum of the heights is not a subset sum of the row's coefficients.
- **A height above the capacity**, as above.
- **The dynamic-programming budget.**

## Testing it

`cumulative_strengthening_presolver` is built out of the observation that almost
every check a presolver normally faces is passed just as well by a presolver that
declined every donor. It writes nothing to the OPB, removes no solution, and —
being time-table neutral — does not even change the search tree unless energy
reasoning is on. So:

1. **The stats block is a tripwire, not decoration.** Every fixture asserts the
   presolver fired, on how many donors, by how many units of capacity, and down
   which of the two derivations. `CumulativeStrengtheningStats::rows_by_division`
   against `rows_by_dynamic_programming` is what stops a fixture drifting onto
   the other path without failing anything.
2. **Neutrality**, asserted as node-for-node equality under time-tabling alone.
3. **The energy differential**, where the strengthening is the only thing that
   refutes the `pack` fixture at the root.
4. **Solution preservation** over a random corpus against brute force, with an
   assertion that the presolver fired on some of it.
5. **Negative controls**: a capacity that is already the largest reachable load
   is passed over, the OPB matches a run with no presolver byte for byte, and no
   marker comment appears in the proof at all.
6. **Mutations**, both of which corrupt the *conclusion* rather than the route to
   it, which is what a rule whose content is a numeric bound needs: `ClaimOneBetter`
   claims one below the largest reachable load, and `BogusDivisor` rounds by a
   divisor that does not divide every height. VeriPB rejects each.

<!-- vim: set tw=72 spell spelllang=en : -->
