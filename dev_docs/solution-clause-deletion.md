# Deleting solution clauses from a proof

When the solver logs a solution, VeriPB derives a constraint from it and puts
that constraint in the **core** set:

- `soli`, for an optimisation problem, adds the objective-improving constraint
  `objective <= value - 1`;
- `solx`, for an enumeration, adds the blocking clause that forbids the
  solution's assignment to the preserved variables.

Neither goes away on its own. Without the machinery this note describes, a proof
that finds *n* solutions ends with *n* extra core constraints, every one of them
in the way of every unit propagation for the rest of the proof. On a 33k-solution
enumeration that was 4x the verification time.

Both are deleted now. The two cases are unrelated in every way except the shape
of the problem, so they are dealt with separately.

## What deleting from core costs

VeriPB splits its constraint database into a **core** set and a **derived** set.
Everything the solver derives with `pol`, `rup`, `red` or `ia` goes into the
derived set, and deleting from there is free — which is what lets
`forget_proof_level` throw away a whole subtree's reasoning with one `del range`.

Deleting from the *core* set is not free. It needs a **deletion check**: a
demonstration that what remains of the core still implies the constraint being
removed, checked exactly as redundance-based strengthening is, and — this is the
part that shapes everything below — able to propagate over **core constraints
only**.

VeriPB does not fail a proof when that check fails. It logs a warning, downgrades
to unchecked deletion, and stops making the equi-enumerable / equi-optimal
guarantees for the rest of the proof; an `s VERIFIED` line still comes out. What
saves us is that it also stops counting excluded solutions and stops updating the
best *valid* objective value, so an `ENUMERATION_COMPLETE n` or `BOUNDS` line
afterwards fails on the count. That is a real backstop but a distant one, so
every proof the test suite verifies is verified with
**`--force-checked-deletion`**, which turns the warning into an error where it
happened (`run_test_and_verify.bash` and `verify_proof_and_dispose` in
`constraints_test_utils.hh`).

## soli: the next bound deletes the last

An objective-improving constraint is superseded the moment a better solution is
found: `objective <= v' - 1` for `v' < v` implies `objective <= v - 1` outright.
So `ProofLogger::solution` remembers the pair of lines each `soli` produces — the
`soli` itself and the `objective < value` atom emitted beside it — and deletes
them when the next `soli` arrives. The deletion check is a plain RUP against the
new bound, which unit propagation over the objective's bits discharges without
help, for every gap and for a signed objective as well as an unsigned one.

The `soli` line therefore stays at `ProofLevel::Top`: the incumbent bound has to
outlive the subtree it was found in, because every later branch anywhere in the
tree prunes against it. Only the arrival of a better one may take it away.

This is close to free, and close to worthless as an optimisation — branch and
bound finds few incumbents, so there were never many of these. It is here because
it is right, and because it costs one `del` line per solution to have it.

## solx: the backtrack clause deletes the blocking clause

A blocking clause is not like an incumbent bound. It only has to hold while the
search is somewhere it could rediscover the same solution — and the backtrack out
of the leaf that found it says exactly that the search is not there any more. So
the `solx` line is recorded at `ProofLevel::Current`, which in a solution leaf at
depth *d* is level *d+1*, and the frame's own tail deletes it:

```
solx i[_1][eq1] i[_2][eq2];      <- VeriPB adds the blocking clause, in core
% backtracking
rup 1 ~i[_1][eq1] 1 ~i[_2][eq2] >= 1;
core id -1;                      <- the backtrack clause, moved to core
del id -2;                       <- forget_proof_level takes the blocking clause
```

The deletion check works because the solution lies under the very guesses the
backtrack clause forbids: negating the blocking clause fixes every preserved
variable to the solution's values, propagation reaches each guess literal, and
the backtrack clause is falsified.

Backtrack clauses then have to be deleted in turn, and they are, by the same
argument one level up: the clause for a child, over the guesses `g1..g(d+1)`, is
implied by the parent's, over `g1..gd`, by weakening. The parent emits its own
clause *before* forgetting the level below, so the witness is always in place by
the time it is needed.

### Which backtrack clauses go to core

Only the ones that have to. A frame's clause is promoted exactly when the level
it is about to forget can hold a core constraint, and only two things put one
there: a `solx` blocking clause, recorded by a solution leaf, and a child's
promoted clause. Both amount to "a solution was found somewhere under here",
which is what `this_subtree_contains_solution` already says, so `solve_with_state`
passes `ClauseSet::Core` on exactly that condition (and only for an enumeration —
an optimisation logs `soli` and never lands anything core at a search level).

A subtree with no solutions in it pays nothing, and neither does a refutation.

### Restarts

A restart unwind is the one place a frame discards the level below it without
deriving a backtrack clause of its own. What justifies the deletions there are
the reduced nld-nogoods the unwind already learns (see
[restarts, nogoods and weighting](restarts-nogoods-weighting.md)): each is a
subset of the backtrack clause of the sibling it was learned from — reduction
drops decisions, it does not add any — and so implies it. A nogood is something
the search derived rather than part of any variable's encoding, so nothing puts
it in core on its behalf: it is moved across explicitly, under the same condition
as the backtrack clauses. One is emitted for every refuted sibling, whatever
shape its decision has, because skipping one would leave a deletion with nothing
to check it against.

### Assertion levels

Above `AssertionLevel::Definitions` the proof stops writing the encoding down and
asserts its links instead, so nothing could carry a blocking clause's
preserved-variable assignment across to the atoms a backtrack clause is written
in, and the deletion check could not succeed. Such a proof keeps its blocking
clauses: `ProofLogger` records them at Top again and promotes no backtrack
clause. It is not a self-contained proof in the first place, and this is one more
thing it leaves to whoever consumes its assertions. (Nothing needs suppressing on
the encoding side — at those levels the definitions are not emitted at all, so
there is nothing to move.)

The `soli` deletions are unaffected, and stay on at every level: an objective
bound and its successor are constraints over the same objective bits, and the
check between them needs no definitions.

## Why the encoding has to be in core too

This is the part that is not obvious. A blocking clause is written over the
**preserved** variables, which is to say a variable's *bits*. A backtrack clause
is written over branching decisions, which is to say its *order*, *equality* and
*interval* atoms. What carries one to the other is the linking constraints — and
the deletion check may only propagate over the core.

For a literal that already existed when the model was written, the links are OPB
rows, and the OPB is core, so this is invisible. For a literal first needed
partway through the search — an interval literal a brancher asks for, an equality
atom for a value nothing had mentioned yet — the links are `red` lines in the
proof, and land in the derived set where the deletion check cannot see them. That
is not a corner case: it is most of them, and the first attempt at this failed on
essentially every constraint test for exactly this reason.

So a variable's **encoding** goes into core. `ProofLevel::TopAndCore` is how it
says so: it means what `Top` means — keep this for the whole proof — and
additionally emits a `core id` for the line. Every one of the tracker's emissions
names it, and nothing else does, so what is in core is visible at the point each
constraint is created rather than inferred from surrounding state.

### Where the line is drawn, and why there

Structurally, not by need: *the encoding of a variable is in core; what a
propagator derives about a problem is not.*

Drawing it by need would be smaller. Deleting a backtrack clause needs no
encoding at all — negating the child's clause sets its guess literals directly,
and the parent's clause is a literal-subset of them, so it falsifies by
subsumption; same for the restart nogoods. The only check that has to cross from
bits to atoms is the blocking-clause one, and its path today is `bits → gevar →
eqvar / interval` through those literals' own defining rows. On `langford 7`,
that would be about a third of what actually goes across.

It is drawn structurally anyway, for two reasons.

The first is that "by need" is not a property anything can rely on. Which rows a
check needs depends on what the search happened to branch on — nothing stops a
user's brancher from branching on intervals, which the built-in heuristics other
than `reject_random_interval` do not — and on which of several shapes a literal
was given, since `define_plain_invar`, the cell / `not_in_range` route and a
view's own range literals all reach a range literal differently. Establishing
that the definitions alone suffice meant reading all three, and it would need
re-establishing every time the literal machinery moved. A rule that changes with
either is a poor foundation for anything that reasons about the core, such as a
redundance-based symmetry break.

The second is that the *converse* — putting more than the encoding in core — is
not free either. VeriPB's solution check (`get_unsatisfied_core_constraint`)
requires **every core constraint** to be satisfied by the solution's propagated
assignment, and does not look at derived ones at all. Sweeping a propagator's
standing lemmas into core would quietly make every one of them an obligation on
every later `solx`, with a `SolutionNotSatisfiedConstraint` landing a long way
from the propagator that caused it.

### Not deferred, and not batched either

The `core id` goes out with the line it names. Two earlier versions of this did
less work and were both worse.

The first deferred the move to the first excluded solution, which made a
refutation byte-identical to what it had been. That is not worth having: it makes
"is this link in core?" answerable only relative to how far the search has got,
and a core-sensitive step would silently see one core before the first solution
and another after. For the same reason the move is not conditional on the proof
being an enumeration either — an encoding that is core when an objective is
posted and derived when one is not would be just as awkward to reason against.

The second kept an RAII scope over each of the tracker's entry points and flushed
one `core range` per contiguous run when the outermost scope was released. That
one is defensible — nothing between entering and leaving a scope can observe core
membership, so it was batching rather than deferral — but it put the answer to
"does this constraint go in core?" in ambient state that a caller could not see,
and it was not paying for itself: emitting the ids eagerly instead costs 1-3% of
proof size (`langford 6` +3.3%, `langford 7` +1.9%, `langford 8` +0.8%,
`regular_random -n 6` +0.004%) and, measured on all four, nothing at all in
checking time.

## What it costs and what it buys

Measured on this machine, against the same solver without any of this:

Enumeration, which is what this is for:

| instance | solutions | proof size | veripb |
| --- | --- | --- | --- |
| `langford 6` (refutation) | 0 | +5.3% | unchanged |
| `langford 7` | 52 | +3.3% | +6% |
| `langford 8` | 300 | +1.5% | +21% |
| `regular_random --all --seed 1 -n 6` | 32985 | +6.0% | **4.3x faster** |

The cost is one extra RUP check per backtrack on a path to a solution, paid
whether or not there are enough solutions for the deletions to earn it back. The
benefit grows with the number of live blocking clauses avoided, so it is
superlinear in the solution count and the crossover is somewhere in the low
thousands. A proof with a handful of solutions is slightly worse off; a proof
with enough solutions for its verification cost to be a problem in the first
place is much better off.

The `langford 8` figure was +11% when propagator lemmas were being swept into
core along with the encoding, and became +23% when they stopped being. Confirmed
by putting them back, which restores the old figure exactly: the deletion checks
were using those lemmas as shortcuts, and without them propagate further through
the encoding instead. That is the price of the narrower rule, taken deliberately
— see the two reasons above.

### What an optimisation proof pays

An optimisation proof deletes only `soli` constraints, and that check needs no
encoding at all — an objective bound and its successor are constraints over the
same objective bits, which are OPB rows. So the encoding being in core buys
nothing here, and it is not free:

| instance | baseline | with the encoding in core |
| --- | --- | --- |
| `table_layout --size 5` | 0.55s | 1.11s |
| `tour` | 1.38s | 2.47s |
| `table_layout --size 4` | 0.26s | 0.38s |
| `talent` | 3.60s | 2.84s |
| `knapsack`, `p_dispersion`, `colour` | < 0.03s | unchanged |

Isolated: suppressing the `soli` deletions changes none of these, while taking
the encoding back out of core reproduces the baseline column exactly, so the
whole swing is VeriPB's per-solution check, which has to find every core
constraint satisfied by the propagated assignment. Why `talent` moves the other
way is not established.

This is the price of the encoding being in core unconditionally rather than only
where a blocking clause could need it. It is paid deliberately: gating it on the
kind of proof would mean a redundance-based symmetry break seeing the encoding in
core when enumerating and not when optimising, which is the sort of thing that is
very hard to be sure about later. But it is a real cost on a real workload, not a
rounding error, and worth revisiting if optimisation proof checking becomes the
thing that hurts.

## Testing

Every proof the suite verifies is verified with `--force-checked-deletion`, so
any deletion whose check does not hold fails the test that produced it, rather
than silently downgrading the guarantee. Adding that flag on its own left the
suite green, which is what says it was a no-op before this work.

`gcs/solve_test.cc` has the two shape tests, `Enumeration deletes its
solution-excluding clauses` and `Optimisation deletes its superseded objective
bounds`. They exist because losing the deletions leaves every proof still
verifying — just with a core set that grows once per solution — so nothing else
in the suite would notice. They compute where the blocking clause has ended up
relative to the backtrack clause and check that the deletion that follows covers
it, and they check the `soli` pair. Each was confirmed to fail with the
corresponding piece of the mechanism disabled.
