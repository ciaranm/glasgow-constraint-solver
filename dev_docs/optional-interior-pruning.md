# Optional interior pruning

A propagator that removes interior values of a variable (values strictly
between its bounds) is doing work for nothing if no other propagator can ever
see the difference. Issue #901 measured the case that prompted this: on both
constant-array `Element` benchmarks, generalised arc consistency on the result
made 62% more effectful inferences on `qap` than bounds consistency, over a
bit-identical search tree, because the only thing looking at the result was a
bounds-consistent linear sum. Issue #902 is the general version: let each
propagator say which variables' holes affect it, let a constraint offer a
pruning of interior values as optional, and work out per model which optional
prunings anything could observe.

This document covers the three pieces, in `gcs/innards/propagators.hh`, and
the argument for why switching a pruning off loses nothing that matters.

## What holes affect: `Triggers::holes_affect_propagation`

A *hole* in a variable is a value removed from strictly between its bounds, and
holes in a variable **affect a propagator's propagation** if one could ever give
that propagator something new to infer. Precisely, for every variable a
propagator does not declare: from any domains, no number of such removals ever
gives it an inference it could not already have made.

The question is what the propagator concludes, not what it does on the way
there. One that walks a domain only to find its extremes is unaffected, and so
is a linear inequality, even though a bound it infers can snap past a hole: what
it infers depends only on bounds, so the inference is the same either way, and
the hole changed only the domain that inference was applied to.

This is almost exactly what the trigger kinds already say. `constraints.md`
asks for the coarsest trigger that suffices: `on_bounds` if the propagator only
inspects bounds, `on_change` if it iterates the domain. So the declaration is
derived from the triggers, unless the propagator overrides it:

| Registered as | Do holes affect it? |
|---|---|
| `on_change` | yes |
| `on_bounds`, `on_instantiated` | no |
| `scope_only` | yes (it arranges its own wakes, which could be on anything) |
| a `refined` watch on `x == v`, `x != v`, or a range | yes |
| a `refined` watch on `x >= v` or `x < v` | no |
| nothing | no |

`Triggers::holes_affect_propagation`, when set, replaces the derived list. It
exists for the places where the triggers do not tell the truth, which an audit
of every install site in `gcs/constraints/` and `gcs/presolvers/` found in two
directions.

**Sensitivity the triggers miss**, now declared explicitly:

- `Count` watches `how_many` for its bounds, but its value-of-interest support
  test asks whether each achievable count is in `how_many`'s domain.
- `SubCircuit`'s main propagator is woken only by instantiation under the
  default `Prevent` algorithm, but its lookahead's evidence-node test asks
  whether a node's own index is still in its successor's domain.
- `BinPacking` watches the loads for their bounds, but the upfront Stage 3
  sweep drops DAG terminals that fall into a hole in a load's domain.
- The refined learned-nogood store is installed with no triggers at all and
  arms every watch at run time; a nogood may hold `x == v`. It declares every
  variable it could learn over.

The first three are also wakes those propagators miss --- a hole appearing in
`how_many` does not wake `Count` --- which is a propagation question in its own
right, and not changed here.

**Sensitivity the triggers overstate** costs nothing but a pruning kept on that
could have been switched off, so those are left alone, with one exception: the
slack-watched linear inequality registers `scope_only` but only ever watches
bound literals, and declares an empty list, since long linear sums are exactly
what an element result tends to feed.

Getting the list wrong in the direction of too few variables never makes the
solver unsound. It can only switch a pruning off that the propagator could in
fact have seen, which loses propagation.

## Declaring an optional pruning: the pair

`Propagators::install_with_optional_interior_pruning()` installs two
implementations of the same propagation: `pruning`, which also removes interior
values of some `targets`, and `fallback`, which does not. Exactly one is live at
a time; until something chooses, it is `pruning`, so a pair propagates exactly
as `pruning` alone would.

A pair is one propagator id. Its slot holds whichever member is live, and the
other waits beside it; both members' trigger entries are registered under the
id, the one not live with its masks zeroed, and each sits exactly where that
member's own would have been had it been installed alone in the pair's place.
So a member that is live is woken, and runs, exactly as it would on its own ---
a pair that falls back propagates as its fallback installed alone would, counts
and all --- and the one that is not costs nothing. Each member also keeps its
own hole sensitivity and its own idempotence-aliasing verdict. For degree and
adjacency the pair counts once, over the union of the two scopes. Both members
must use coarse triggers only, since a refined watch is delivered to a
propagator id and could not say which member armed it.

That shape is measured, not decorative. Installed as two propagators, one
permanently disabled, a pair that falls back cost `qap` 1.7% and `tsp` 0.9%
over the fallback on its own, over identical propagation: 0.4% more
instructions, but 11% more L1 misses. Zeroing the disabled one's trigger masks
bought nothing measurable; a denser propagator id space is what the per-id
arrays wanted.

Declaring a pair makes two promises about the constraint as a whole, meaning
everything installed under its `ConstraintID`:

- **The two differ only in the targets' interiors.** `pruning` is at least as
  strong as `fallback`, and wherever `fallback` and the constraint's other
  propagators all have nothing left to do, `pruning` could remove nothing but
  interior values of the targets.
- **The constraint cannot see those values itself.** None of its other
  propagators --- `fallback` included, and any other pair it installs --- can
  tell whether the values `pruning` would remove are there. A fallback usually
  keeps this by being unaffected by holes in its targets at all, as `Element`'s
  range is (it watches the result only for its bounds). Any other propagator
  that they do affect keeps it by being an exact support test for the
  constraint: `pruning` removes only values the constraint has no support for,
  and a supporting tuple contains only supported values. Nothing checks this
  one; the analysis simply ignores a constraint's own sensitivity to its targets
  on the strength of it.

The second promise is load-bearing. `Element`'s index propagator is GAC in both
of its arms, and asks whether each live entry is in the result's domain, so a
hole in the result affects it; without the promise, every element's own index
propagator would keep its own pruning on, and the analysis would never fire on
`qap` or `tsp`. The promise is what lets the analysis ignore a constraint's own
sensitivity to its targets. Any other constraint's always counts.

### Element

`Element` takes `consistency::Auto`, under which it installs its result
propagators as a pair: the union of the live entries (GAC) as `pruning`, their
range (BC) as `fallback`. It only does so over an array of constants, because
only there are both promises kept:

- With constant entries the range is at a fixpoint only once its lower bound is
  the smallest live entry in range --- it re-runs after a bound it infers snaps
  past a hole, which is why it must never claim idempotence --- and a bound is
  always in the domain, so that entry is also the smallest value the union
  keeps. The union is also never weaker than the range, on any domain. With variable entries the range takes an
  entry's bounds and misses the holes in it, so result in `[1, 10]` against a
  live entry in `{0, 5, 10}` keeps 1 where the union gets 5, and that is a
  bound, which anything can see.
- The index propagators ask only whether the entry at a live index tuple is in
  the result's domain, which is never a value the union removes.

Index variables aliasing one another, as in `qap`'s `D[x_i][x_i]`, change
neither argument, since every propagator here treats the dimensions
independently. The result doubling as an index does, and keeps the plain GAC
arm. So does any array with a non-constant entry.

## The analysis: promotion to a least fixpoint

`Propagators::analyse_optional_interior_pruning()` answers, for every pair,
whether its pruning is needed:

1. Every live propagator outside a pair, and every pair's `fallback`, is a
   **source**: its hole sensitivity always counts.
2. A pair's pruning is **needed** once a hole in one of its targets would
   affect a constraint other than its own.
3. The needed pruning's own hole sensitivity then counts too, which can make
   another pair's pruning needed. Repeat until nothing changes.

This is promotion from "nothing is needed", so it finds the *least* fixpoint,
by a single worklist pass. Starting instead from "everything is needed" and
switching off whatever nothing is affected by finds the greatest fixpoint, and
differs in the cycles: two prunings that could each observe the other, and that
nothing else observes, stay on under demotion and off under promotion, and off
is right, since neither's work ever affects anything that matters.

Counting the fallback's sensitivity whichever of the pair is live keeps the
computation monotone. Permanently disabled propagators are affected by nothing,
and a pair whose propagator is disabled is left out. Each verdict names one
constraint responsible for a needed pruning (`observed_by`), which is what a
report of the decision should show.

## Why switching a pruning off loses nothing

Suppose every propagator's hole sensitivity is honest, every pair keeps its two
promises, and propagation reaches the same fixpoint whatever order it runs
things in, as it does for monotone propagators. Take the fixpoint the solver reaches
with every unneeded pruning switched off, and from it remove, for each
unneeded pair, the interior values its pruning would remove, repeating until
none would remove any more. By the first promise that never touches a bound or
a non-target. The only things that can see the removals are other unneeded
prunings, whose sensitivity the analysis did not count, and they react only by
removing more of their own targets' interiors, which the repetition already
does. Nothing else can: not a propagator of another constraint that runs
either way, including a needed pruning, since then the pair would have been
needed; not the pair's own constraint, by the second promise. So what is left
is a fixpoint of the system with every pruning on, and it agrees with the first
one everywhere but the unneeded targets' interiors.

That last assumption is an idealisation, and it is worth knowing where it
bends. `Element`'s range is not monotone on its own: shrink the index domain
until no live entry is in range and it stops inferring anything. It is only in
combination with the index propagators, which wipe out in exactly that case,
that the fixpoint is order-independent. And a propagator that misses wakes ---
the three under-triggered ones above, say --- makes fixpoints depend on order
in general, whether or not anything here is switched off.

So **every variable's bounds are the same at every fixpoint** either way.
Anything that only ever reads bounds sees no difference at all: in particular a
search whose brancher only looks at bounds (`in_order` with `smallest_in`, say)
explores an identical tree. This is the property to test, and it is a stronger
test than soundness, which a wrong switch-off could never break: both arms are
sound, so a solver that switches off too much is merely weaker.

## What the analysis deliberately ignores

Only propagators are consulted.

- **The branching heuristic** is not a consumer. A heuristic that sees a larger
  domain chooses differently, so the tree can change when the brancher ranges
  over an affected variable --- `dom`-family counts differ, enumerating value
  orders (`smallest_first`, the default, and `random`) visit values the pruning
  would have removed, each an immediately failing child, split points move, and
  hole-punching orders (`random_out`, `median`, `reject_random_interval`) make
  holes nothing propagates --- but never which solutions exist. The search
  only reports a solution once every variable is fixed, and bounds agree at
  every fixpoint, so anything that would have been fixed still is.
- **The objective** is only ever bounded (`obj < best`) or read once fixed.
- **Solution callbacks** only see fixed values. The `trace` callback sees open
  domains, but only watches.

## Proofs and the OPB

The two halves of a pair are two propagators for one constraint, whose
encoding is written once, when the constraint is installed and before either
is chosen, so the choice cannot change the OPB. `Element`'s `with_consistency`
already promised the same of `GAC` and `BC`. The proof can change, since which
inferences get made changes.

## Where the choice is made

Nothing chooses yet: a pair keeps its pruning on, and `consistency::Auto`
propagates as `GAC`. The analysis can be run directly on a `Propagators`, as
`gcs/innards/optional_interior_pruning_test.cc` does for the `qap` and `tsp`
shapes.

## Known conservatism

- **Learned nogoods.** With restarts on, the learned-nogood store declares that
  holes in every variable affect it, so every pruning is kept. That is right in
  general: a nogood holds the negation of each decision on a path, so any
  brancher that can decide `x != v` --- `smallest_in`'s right branch does ---
  can put `x == v` in a nogood, and a hole falsifies that. Only a brancher
  whose decisions are all `x == v` or bounds would allow less, and the store
  cannot know which brancher it is learning from.
- **Overstated sensitivity** keeps prunings on that could go off.
