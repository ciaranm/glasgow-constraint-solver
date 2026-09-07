# Large domains

Nothing in the solver bounds the work a constraint does as a function of how
*wide* a variable's domain is. A propagator that reasons value by value over a
billion-value domain does a billion units of work per call; an initialiser that
precomputes per value allocates per value; a scheduling propagator that indexes
by time allocates over the whole horizon. None of that is a bug in any one
constraint. It is a missing policy, and this document is where the policy and
the machinery for finding violations of it live.

The tracking issue is [#833](https://github.com/ciaranm/glasgow-constraint-solver/issues/833).

## The rule

> **Every bounds-consistency path must be independent of domain width.**

This is the backstop the rest of the policy hangs off. A model may legitimately
declare `var 0..1000000000`, and `fzn-glasgow` gives a domainless FlatZinc `var
int` a domain of about 9.2×10^18 values, so a wide domain is an ordinary input
rather than a mistake to be refused. What makes that safe is not a check that
rejects it, but every constraint having somewhere cheap to fall back to. A
constraint may drop to propagating almost nothing over a wide domain — that is
allowed, and it should say so on the stats channel — but it must stay correct
and it must stay cheap.

Two corollaries that are easy to get wrong:

* **"Fall back to bounds" is not the same as "pick the BC arm."** A bounds arm
  that enumerates values is not a fallback at all. `GlobalCardinality` already
  defaults to `consistency::BC{}` and still enumerates
  (`bounds_global_cardinality.cc`), which is the canonical counterexample.
* **Weakening for cost is legitimate; weakening for proof size is not.** See
  `propagator-performance.md` — a fallback arm is justified by time and memory,
  never by the proof being too big.

## The hazards

| | hazard | where it bites |
|---|---|---|
| **H1a** | a per-value spelling of an interval operation | fixable at full strength — see below |
| **H1b** | a missing bounds inference, so a per-value loop is what establishes the bound | a propagator bug |
| **H1c** | a genuine per-value support scan with no interval structure to exploit | needs a weaker arm |
| **H2** | install-time precompute proportional to the sum of domain sizes, before search exists | needs the decision taken in `prepare()` |
| **H2′** | an OPB *encoding* proportional to a domain | no consistency level helps; `NValue` writes one proof flag per value of the union of the domains |
| **H3** | arrays sized by a span, which no consistency level covers | a cap and a weaker rung |

H1a is the one worth looking for first, because it is not a trade-off at all.
The tree already has the machinery: `IntervalSet::each_interval_minus()`,
`InferenceTracker::infer_not_in_range()`, and
`justify_not_in_range_across_equality()` for the proof side, used in
`equals.cc`, `in.cc`, `min_max.cc` and `global_cardinality.cc` today. A loop
that removes "everything not in this small given set" one value at a time is an
interval operation written out longhand, and rewriting it keeps GAC.

H3 has two precedents in the tree for what a good cap looks like:
`ExtensionalDomainBitmaps::max_words` and `cumulative.cc`'s
`max_knapsack_capacity`. Both are far above anything a real model asks for, both
degrade to a named weaker rung rather than silently doing less, and the comment
on the second is the model for how to write one up.

## The guard

`-DGCS_LARGE_DOMAIN_GUARD=ON` turns work proportional to a domain's width into a
`LargeDomainGuardTripped`. It is **off by default and is not a user-facing
safety net**: what protects a user is a constraint having somewhere to fall back
to, not an exception thrown from the middle of propagation. The guard is a
development tripwire, so that a wedged core or a `bad_alloc` deep inside
propagation becomes an attributable test failure.

```shell
cmake -S . -B build-guard -DGCS_LARGE_DOMAIN_GUARD=ON
cmake --build build-guard --parallel $(nproc)
./build-guard/large_domain_audit_test
```

Two kinds of check, and the difference matters:

* **`LargeDomainIterationCounter`** counts values *as an iteration hands them
  out*, in `State::each_value_*` and `State::for_each_value_*`. Counting work
  done is the right measure and checking the domain's width up front is not: a
  branching heuristic asks for a generator over a billion-value domain and reads
  one value from it, which is fine. An early version of this guard checked the
  width and condemned `Plus`, `Abs`, `LessThan` and `LinearEquality` for it.
* **`GCS_CHECK_LARGE_DOMAIN`** checks a size up front, for the H3 sites that
  commit to a whole array at once.

The limit is 100000, overridable with `GCS_LARGE_DOMAIN_GUARD_LIMIT`. It sits in
the gap #833 measured between "free" (10^4) and "hundreds of megabytes" (10^6),
and far above anything the test suite asks for. It is deliberately *not* the
threshold the policy itself will use to choose an arm: a guard wants to be far
enough above normal work never to fire on it, and a policy wants to be near the
cliff.

With the guard off, every check compiles to nothing — not merely to a no-op call,
but to nothing that evaluates the size being checked.

## The audit lane

`gcs/large_domain_audit_test.cc` posts every constraint class once over a
`0..10^9` domain, installs it, propagates at the root and nowhere else. It is
built always (so it cannot rot) but registered as a ctest case only when the
guard is on, since without the guard every probe passes trivially.

Each row pins the outcome we currently expect, so the lane is green today and
each piece of #833 flips rows rather than introducing failures. **A row that
stops tripping is a failure too** — that is good news which needs the table
updated, and pinning both directions is what stops the table drifting away from
what the code does.

The four outcomes say different things, and the difference between the last two
is the part worth reading carefully:

| outcome | meaning |
|---|---|
| `Clean` | has a position where a wide domain is meaningful, and survives one |
| `KnownTrip` | likewise, and does not. This is the work #833 is about |
| `NoWidePosition` | no variable it takes can meaningfully be wide — successors index an array, Booleans are `{0,1}`. Structural immunity, not a working fallback |
| `HazardNotReached` | the source has a per-value site, but this probe does not reach it. **Not** a clean bill of health: a gap in the probe, tracked below |

### Where we stand

67 probes, run on `7d014207`. The trips:

| | constraints |
|---|---|
| **KnownTrip** (21) | `Power`, `PowerTable`, `AllDifferent`, `AllDifferentExcept`, `Among`, `Count`, `NValue`, `AtMostOne`, `AtMostOneSmartTable`, `In`, `ArrayMinMax`, `LexSmartTable`, `Table`, `SmartTable`, `Regular`, `RegularLegacy`, `RegularBacchus`, `MDD`, `Cumulative`, `Disjunctive`, `Knapsack` |
| **HazardNotReached** (5) | `GlobalCardinality`, `Element`, `NegativeTable`, `Disjunctive2D`, `MinDistance` |
| **Clean** (27) | the arithmetic family, comparison, equality, linear, `AllDifferent` under `VC`, `Element` under `BC`, `AllEqual`, `ValuePrecede`, `SeqPrecedeChain`, `IncreasingChain`, `Lex`, `Sort`, `ArgSort`, `BinPacking`, `DifferenceConstraints`, `Nogoods` |
| **NoWidePosition** (14) | the graph and permutation family, and the Boolean constraints |

Three things in that table were not what #833 predicted, and are worth
recording because they change what the later stages have to do:

1. **`AllDifferent` under `consistency::VC{}` is clean.** The designated
   fallback really is width-independent, so the `AllDifferent` fix is a policy
   decision rather than new propagator work. The same holds for `Element` under
   `BC`.
2. **`Power` trips**, which #833 did not list — it reaches `PowerTable`'s
   product enumeration. So does `LexSmartTable`.
3. **`Among`'s trip is conditional.** Its per-value branch only runs with the
   count pinned; with slack in the count the propagator concludes nothing and
   the probe passes without touching the hazard. A probe that does not reach a
   path proves nothing about it, which is what `HazardNotReached` exists to say.

### Known gaps in the lane

Each of these is a probe that needs sharpening rather than a constraint that is
known good:

* `GlobalCardinality` — `propagate_bounds_global_cardinality` enumerates values,
  but not on a probe of this shape.
* `Element` — the per-value support remainder is not reached from a narrow index
  at the root.
* `NegativeTable` — does not take the residue path the positive table dies in.
* `Disjunctive2D` — the time-table pass is not reached at the root.
* `MinDistance` — its per-value sites need more sites than this probe has.
* `AllEqual` — the probe has no holes, so `all_equal.cc`'s hole path never runs.
* The lane runs without proof logging. H2′ (`NValue`) is caught anyway, because
  the per-value work is in `prepare()`, but a constraint whose *encoding* alone
  is per-value would not be. A proofs axis is the obvious next addition.

## See also

- [constraints.md](constraints.md) — the constraint-authoring pattern; "Querying
  state" is where the per-value APIs this document is about are introduced.
- [propagator-performance.md](propagator-performance.md) — the strength-versus-
  performance ground rules a fallback arm has to respect.
- [state-and-variables.md](state-and-variables.md) — `IntervalSet`, and why a
  wide domain is cheap to *store* and expensive only to *walk*.
