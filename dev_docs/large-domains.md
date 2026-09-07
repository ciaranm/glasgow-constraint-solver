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

### A trap: a bound that is obvious is not necessarily RUP

`ArrayMinMax` has no hull bound on the loose side — for a max it posts
`result >= lb(var_i)` for every i but never `result <= max_i ub(var_i)`, so the
per-value union sweep is what establishes it (issue #815, which proposes adding
the bound as a small, obviously-correct first fix).

It is obviously correct, and it is **not a small fix**, because it does not
verify. Negating it gives `result > max_i ub(var_i)`; each selector asserts
`result <= var_i`, so every selector must be false and the al1 row fails. That
argument needs to carry an order atom on `result` across the half-reified row
relating `result` and `var_i`, which is a linear row over the *bits* — and unit
propagation does not cross a bit sum on a wide domain, where nothing fixes an
individual bit. Adding the bound with `JustifyUsingRUP` fails VeriPB on
`min_max_constraint` and `min_max_constraint_view_mixed`. Making it verify needs
an explicit `pol` per selector, over line numbers `define_proof_model` does not
currently keep.

The interval rewrite of the union sweep is the better target anyway: it fixes the
general case rather than only the narrow-array one, and the range-removal proof
pattern it needs already exists and verifies fifty lines further down the same
file (`min_max.cc:199`, `infer_not_in_range` with a value-independent
justification emitted once per interval).

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
| `HazardNotReached` | the source has a per-value site, but this probe does not reach it. **Not** a clean bill of health: a gap in the probe. No row uses this today — every gap has been closed — but the outcome stays, because it is what to reach for rather than guessing when a probe cannot get at a site |

### Where we stand

68 probes, run on `7d014207`.

| | constraints |
|---|---|
| **KnownTrip** (24) | `Power`, `PowerTable`, `AllDifferent`, `AllDifferentExcept`, `AllEqual/holes`, `Among`, `Count`, `NValue`, `AtMostOne`, `AtMostOneSmartTable`, `GlobalCardinality`, `In`, `ArrayMinMax`, `Element`, `LexSmartTable`, `Table`, `SmartTable`, `Regular`, `RegularLegacy`, `RegularBacchus`, `MDD`, `Cumulative`, `Disjunctive`, `Knapsack` |
| **Clean** (30) | the arithmetic family, comparison, equality, linear, `AllDifferent` under `VC`, `Element` under `BC`, `AllEqual` without holes, `ValuePrecede`, `SeqPrecedeChain`, `IncreasingChain`, `Lex`, `Sort`, `ArgSort`, `NegativeTable`, `Disjunctive2D`, `BinPacking`, `MinDistance`, `DifferenceConstraints`, `Nogoods` |
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

### What the sharpening pass found

Six probes originally passed without touching the site they were meant to test.
Chasing each one down split them three ways, and the split is the useful part:
"survives" meant three different things.

**Three were real hazards behind a condition the probe did not meet.** Each is
now a `KnownTrip`:

* `GlobalCardinality` needs the *just-met-demand* branch
  (`bounds_global_cardinality.cc:127`), where the number of variables that can
  take a cover value equals that value's count lower bound, so each is forced to
  it by removing every other value one at a time. Three variables, one cover
  value, a count pinned at three.
* `Element` needs the array entries to be **narrow**. The GAC sweep erases each
  entry's domain from the result's still-unsupported set, so a *wide* entry
  erases everything in one `erase_range` and leaves no remainder — the original
  probe made the hazard disappear by being too wide.
* `AllEqual` needs holes *and* a large difference. Bounds propagation runs first
  (`all_equal.cc:95`) and collapses a merely narrow partner, so the hole has to
  be spread across the full width: a two-value domain at the extremes leaves the
  whole middle of the other variable to be removed one value at a time.

**Three were not hazards at all**, and the entry in #833's source list was about
a sibling rather than the constraint itself. Each is now `Clean`:

* `NegativeTable` is watched-literal over tuples and never iterates a domain, so
  it takes none of the residue path the positive `Table` dies in.
* `Disjunctive2D` is pairwise, with no value loop and no span-indexed array, and
  installs no 1D `Disjunctive` child that would have one.
* `MinDistance`'s per-value loops are all over its *position* variables, and
  `prepare()` `define_bound()`s those to `0..n-1` of the distance matrix
  (`min_distance.cc:92-93`), so they cannot be wide. Its wide position is the
  objective, which it reasons about by bounds.

The moral for anyone adding a row: **a probe that survives has proved nothing
until you have checked it reached the code you meant to test.** Two of the three
real hazards above were hidden by the probe being *more* extreme than necessary,
which is not the direction one expects to have to correct.

One deliberate non-axis: the lane runs **without proof logging**. `NValue`'s
H2′ is caught anyway, because its per-value work is in `prepare()`, but a
constraint whose *encoding* alone were per-value would not be. That is by
design — see below.

## Proofs

**Out of scope for fixing.** Several of these have no viable fix today, and a
propagator is never weakened for proof size ([propagator-performance.md](propagator-performance.md)).
The reason to measure it anyway is that the bad cases are *evidence*: where an
inference's justification emits one near-identical step per value — the same
derivation with a different constant substituted in — a VeriPB feature that
could express the whole family in one step would take an O(n) or better bite out
of it. This survey is where candidates for such a feature come from.

```shell
# from a build with the guard OFF, so the probes are not stopped before they write
./build/large_domain_audit_test "[.proofscaling]"
```

It runs every probe at widths 10^3 and 10^4 and reports OPB rows and proof steps
separately, because they mean different things:

* **OPB rows growing with the width** is an encoding that is per-value. That is a
  modelling problem, and no checker feature helps.
* **Proof steps growing at a *fixed* encoding** is the copy-paste, and is what a
  checker feature could collapse.

### Results at 10^3 → 10^4

| | growth (opb / steps) | constraints |
|---|---|---|
| **Both** grow | 10x / 10x | `Power`, `PowerTable`, `NValue`, `Regular`, `RegularLegacy`, `RegularBacchus`, `MDD` |
| **OPB only** | 10x / 1.0x | `Cumulative` (19046 → 190046 rows; one capacity line per time point, so it is H3 on the encoding side) |
| **Steps only** | 1.0x / 10x | **`Among`** (42-row OPB fixed, 32996 → 329996 steps) and **`Table`** (47-row OPB fixed, 50788 → 509788 steps) |
| neither | 1.0x / 1.0x | everything else, 59 of 67 |

**`Among` and `Table` are the two clean candidates.** Their encodings do not grow
at all, so every one of those extra steps is the *same* derivation with a
different value in it:

* `Table` is the purest. `extensional_utils.cc`'s support scan calls
  `inference.infer(logger, vars[idx] != val, JustifyUsingRUP{hint}, table.reason)`
  once per unsupported value — the same reason, the same hint, one RUP step each,
  differing only in `val`. A rule that could discharge "these removals, for every
  value in this interval, by this one derivation" would replace the lot.
* `Among` emits, per removed value, one line per value-of-interest
  (`among.cc`) — the same clause shape with one constant substituted, nested one
  level deeper.

Both are also H1a in the propagation column, so the interval-level rewrite would
remove much of the proof volume as a side effect: an interval removal is one
inference where a run of values was many. That does not make a checker feature
redundant — the rewrite only applies where the removed set *is* an interval — but
it does mean these two rows should be re-measured afterwards rather than quoted
as a standing figure.

### The bad encoding cases

Eight constraints write an OPB whose size grows with the domain. They are not
all the same shape, and the difference decides whether a checker feature is the
only way out. All five are filed and parked under tracker **#846**; nothing here
is scheduled before the propagation work in #833.

| issue | constraint | rows | what varies per row | re-encodable without checker help? |
|---|---|---|---|---|
| #841 | `Regular`, `RegularLegacy`, `RegularBacchus` | O(layers × states × D) | a value with **no transition** at that state | **yes**, see below |
| #842 | `MDD` | O(layers × nodes × D) | same | **yes**, same fix |
| #843 | `NValue` | O(D) | a value of the union of the domains | only by changing encoding family |
| ~~#844~~ | `Cumulative` | O(tasks × horizon) | a time point | **already fixed by #781**, opt-in |
| #845 | `Power`, `PowerTable` | O(D) | a row of an enumerated relation | no — it *is* a table |

**`Regular` and `MDD` are the easy ones, and the fix needs no checker feature.**
Both deliberately widen their OPB alphabet to the union of the transition keys
*and every value of every variable's initial domain*
(`regular.cc:581-584`, `mdd.cc:465-471`), purely so that a value with no
transition gets an explicit `(x_i ≠ val) ∨ ¬(state_i = q)` row — the comment says
it is "what veripb needs to verify the propagator's RUP-justified pruning of
those values". But a value outside the transition keys entirely has no transition
at *any* state, so the honest statement about it is not one row per state, it is
`x_i ∈ alphabet`. The complement of a k-element key set inside a domain is at most
k+1 intervals, so that is O(|alphabet|) range rows instead of O(states × D), with
no dependence on the width at all. The measured 18042 → 180042 rows for a
*two-state, one-symbol* automaton is all no-transition rows.

What needs checking before believing that: whether the propagator's RUP pruning
of an out-of-alphabet value still goes through against range rows. A range row
asserts order atoms, and getting from there to `x_i ≠ val` is the same step
`justify_not_in_range_across_equality()` exists for — so there is precedent, but
it is exactly the sort of thing that has to be run past VeriPB rather than
argued.

#### Two thirds of that OPB is not the constraint

Worth breaking down, because it is not where you would guess. `regular` over
three variables of `0..100`, a two-state one-symbol automaton, 1841 rows:

| rows | what |
|---|---|
| 612 | `@i[x][geN][r]` / `[f]` — **order-atom definitions** against the bit encoding, two per atom |
| 606 | `@i[x][eqN][r]` / `[f]` — **equality-atom definitions**, two per atom, built from the order atoms |
| 600 | the constraint's own `(x_i ≠ val) ∨ ¬(state_i = q)` rows |
| 23 | everything else |

So only a third of the per-value cost is `Regular`'s own rows. The other two
thirds is the **variable's direct encoding**, written out one value at a time
*because the constraint names those atoms* — atoms are emitted on reference, not
wholesale (`always_use_full_encoding` is off by default; see
[variable-encodings.md](variable-encodings.md)). The `geN` rows also carry one
term per bit, so the character count is O(states × D × log D).

Two consequences:

* The `Regular`/`MDD` re-encoding is worth about **3x more** than the
  constraint-row count suggests, because not naming those atoms stops their
  definitions being emitted at all.
* A parameterised-family feature has to be able to introduce **atom
  definitions**, not merely constraint rows. On this instance a feature that
  collapsed only the 600 constraint rows would leave 1218 behind and change the
  asymptotics not at all. That is a sharper requirement than "a family of
  constraints", and it is the one this measurement actually supports.

**`NValue` is fixable, and the ugliness is not where I first assumed.** The
value-indexed encoding is a fully-reified flag per value of the union
(`n_value.cc:60-77`), `flag_v ⇔ ∃i. x_i = v`, and `n = Σ_v flag_v`. The
position-indexed alternative is `n = Σ_i f_i` with `f_i ⇔ ∀j<i. x_i ≠ x_j` —
"x_i is the first occurrence of its value" — which is O(n²) rows and completely
independent of the domain.

The obvious objection is that all the propagator's justifications would need
rewriting against the new flags. **That objection is wrong**: `NValue`'s
propagator emits no explicit steps at all, just two `JustifyUsingRUP` inferences
(`n_value.cc:104` and `:116`). The real costs are different, and worse:

1. `n_values ≤ |possible values|` is RUP under the value-indexed encoding almost
   by construction — at most that many flags can be true. Under the
   position-indexed one it is a counting argument over the `f_i`, and very likely
   **not** RUP, so a currently-free inference would need a real justification.
2. It abandons cake_pb_cp's nvalue encoding, which `n_value.cc:61` says it
   conforms to deliberately (#354), so the workflow-2 chain breaks for nvalue.
3. O(n²) is worse than O(D) whenever the domain is narrower than the scope, so
   the honest version picks between the two — which means two encodings and two
   sets of justifications to maintain.

The same breakdown for the other two measured cases, three variables at
`0..100`, which is what the tracker's feature argument rests on:

| constraint | total rows | variable `geN`/`eqN` atom definitions | its own rows |
|---|---|---|---|
| `Regular` | 1841 | 1218 (66%) | 600 |
| `NValue` | 1431 | 1218 (85%) | 213 |
| `Cumulative` | 1945 | **0** | 1836 |

`Cumulative` is the instructive exception: it names no equality atoms at all,
because its flags are defined against order comparisons over the bits
(`starts[i] <= t`), so every one of its 1836 rows is its own reified flag
halves. So the family construct needs to introduce *two* kinds of definition —
eq/ge atoms for `Regular` and `NValue`, reified flag halves for `Cumulative` —
not one.

**`Cumulative` already has its fix, and it is the useful counterexample.** The
figures above are the `TimeIndexed` encoding, which is still the default: three
fully-reified flags and a load line per (task, time point). PR #781 (for #780)
replaces it with a horizon-free start-checkpoint encoding, and on the same
instance that is 1945 → **46** rows at `0..100` and 190045 → **46** at
`0..10000`, flat in the horizon. It is opt-in behind
`GCS_CUMULATIVE_ENCODING=start-checkpoint`; #781 says the default is deliberate
pending a measurement over #777.

This is worth remembering when arguing that a shape needs checker support. Before
#781, `Cumulative` looked like the case with no way out — time-indexing was "what
the encoding is". It was not: a change of formulation plus minting the
per-(task, time) flags inside the proof rather than in the model removed the
dependence entirely. Re-encoding may be available more often than it looks.

`PowerTable` genuinely *is* a table; its rows are the relation.

### What a parameterised-family feature would buy

Four of the eight — `NValue`, `Cumulative`, and `Regular`/`MDD` if they are left
as they are — share one shape: **the same row schema with a single parameter
ranging over a contiguous interval**. `flag_v ⇔ ∃i. x_i = v` for every v in
[lo,hi]; `active_{i,t} ⇔ before ∧ after` for every t in a window; `(x_i ≠ val) ∨
¬(state_i = q)` for every val in a gap. If a family like that could be *declared*
once and instantiated by the checker on demand, all four collapse, and the two
step-level cases from the previous section (`Among`, `Table`) collapse with them
— they are the same construct applied to derivation steps rather than axioms.

The `Regular` breakdown above says the feature has to reach one level further
down than that, though: the majority of the rows in every one of these cases are
the **eq/ge atom definitions of the variables the family mentions**, which are
themselves a family over the same parameter. A construct that covers the
constraint rows but not the atoms they name would leave two thirds of the OPB
untouched.

That is a stronger case for the feature than the step-level cases alone make,
because `Cumulative` and `NValue` have no other way out: for them it is the
feature or the O(n²) re-encoding with its own costs, and there is no third
option.

## See also

- [constraints.md](constraints.md) — the constraint-authoring pattern; "Querying
  state" is where the per-value APIs this document is about are introduced.
- [propagator-performance.md](propagator-performance.md) — the strength-versus-
  performance ground rules a fallback arm has to respect.
- [state-and-variables.md](state-and-variables.md) — `IntervalSet`, and why a
  wide domain is cheap to *store* and expensive only to *walk*.
