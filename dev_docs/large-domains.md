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

**First, check whether the loop already stops early.** A `for` over a domain is
not automatically a hazard: what matters is how many values it takes before it
can answer. `Among`'s variable partition asks "is every value of this domain one
of the values of interest", walking the domain — but as a `none_of`, so it stops
at the first value that is not, and among any `|voi| + 1` values at most `|voi|`
can be of interest. It is bounded by the value set, not the domain, and rewriting
it as a counting query over `in_domain` made it **9% slower** on a search that
calls it hundreds of thousands of times, for no width benefit at all. Ten lines
below it the *same* predicate was written as a plain loop with no early exit, and
that one really did walk a billion values; the fix there was the missing exit, not
a new algorithm.

Neither the audit lane nor the test suite can tell these two apart — both are
`each_value_immutable` over a wide domain, and only one trips the guard. So read
the loop for its exit condition before reaching for an interval rewrite, and put
any rewrite of a hot query through a before/after benchmark.

**The cheapest H1a of all is where the conclusions are already intervals and only
the search for them is per-value.** `In`'s constant-set filter emitted one
`infer_not_in_range` per maximal run of forbidden values, and found those runs by
walking the domain and grouping consecutive ones. A merge against the permitted
set yields the same runs — a run breaks exactly where the domain has a hole or a
permitted value intervenes, which is where `each_interval_minus` ends one too — so
the rewrite changes nothing at all in the proof. Verified rather than argued: at a
fixed seed the OPB, the proof, and the test output are byte-identical before and
after, and a differential check computing both algorithms in one binary reports
zero disagreements over ten seeds. Look for this shape first; it is free.

H1a is the one worth looking for first, because it is not a trade-off at all.
The tree already has the machinery: `IntervalSet::each_interval_minus()`,
`InferenceTracker::infer_not_in_range()`, and
`justify_not_in_range_across_equality()` for the proof side, used in
`equals.cc`, `in.cc`, `min_max.cc` and `global_cardinality.cc` today. A loop
that removes "everything not in this small given set" one value at a time is an
interval operation written out longhand, and rewriting it keeps GAC.

### Getting a range removal past the checker

Replacing a per-value removal with a range one is not free in the proof, and the
reason it is not is worth understanding once, because it decides which
interval rewrites are cheap.

The conclusion side is fine. Negating `result NOT IN [lo, hi]` gives two opposing
bounds on `result`, and those *do* contradict through the bit rows — that is the
configuration `justify_not_in_range_across_equality()` already relies on, and it
holds even for a signed 63-bit variable.

**The blocker is the reason side.** A reason literal `var NOT IN [lo, hi]` is the
*disjunction* `~ge_lo(var) OR ge_{hi+1}(var)`, and RUP cannot case split. Unit
propagation can *refute* "result >= lo and var <= lo-1 and f_i", but it cannot
*derive* "var >= lo" from "result >= lo and f_i". The per-value form never meets
this, because `result = val` pins every bit of `result`, which pins every bit of
`var` through the linear row, deciding both halves of the disjunction at once. A
range pins no bit, so both halves stay open.

The fix is to restate each refutation as a clause the checker can propagate — the
two ge-layer bound lemmas — and only then draw the conclusion. For `ArrayMinMax`
that is, per variable `i`:

```
rup  ~f_i \/ ~ge_lo(result) \/ ge_lo(var_i)             [crosses the half-reified row]
rup  ~ge_{hi+1}(var_i) \/ ge_{hi+1}(result)             [crosses the unconditional row]
rup  ~f_i \/ ~in(result,lo,hi) \/ in(var_i,lo,hi)
```

then RUP the conclusion. **3n+1 lines per interval, independent of the range
width**, which is the property that matters: the point of the rewrite is to
replace 9.2x10^18 steps with a constant number, so a procedure linear in `hi-lo`
would be worthless.

Which of the two lemmas carries the selector depends on which row it crosses. For
`max` the model has `result >= var_i` unconditionally and `result <= var_i` under
`f_i`, so the *lower* lemma needs the selector; for `min` it is the upper one.
This is `justify_not_in_range_across_equality()` generalised from an
unconditional equality to one that holds only under a guard.

Views keep the per-value path: a view's atoms are spelled through the view and
the lemmas have not been shown to bridge that. Same restriction, and same reason,
as the single-support range path in the same file.

**Two things that make an interval rewrite pay, learned on `AllEqual`.**

*Keep the per-value spelling for a width-1 interval.* A range literal of one value
*is* the eq atom — the proof machinery never makes an interval of one — so saying
it as `infer_not_equal` is the identical inference, and finding its reason costs
no set construction. Over holey domains most removed intervals are single values,
and routing them through the interval path instead cost 2% on a search.

*Do not pay for machinery the common case does not need.* Where the reason names a
witness that can vary within an interval, the general answer is to split the
interval by which variable accounts for which part. But almost always one variable
explains the whole of it, and a scan for a single covering witness is a few
allocation-free merge-walks, where building a leftover set to subtract from costs
an allocation whatever happens. Check for the easy case first and only then split.

Together these take a rewrite that was 2.5% slower on holey-domain search back to
level, while keeping the wide case (200 ms of work, and 131 seconds in the audit
probe) at nothing.

**Where the equality is guarded by a conjunction, the same lemmas take a longer
guard.** `Element`'s model is `result - array[i] == 0` half-reified on the
conjunction of index conditions, so it is `ArrayMinMax`'s shape with the selector
replaced by a tuple of index atoms. Per removed range and per feasible index
tuple, with `G` standing for the negated guard (the disjunction of
`index_d != x_d` over the dimensions):

```
rup  G \/ result < lo      \/ array[i] >= lo
rup  G \/ result >= hi + 1 \/ array[i] < hi + 1
rup  G \/ ~in(result, lo, hi)
```

Both lemmas need the guard here, where `ArrayMinMax` needs it on only one of the
two, because there the model has one direction unconditionally and here neither
holds outside the guard. Each is RUP for the same reason: its negation supplies
opposing bounds across an equality. With both in the database, the entry's own
`~in(array[i], lo, hi)` from the reason is a clause whose every literal is now
falsified, so the third line is propagation and the tuple walk then finishes as
it did per value.

**Two lemmas per tuple, independent of the range width.** A disjunctive reason
literal is fine in this direction, which is worth being precise about: the trap is
needing to *derive* a bound from `var NOT IN [lo, hi]`, and unit propagation cannot
case split. *Refuting* it is ordinary propagation once both of its literals are
falsified, which is exactly what the two lemmas arrange.

Checked by negative control rather than assumed: with the two lemmas suppressed
and everything else unchanged, VeriPB rejects the tuple line.

A constant-entry array needs no lemmas — the model row pins every bit of `result`
to the constant, so there is no crossing — and that branch is now covered by
`element_test`'s `constgac` mode. It had no coverage at all before, because
`ElementConstantArray` is bounds-only by default, so nothing in the suite ran the
GAC propagator's constant instantiation.

**Where the conclusion needs a counting argument, only the case split changes.**
`Among` is the third shape, and it is much cheaper than `ArrayMinMax`'s. Its
conclusion does not follow from one row: it needs `pol` over the encoding's
`sum >= how_many` half plus an at-most-one line per other variable, which is what
shows that a variable stepping outside the value set leaves the count short. That
argument does not mention the removed value at all, so it is *unchanged* by the
rewrite. What changes is only the step before it, which zeroes the `[var = voi]`
terms. Per value that was, for each value of interest,

```
rup  var != val \/ var != voi
```

and per range it is, for each value of interest,

```
rup  var < lo      \/ var != voi      [when voi < lo]
rup  var >= hi + 1 \/ var != voi      [when voi > hi]
```

Every value of interest sits wholly on one side of the range — the ranges removed
are the gaps between them — so which of the two applies is decided when the line
is written, and unit propagation then reaches the negated eq atom along the
ge-atom chain links. The per-value form needed no such choice because `var = val`
pins every bit of `var`; a range pins none, so the side has to be picked
explicitly rather than left to the checker.

The count goes from `|voi|` lines per removed *value* to `|voi|` per removed
*range*, and there are at most `|voi| + 1` of those however wide the domain is.
Measured: `Among`'s survey row falls from 32996 → 329996 steps across a 10x width
to a flat 98.

**And unlike `ArrayMinMax`, this one bridges views**, so `Among` needs no
plain-variable restriction: 259 range removals on view variables under proofs,
all verified. The difference is that every atom in these lines is on the *same*
variable — its order atoms against its own eq atoms — and `need_gevar` pol-derives
a view's chain links from the underlying variable's. `ArrayMinMax`'s lemmas have
to carry an atom on `result` across a row to an atom on `var_i`, and it is the
crossing, not the range, that views break. So "does this constraint's range
justification stay within one variable" is the question to ask before restricting
a rewrite to `SimpleIntegerVariableID`.

**The related trap.** The *hull bound* `result <= max_i ub(var_i)`, which #815
proposes as a small first fix, is a different problem and is still open. There the
selector has to be *derived* rather than assumed — the RUP negation does not hand
you `f_i` — so the lemmas above do not apply and it needs `pol` over OPB line
numbers `define_proof_model` does not keep. The interval rewrite above makes it
unnecessary for the case that motivated it.

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

  `State`'s iterators are not the only way a propagator walks a domain. It can
  build an `IntervalSet` of its own and walk that, or take an interval and expand
  it with a plain `for (Integer v = lo; v <= hi; ++v)`. `State` sees neither, so
  each such loop needs its own counter declared at the loop. Three sites carry
  one: `element.cc`'s sweep over unsupported result values (now only on its
  per-value view path), `all_equal.cc`'s expansion of the intersection
  difference, and `equals.cc`'s no-overlap reason. The counter does not belong in
  `IntervalSet::each()` itself, which is a general container used for deliberate
  enumeration — tabulation, and the tests.

  The first two were found the same way, and it is worth naming the smell: **a
  row that starts passing when you did not fix it.** Neither site allocated a
  suspicious amount or crashed; each simply ran for a minute or two and finished,
  so the row came out `Clean` on a machine with 16 GB free and `KnownTrip` on a
  smaller one. If a probe stops tripping, measure what it costs before believing
  it.

  The third was not found by the lane at all, and is the more uncomfortable case
  (#864, from the `equals` family audit in #863). It is not a pruning loop but a
  **reason**: one literal per value, assembled on the propagation path and then
  discarded unread whenever the tracker does not materialise reasons. Two things
  hid it. Its `ReifiedEquals` probe had *both* operands over the same wide
  interval, so they always intersected and the rule never fired — the probe being
  more extreme than necessary, exactly what the sharpening pass corrected
  elsewhere. And once the probe was fixed to disjoint operands, it still reported
  `Clean`: 160 s and 78 GB on a machine with 2 TB, where the same shape had died
  with `bad_alloc` at 2.6 GB for the person who reported it.

  Both halves generalise. **The lane's `bad_alloc` fallback is a property of the
  machine, not of the code** — on a large-memory node it will not fire, so a
  `Clean` row that nothing instruments is only as strong as the box it ran on.
  And a reason is a place to look that a search for pruning loops will not reach:
  guard the assembly on `InferenceTrackerBase::want_reasons()` first, then count
  the walk that survives it.
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

70 probes. The lane itself is the authority — run it rather than trusting this
table, which is a snapshot for orientation.

| | constraints |
|---|---|
| **KnownTrip** (19) | `Power`, `PowerTable`, `AllDifferent`, `AllDifferentExcept`, `Count`, `NValue`, `AtMostOne`, `AtMostOneSmartTable`, `GlobalCardinality/hall`, `ArrayMinMax`, `LexSmartTable`, `SmartTable`, `Regular`, `RegularLegacy`, `RegularBacchus`, `MDD`, `Cumulative`, `Disjunctive`, `Knapsack` |
| **Clean** (37) | the arithmetic family, comparison, equality, linear, `AllDifferent` under `VC`, `Element` in both arms, `AllEqual` with holes and without, `Among`, `In`, `GlobalCardinality`, `Table` (both shapes), `ValuePrecede`, `SeqPrecedeChain`, `IncreasingChain`, `Lex`, `Sort`, `ArgSort`, `NegativeTable`, `Disjunctive2D`, `BinPacking`, `MinDistance`, `DifferenceConstraints`, `Nogoods` |
| **NoWidePosition** (14) | the graph and permutation family, and the Boolean constraints |

`Among`, `In`, `AllEqual/holes`, `GlobalCardinality`, `Table` and `Element` started
as `KnownTrip` and are now `Clean`, by the interval rewrites rather than by a
weaker arm: all of them still propagate at their original strength.

`GlobalCardinality` mattered most of the five, because it was the rule's own
counterexample: already the bounds arm, and still enumerating, so it had nothing
weaker to fall back to. Its just-met-demand branch forces a variable to a value,
which is two range removals however wide the domain is. **A second per-value site
remains** in its Hall reasoning, which the original probe could not reach — one
cover value means there is no multi-value hall — so it now has a row of its own
rather than being covered by association.

**`In` is worth more than its own row.** `create_integer_variable` over a vector
posts an `In` to carve the holes, so any probe that builds a sparse variable that
way was tripping inside `In` before it reached the constraint it meant to test.
`AllEqual/holes` was one: its row was measuring the wrong constraint, and only
turned into a real `AllEqual` trip once `In` was fixed. A row names the probe, not
necessarily the culprit.

`ArrayMinMax` is *not* in that list even though its union sweep was rewritten the
same way, and that is correct: it has a second per-value sweep, the full-GAC pass
over the array variables, which a probe with every variable wide still reaches. A
constraint can have more than one hazard, and a row flips only when all are gone.

Three things in that table were not what #833 predicted, and are worth
recording because they change what the later stages have to do:

1. **`AllDifferent` under `consistency::VC{}` is clean.** The designated
   fallback really is width-independent, so the `AllDifferent` fix is a policy
   decision rather than new propagator work. The same holds for `Element` under
   `BC`.
2. **`Power` trips**, which #833 did not list — it reaches `PowerTable`'s
   product enumeration. So does `LexSmartTable`.
3. **`Among`'s trip was conditional.** Its per-value branch only ran with the
   count pinned; with slack in the count the propagator concluded nothing and
   the probe passed without touching the hazard. A probe that does not reach a
   path proves nothing about it, which is what `HazardNotReached` exists to say.
   The probe still pins the count for the same reason, now to reach the interval
   rewrite that replaced the per-value branch.

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

Re-measured over all 69 probes after the interval rewrites for `ArrayMinMax`,
`Table` and `Among` landed. The figures move, so re-run the survey rather than
quoting this table after touching any propagator's removal loop — that is how the
previous version of it went stale, see below.

| | growth (opb / steps) | constraints |
|---|---|---|
| **Both** grow | 10x / 10x | `Power`, `PowerTable`, `NValue`, `Regular`, `RegularLegacy`, `RegularBacchus`, `MDD` |
| **OPB only** | 10x / 1.0x | `Cumulative` (19046 → 190046 rows; one capacity line per time point, so it is H3 on the encoding side) |
| **Steps only** | 1.0x / 10x | `GlobalCardinality/hall` (34-row OPB fixed, 33984 → 339984 steps) |
| neither | 1.0x / 1.0x | everything else, 61 of 70 |

`Multiply`, `Divide` and `Modulus` sit in the last row but are not flat: their OPB
grows 1.8x for a 10x width, which is the bit-width of the product, not a per-value
encoding. Nothing to do about that, and nothing a checker feature would help with.

**A "steps only" row is not on its own evidence for a checker feature**, and this
is the lesson the table's own history teaches. The previous version named `Among`
(32996 → 329996 steps) and `Table` (50788 → 509788) as the two clean candidates,
on the grounds that their encodings do not grow at all, so every extra step is the
same derivation with a different constant in it. That was true, and it was still
the wrong conclusion: both were also H1a in the propagation column, and the
interval rewrites collapsed both to **flat** — `Among` 98 steps and `Table` 93, at
either width. The copy-paste was real, but the right place to remove it was the
propagator, not the checker.

So the question to ask of a row here is not "are the steps repetitive" but **"is
the removed set an interval?"** Where it is, an interval rewrite deletes the volume
at full strength and needs nothing from VeriPB. Where it is not, no rewrite helps
and a checker feature is the only way out.

**On that test, none of the three rows above is a candidate either.** All three are
H1a sites — a propagator expanding an interval by hand — and all three are stage 4
work rather than evidence:

* `AllEqual/holes` was the starkest: `all_equal.cc` already computed the values to
  remove with `each_interval_minus` and then expanded each interval one value at a
  time, so the interval was literally in hand when the per-value loop started. The
  obstacle was that the reason names a *witness* — some variable whose domain lacks
  that value — which can differ across one interval, because the difference is
  taken against the intersection of every domain. **Done**: 16987 → 169987 steps
  became a flat 37. The witness is resolved by splitting the interval by which
  variable accounts for which part, and striking off what is accounted for, so each
  part is still removed exactly once.
* `GlobalCardinality`'s just-met-demand branch
  (`bounds_global_cardinality.cc`) removed every value of a variable *except*
  one, which is two range removals — and its reason was already hoisted out of the
  loop and constant, so it was a simpler case than `Among`'s. **Done**: 18024 →
  180024 steps became a flat 63.

  Its **Hall pruning** is a separate site, and it is the first one here whose
  obstacle is not the removed set. That set is an interval complement like all the
  others; what resists is the *justification*, whose `pol` builds an at-most-one
  over the hall values plus the single removed value, so the removed value is
  named in the derivation rather than merely concluded. It has its own probe and
  its own survey row now (33984 → 339984), and it is the most interesting
  remaining candidate for exactly that reason.
* `Element` walked the result values its array does not support (`element.cc`),
  which for a narrow array over a wide result is mostly intervals. **Done**, and it
  collapsed as predicted: 27981 → 279981 steps became a flat 108. Two of the three
  are left.

So the survey currently supports **no** VeriPB feature request at all: every row
whose steps grow at a fixed encoding is a propagator that has an interval and
spells it out. That is a real conclusion rather than a gap in the survey, and it
should be re-tested after stage 4 rather than assumed to stay true — a genuine
candidate would be a growing row whose removed set provably is not an interval,
and none of the 69 probes produces one today.

Two things kept this table wrong for longer than it should have been. The probe
sharpening of PR #849 turned exactly these three rows from `HazardNotReached` into
real hazards without the survey being re-run — sharpening a probe changes what the
survey measures. And the rows were read as feature evidence without first checking
the propagator for an interval it had already computed.

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
