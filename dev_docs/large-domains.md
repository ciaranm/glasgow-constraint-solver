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
int` a domain spanning billions of billions of values, so a wide domain is an
ordinary input rather than a mistake to be refused. (Deliberately not a figure:
what it is exactly depends on `Integer::max_bounded_value()`, which #853 changes,
and pinning it here coupled two branches whose CI could not see each other.) What
makes that safe is not a check that rejects it, but every constraint having
somewhere cheap to fall back to. A
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

**And before optimising a predicate, check it is the cost.** `Among`'s
`domain_is_inside_values_of_interest` looks like the obvious thing to speed up, and
a profile puts it at **0.75%** of the propagator's time. What the profile does show
is that the two places asking it were recomputing what the variable partition had
just worked out: a variable is not wholly inside the value set exactly when it is
not a `must_match` one, and it has some value of interest exactly when it is not a
`must_not_match` one. Iterating the partition's own subranges instead is **1.9x**
at a 40-value set, **2.7x** at 400 and **3.9x** at 5000, for no change to a single
inference.

Not, however, for a byte-identical proof, which this document originally claimed:
4 of 31 proofs move. `std::ranges::partition` *groups* the variables, where the
loops used to walk `vars` and skip, so a must_match variable's block can now be
emitted before a can_be_either one that preceded it. The steps are the same steps;
what changes with them is the `pol ... -N +` relative back-references, which count
lines backwards and so shift when a block moves. `stable_partition` does not help
and was tried: the grouping *is* the reordering, and stability within each group
does not undo it.

So this is a case where byte-identity is the wrong property to ask for, and the
weaker one — same OPB, same test output, same node counts, every proof still
verifying — is what holds. Worth being exact about, because this document uses
byte-identical proofs as a *technique* elsewhere (`In`, below, really is), and a
false instance makes the true ones harder to trust.

Asking the two surviving questions of the value set *as a set* pays on top of
that, and the reason it is worth doing is not the speed. `State` answers both at
interval level — `domain_intersects_with()` for "is any value of interest still
here" and `domain_is_subset_of()` for "is this domain inside the set" — and using
them means `among.cc` reaches for `State`'s per-value iterators nowhere at all,
which is a property that can be checked by inspection rather than by profiling.
That it is also **1.7x** at a 40-value set, **3.0x** at 400 and **1.6x** at 5000
is a bonus, not the argument.

**A warning attached to those numbers, because they were wrong here first.** This
paragraph originally said the interval version measured "exactly neutral". It does
not; the binary measured was stale, because the change carried a compile error
(`move` on a `gcs::` type is not found by ADL, where `move` on a `std::vector` is)
and the build check being used was `grep -c " error "`, which never matches
either compiler's output. A benchmark that links a library which failed to rebuild
compares a binary against itself, and the answer it gives — "no difference" — is
the answer it would give for any change at all. Check a build's *exit status*, and
treat "the change made no difference" as a claim needing the same suspicion as any
other.

**The cheapest H1a of all is where the conclusions are already intervals and only
the search for them is per-value.** `In`'s constant-set filter emitted one
`infer_not_in_range` per maximal run of forbidden values, and found those runs by
walking the domain and grouping consecutive ones. A merge against the permitted
set yields the same runs — a run breaks exactly where the domain has a hole or a
permitted value intervenes, which is where `each_interval_minus` ends one too — so
the rewrite changes nothing at all in the proof. Verified rather than argued: at a
fixed seed the OPB, the proof, and the test output are byte-identical before and
after — all 212 artefacts, not just the last instance's — and a differential check
computing both algorithms in one binary reports zero disagreements over ten seeds.
Look for this shape first; it is free.

*But check the constraint's other constructors before believing the row.* That
rewrite was of the branch `In` takes when every candidate is a constant, and
`In` has three constructors: with a *variable* among the candidates it takes the
other branch, which went on walking `dom(var)` a value at a time, asking each
value whether some source held it (#874). Three sites, in fact — that walk, the
overlap test in step 2 (now `State::domains_intersect`, a merge walk that stops
at the first common value), and the single-supporting-source pruning in step 3.
Rewritten the same way, the whole rule is now interval-shaped: 29.4 s of root
propagation at 10^9 becomes 22 µs, and, because the difference is also *fewer
questions asked*, a narrow search-heavy shape — six sources over `1..8`, four
`In`s and an `AllDifferent`, 26.1M solutions — goes from 14.9 s to 11.8 s with
recursions, propagations and solutions all identical.

**Check byte-identity with `GCS_PRESERVE_PROOF_FILES=all`, not `=1`.** The latter
keeps only the last instance's files under each basename, and `among_test` writes
its 31 proving instances under three basenames: 26 as `among_test_w0_pall`, 3 as
`among_test_dup`, 2 as `among_test_selfref`. At four artefacts apiece — `.opb`,
`.pbp`, `.scp`, `.varmap` — `=1` leaves twelve files to compare out of 124, and
that is how the claim above this one came to be believed when it was false. The
near miss is the part worth stating: the four proofs that moved are `w0_pall`
0001, 0002, 0003 and 0006, and the only `w0_pall` proof `=1` leaves behind is
0026 — so not one of the differences was ever in front of the check.

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

A view operand needs nothing extra. The lemmas name no bit vector, only order
conditions on the two operands, so they are emitted over whichever encoded
variable each one resolves to -- a registered view's own, which since #904 is
where its range literals live and is also the representation the model states
these rows in. Both of `min_max.cc`'s range paths and both of `In`'s dropped
their view guards accordingly.

`In` (#874) is the case where *both* lemmas carry the selector, because both
halves of its link are half-reified: the model says `V_i >= var` and
`V_i <= var` each under `sel_i`, so neither bound crosses unconditionally. Same
`3n+1` shape otherwise, and the same shape twice more in the mirror direction,
where the single supporting source is pruned to `dom(var)`. Ruling out the other
selectors is the first of the two: `! sel_j` follows from `dom(var)` holding
nothing `V_j` could be, which is the guarded walk again, once per interval of
`dom(var)` rather than once per value of it. With those out, the at-least-one row
forces `sel_i`, the link to the surviving source is unconditional, and the
conclusion's own two lemmas need no guard.

**When the lemmas are load-bearing, and when they are decoration.** Dropping just
the two bound lemmas from either of `In`'s range prunings, and leaving everything
else, is *accepted* by VeriPB on a probe where the source's absence from the run
follows from its declared bounds — a source over `0..400` and a run of `401..699`
— and it is accepted on all 37 of `in_test`'s contiguous-domain proving rows,
whose domains are a handful of values wide. It is *rejected* at both widths once
the absence is an interior **hole** instead — on the 38th row, the first of the
three `#874` added for exactly this. That is the distinction to reason
from, and it is not the width: a bound that the model itself states is a third
constraint the checker can put into the Theorem 2.9 configuration directly, so
unit propagation crosses the equality with no help. A hole is stated only by a
range literal, which is the disjunction RUP cannot split, and then the walk has
to be spelled out. `in_test`'s rows were all of the first kind until `#874` added
three sparse-domain ones; before those, sabotaging the lemmas changed nothing the
suite could see. (`equals` records the neighbouring observation from its own
mutation lane: there the exceptions are interval endpoints that land on a bit
boundary, where a bound is one literal rather than a sum.)

The same three rows say it under a view, which is the check worth having on the
crossing #904 introduced rather than on the lemmas themselves: with a view on the
supporting source (`--view-wrap=8 --view-position=1`), dropping the lemmas is
rejected on `in_test_holes_step1_source_hole`, so the pair really is carrying the
run's endpoints across the view's own encoding and not merely across the bare
variable's.

### Theorem 2.9 is what makes the two-lemma shape work, and it wants a *difference*

The bound-lemma shape above is not a trick that happens to work: it is an
instance of **Theorem 2.9 (Contradictory constraints on binary sums)** in
chapter 2 of Matthew's thesis
(*Pseudo-Boolean Proof Logging for Constraint Propagation Algorithms*,
Glasgow 2026, <https://theses.gla.ac.uk/86049/>; and see
[range_literals_spec.md](range_literals_spec.md) Appendix B3). Read the theorem before adapting the
shape to a new constraint, because its hypotheses are exactly the thing that can
fail.

The theorem says: for two's-complement sums `x` and `y`, the three constraints

```
y >= A            x - y >= B            x <= C
```

**always unit propagate to contradiction**, provided `A + B - C > 0` and
`B ∈ {0, 1}`. The proof is a slack cascade, and it turns on C2 containing exactly
the opposite literals to C1's and C3's with the same coefficients.

`justify_not_in_range_across_equality()` is that configuration with `B = 0`: the
equality row is the difference `x - y >= 0`, and the two lemmas put a *lower*
bound on one operand against an *upper* bound on the other. `min_max.cc` and
`element.cc`'s guarded versions are the same thing with a selector carried
through. So they are sound by a proven theorem, for any domain width — a probe
built to doubt it (`result` in `[0, 63]`, entries in `{0, 40}`, so the removed
run `[41, 63]` puts `result >= 41` against `array <= 40` with neither bound
tight) verifies, and the cascade it verifies through is the theorem's own.

**What `Abs` shows is where the hypotheses stop holding, not that the shape is
unreliable.** `Abs`' model is two half-reified rows: `v2 - v1 == 0` under
`v1 >= 0`, and `v2 + v1 == 0` under `v1 < 0`.

* The **non-negative** branch is a difference, so it is Theorem 2.9 and the two
  bound lemmas work. Verified by putting that branch back on the RUP shape:
  `abs_test` passes at three seeds.
* The **negative** branch links `v2` to `-v1`, so the row is a **sum**. The
  lemma's negation then supplies *two lower bounds* rather than a lower and an
  upper, and there is no assignment of the theorem's `x` and `y` to `v1` and
  `v2` that makes the row its `x - y >= B`. Outside the hypothesis, and not
  merely in principle: on `abs_test`'s own `v1 = [-6, 8]`, `v2 = [0, 15]` with
  `lo = -6`, the three constraints normalise to slacks 5, 8 and 8 against largest
  remaining coefficients 4, 8 and 8, so by **Proposition 2.1** (`C` propagates
  `l_i` iff `slack(C) < a_i`) nothing propagates at all. Same family as the
  thesis' own **Example 2.15**, which is the warning that generalisations of 2.9
  do not always hold.

So the rule to take away is about the *pairing*, not about `Abs`: **the two-lemma
shape needs a lower bound on one operand and an upper bound on the other, across
a row that is their difference.** A sign-flipped link does not qualify.
`justify_not_in_range.hh` used to suggest that it just needs "the mirrored
pairing"; that was too optimistic — the mirrored pairing *is* the
non-propagating configuration above — and the header comment was corrected to
say so.

`pol` is what does not care, which is why `abs/justify.cc` uses it for both
branches: the model half, plus the defining item of each atom whose arithmetic
the step uses, summed and saturated. The operands cancel, the constant comes out
negative, and saturation leaves a clause over order atoms. The non-negative
branch could use the cheaper RUP form, and does not, for uniformity — three
resolutions against two RUP lines is not worth a second code path on a
proof-writing path.

Two shapes come out of it, and their asymmetry is the useful part:

* Concluding on the variable the guard is *about* (`Abs`' image direction,
  `~[v2 in lo..hi]`) has to close both sign branches, because the conclusion's
  negation says nothing about the sign. Four resolutions, then one clause per
  branch whose only free literal is the sign; the two signs being a literal and
  its negation, the conclusion follows by RUP. Six lines.
* Concluding on the guard variable itself (the preimage direction,
  `~[v1 in lo..hi]`) is cheaper, provided the caller **splits each run at zero**
  first. Then `v1 >= lo >= 0` propagates `v1 >= 0` up the ge layer, so the
  conclusion's own negation decides the sign and only the active branch is
  needed. Three lines, and no case split left over.

Neither count depends on the range's width, which is the property that matters.

### Sabotaging proof lines one at a time under-reports

The same work produced a methodology result worth having, because the obvious way
to check a new justification is misleading.

Dropping each of `Abs`' twelve new proof lines in turn and re-running `abs_test`
at a pinned seed marks **eight of the twelve as droppable**; only one is
individually load-bearing, and that one only because of a row added specifically
to reach it. Emptying either justification wholesale is rejected, so the lines
are jointly necessary and individually redundant — VeriPB's unit propagation has
several routes to the same conclusion, and removing one leaves the others.

Greedily minimising instead gives a four-line set that passes the pinned seed.
It keeps only the *upper* lemma of each pair and only one of the two sign
branches, which cannot be right by symmetry, and it is not: the same four-line
set is **rejected on four of ten seeds**. The suite's randomised rows do not
separate the halves of a symmetric rule at any one seed, so a minimisation run
against one of them is fitting the fixtures.

Two rules follow. **Sabotage the whole justification, not its lines** — that is
the test that distinguishes a load-bearing derivation from a decorative one.
And **keep a derivation you can state end to end**, rather than the subset a
particular seed happens to need; the full set here passes ten seeds plain and
three view-wrapped, and each of its lines has a stated role.

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

**A third, learned on `Element` (#878): a domain's runs are not free to read.**
Not every H1a site is an inference at all. `Element`'s GAC sweep subtracts each
array entry's domain from the result's still-unsupported set, which is internal
bookkeeping — the set of values removed from `result` is identical either way, so
the proof does not change and there is nothing to get past the checker. What is
left is purely a question of cost, and the run-level form of that subtraction has
to get the runs from somewhere.

Four shapes were measured on `langford --size=11`, whose 25.7M `element` calls
are the only variable-array `Element` in a hot loop in the benchmark set (`qap`,
`tsp`, `table_layout` and `p_dispersion` all post the constant-array form, which
takes a different branch, and `hitori` and `seat_moving` post the variable one
but finish in under a tenth of a second). Instructions retired and cycles,
median of five pinned runs, with the search identical in all five:

| how the entry's domain is subtracted | instructions | cycles |
|---|---|---|
| a run of `erase()` per value — before (#515's fallback) | 47.587e9 | 19.789e9 |
| **contiguity test, else `copy_of_values()` + `for_each_interval()`** | **47.170e9 (−0.88%)** | **19.734e9 (−0.28%)** |
| `copy_of_values()` + `for_each_interval()`, unconditionally | 47.640e9 (+0.11%) | 19.821e9 (+0.16%) |
| a new zero-copy `State::for_each_interval_immutable()`, unconditionally | 47.324e9 (−0.55%) | 20.220e9 (+2.18%) |
| the same, in the holey branch only | 47.581e9 (−0.01%) | 20.440e9 (+3.29%) |

All four fix the hazard — none of them walks a value — so what separates them is
what the *contiguous* entry pays, which is most entries here. Two things in that
table are worth carrying forward.

Dropping the contiguity test and materialising every entry costs 0.1% of the
instructions, which is the `small_vector` copy, so the test earns its keep. And
the shape that avoids the copy altogether is the one that loses: both zero-copy
variants retire no more instructions than the per-value fallback and burn 2–3%
more cycles than anything else in the table. Nothing in `branch-misses` or
`L1-icache-load-misses` accounts for that (three more pinned runs, medians): all
four sit at 0.167–0.168e9 branch misses, and the variant with the *best* icache
figure — 0.125e9, against 0.142e9 for the per-value fallback — has the
second-worst cycles. So the extra cycles are stall this measurement does not
explain, and chasing it further was not worth doing once the answer was "don't".
**Do not reach for a new `State` iteration primitive for a per-entry inner loop
on the strength of the copy it saves; measure it, because the copy is not what
costs.**

Instructions retired is the metric that settles a comparison like this one, and
worth reaching for before wall time: identical search makes it reproducible to
0.002% here, where wall time and cycles move ±1% between batches and about 3%
between one hour and the next.

**A fourth, on `GlobalCardinality`'s closed propagator (#877): ask the cheap
question before reaching for a new primitive, not after.** The closed restriction
removes every value outside the cover from every variable, and it is idempotent
— once a domain is inside the cover it stays there, since domains only shrink —
so the number that matters is not what the removal costs but what the *no-op* run
costs, which is every run but the first. Four shapes over two searches whose
recursion and propagation counts are identical throughout: seven variables over
`[0,5]` with the whole of it covered (`flat`, one interval per domain), and the
same with the cover `{0,2,4}` (`holey`, three intervals per domain, one more than
`IntervalSet`'s inline capacity, so the copy allocates). Instructions retired,
median of five pinned runs:

| how the non-cover runs are found | flat | holey |
|---|---|---|
| walk the domain grouping runs — before | 4.7313e9 | 156.98e6 |
| `copy_of_values()` + `each_interval_minus()` | 4.5750e9 (−3.30%) | 146.86e6 (−6.45%) |
| **`domain_is_subset_of()` first, else the above** | **4.4653e9 (−5.62%)** | **138.94e6 (−11.5%)** |
| a new callback `IntervalSet::for_each_interval_minus()` | 4.4984e9 (−4.93%) | 141.36e6 (−9.95%) |
| both | 4.4655e9 (−5.62%) | 138.97e6 (−11.5%) |

The shape that wins is an existing `State` query rather than a new primitive, and
it wins for a reason worth stating separately from the numbers: it answers the
whole question without copying anything, and it can be false **at most once per
variable**, because this propagator's own run is what makes the domain a subset.
So the merge walk it duplicates on that one call is paid once, against a copy
saved on every later call.

The new primitive is then *subsumed*: with the early-out in, the generator form
and the callback form agree to three figures, because the code they differ over
is what almost never runs. That is `Element`'s finding arrived at from the other
side — there the question was whether to avoid the copy in the inner loop and the
answer was no; here the copy is worth avoiding, and the way to avoid it is a
query that already exists. **Measure the new primitive against the cheap
early-out, not against the code you are replacing.**

One further step was measured and not taken. The propagator is not merely
idempotent but *entailed* once every domain is inside the cover, so it could
return `PropagatorState::DisableUntilBacktrack` and not run again in the subtree
at all: another −0.70% / −1.74% on the two shapes, and half the propagation
count (102474 → 51246 on `flat`). That is a claim about the engine rather than
about domain width, and it changes a reported statistic, so it is left as a
separate question.

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
  each such loop needs its own counter declared at the loop. Four constraints
  carry one, over five sites: `element.cc`'s sweep over unsupported result values
  (now only on its per-value view path), `all_equal.cc`'s expansion of the
  intersection difference, `equals.cc`'s no-overlap reason, and `abs.cc`'s two
  interior hole loops. The counter does not belong in `IntervalSet::each()`
  itself, which is a general container used for deliberate enumeration —
  tabulation, and the tests.

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

  `abs.cc`'s two loops (#875) put a number on the first half. Its 10^9 shapes
  were reported as surviving in 129 s on a 2 TB box; re-measured here, the image
  shape takes 42 s and **16.4 GB**, and the preimage shape does not finish at
  all — `bad_alloc` after 45 s and 23.7 GB under a cap. So the same two rows
  would have come out one `Clean` and one `KnownTrip` on this 30 GB machine, and
  both `Clean` on the big one, from the identical code. That is the argument for
  instrumenting a loop rather than leaving it to the fallback, made concrete:
  neither reading was a fact about `Abs`.

  It also took two probes rather than a sharpened one. The `Abs` row posts two
  bare wide variables, which never *reach* either loop: the image of `v1`'s whole
  domain is the whole of `v2`'s, so `each_interval_minus()` yields nothing. One
  row per loop, because a probe that reaches one reaches neither the other (a
  contiguous `v2` has a contiguous preimage). Checked one at a time that each row
  trips its own counter and not the other's — with two counters in one propagator,
  a row that trips *a* guard proves nothing about which loop it exercised.

  What the counter at that site now counts is *moves of an interval walk*, not
  values (#867). A reason that says "these two domains do not overlap" one value
  at a time is width-proportional by construction, and the guard is then the only
  thing standing between a wide model and the cliff. Restating it over runs —
  "v1 has nothing in [lo, hi]", "v2 has nothing in [lo, hi]", and the bounds that
  separate them — makes the same fact cost one literal per run instead, which for
  two hole-free domains on opposite sides of a point is two literals at any
  width. **A width-proportional reason is worth trying to restate before it is
  worth guarding**, because the guard only converts a hang into an exception,
  whereas the restatement removes the width from the cost. The interval
  vocabulary this uses is `dev_docs/range_literals_spec.md`. Views were its one
  gap until #904 gave them range literals of their own, and a run of values a
  view cannot take is now one literal like anyone else's; the counter still
  covers the walk, which is what it was ever counting. The remaining variable
  with no range literal is a bits-less (direct-only, so zero-one) one, which has
  no interior run to state.
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
guard is on, since without the guard every probe passes trivially. A second
table does the same for the branching heuristics; see below, and note that the
first table cannot see them at all.

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

78 constraint probes, plus 20 heuristic ones in the second table. The lane
itself is the authority — run it rather than trusting this table, which is a
snapshot for orientation.

| | constraints |
|---|---|
| **KnownTrip** (19) | `Power`, `PowerTable`, `AllDifferent`, `AllDifferentExcept`, `Count`, `NValue`, `AtMostOne`, `AtMostOneSmartTable`, `GlobalCardinality/hall`, `ArrayMinMax`, `LexSmartTable`, `SmartTable`, `Regular`, `RegularLegacy`, `RegularBacchus`, `MDD`, `Cumulative`, `Disjunctive`, `Knapsack` |
| **Clean** (44) | the arithmetic family (with two rows of its own for `Abs`' interior holes), comparison, equality, linear, `AllDifferent` under `VC`, `Element` in both arms, with a holey entry and with a *view* on the result, `AllEqual` with holes and without, `Among`, `In` in three rows (a constant candidate list, and a variable one in each of its two rules), `GlobalCardinality` open and closed, `Table` (both shapes), `ValuePrecede`, `SeqPrecedeChain`, `IncreasingChain`, `Lex`, `Sort`, `ArgSort`, `NegativeTable`, `Disjunctive2D`, `BinPacking`, `MinDistance`, `DifferenceConstraints`, `Nogoods` |
| **NoWidePosition** (15) | the graph and permutation family, and the Boolean constraints |

`Among`, `In`, `AllEqual/holes`, `GlobalCardinality` (open and closed), `Table`
and `Element` started as `KnownTrip` and are now `Clean`, by the interval
rewrites rather than by a weaker arm: all of them still propagate at their
original strength.

`GlobalCardinality` mattered most of the six, because it was the rule's own
counterexample: already the bounds arm, and still enumerating, so it had nothing
weaker to fall back to. Its just-met-demand branch forces a variable to a value,
which is two range removals however wide the domain is. **A second per-value site
remains** in its Hall reasoning, which the original probe could not reach — one
cover value means there is no multi-value hall — so it now has a row of its own
rather than being covered by association.

**Every probe in this lane wraps nothing, and that is an axis of its own.**
`Element/view-result` is the first row to put a view on anything. It is the GAC
`Element` row with the result wrapped and nothing else changed, and before #924
it walked 10^9 values while the bare row beside it removed two ranges: the
result-union rule answered "can I say a range about these?" with a *type* test,
so a view anywhere sent the whole rule down a per-value walk of the remainder.
Nothing in this file could have caught that, because nothing in this file wraps.

The general question is open and is not really about `Element`. Every constraint
whose proof reasons about intervals has the same question to answer, and #904
changed the answer for all of them at once; a lane that only ever asks it about
bare variables cannot tell which ones were updated. One row is a start, not a
policy.

It has a **third** site, and finding it was a lesson about the axes a row covers
rather than about the constraint. `with_closed()` installs a propagator of its
own — the one that restricts every variable to the cover — and nothing in the
lane called `with_closed`, in either consistency arm, so neither of the rows
above could reach it (#877). It is the same shape `In` had: the conclusions were
always intervals, and what was per-value was *finding* them, by walking the
domain and grouping maximal runs the cover misses. `GlobalCardinality/closed` is
that row, and the fix is `each_interval_minus()` against the cover with a
`domain_is_subset_of()` early-out in front of it. Linear in the width before
(35 ms at 10^6, 351 at 10^7, 3505 at 10^8, **35088 at 10^9**), and 0 ms at every
one of those widths after. The default
BC level on purpose: the closed propagator is installed identically whichever
level is chosen, so the row is about that propagator alone, where a GAC row would
trip on the GAC arm's own sites (#876) and say nothing about this one.

**`In` is worth more than its own row.** `create_integer_variable` over a vector
posts an `In` to carve the holes, so any probe that builds a sparse variable that
way was tripping inside `In` before it reached the constraint it meant to test.
`AllEqual/holes` was one: its row was measuring the wrong constraint, and only
turned into a real `AllEqual` trip once `In` was fixed. A row names the probe, not
necessarily the culprit.

**And it needed three rows, not one.** `In` has three constructors, and the
original row used the all-constants one, which is the only spelling that takes
the branch the rewrite above fixed. With a variable among the candidates the
propagator takes the *other* branch, which was still walking `dom(var)` a value
at a time — so the row read `Clean` for a constraint that tripped instantly the
moment a model spelled it the way `member` does (#874). `In/vars` and
`In/vars-single-support` are the two rows for it: the first for the filtering of
`dom(var)`, the second for the pruning of the one source that still overlaps it,
which needs exactly one source to overlap and so cannot be reached by the first.
The moral generalises past this constraint: **a probe exercises one spelling of a
constraint's API, and a constructor is as much a branch as an `if` is.** Reading
the propagator for which of its arms the probe actually enters is the same
discipline as reading the *condition* on a branch, which is what `Element/holey`
taught.

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
  probe made the hazard disappear by being too wide. (And a narrow entry reaches
  only half of that sweep; see below.)
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

**And bracketing an axis with two probes is not the same as covering it.** The
`Element` bullet above is the case to learn this from, because sharpening it
once was not enough. The row it produced makes the array entries narrow, which
reaches the sweep's remainder; the row it replaced made them wide, which reaches
the `erase_range` that leaves no remainder. Between the two sits the shape that
reaches neither: an entry that is wide *and* has a hole in it. Both rows said
`Clean` while that shape walked a 10^9-value entry one value at a time (#878):
4.2 s of root propagation at that width, and 0 ms after the fix. The branch is
not selected by the width at all — it is selected by
`domain_size(entry) == hi - lo + 1`, which a narrow entry satisfies and a wide
contiguous one satisfies too. Before adding a row, read the *condition* on the
branch and pick the probe from that, rather than reasoning about the axis the
issue is named after. `Element/holey` is that row.

**And an option that installs a propagator of its own needs a row for the
option, not just for the constraint.** `GlobalCardinality`'s two rows were both
about the propagator `with_consistency` selects; `with_closed` installs a
*third* propagator alongside whichever of those runs, nothing in the lane called
it, and so no row reached that code at all (#877). The question to ask when
adding a constraint to the lane is not how many consistency arms it has but **how
many propagators it can install**, and an option that adds one rather than
choosing between them is the case a row per arm silently misses. Whether any
other constraint has the same gap has not been checked here; #876 proposes that
sweep — a row per arm and a row per `with_` option throughout — as its own piece
of work.

Where a constraint has both kinds of choice, keep the rows separate. The closed
propagator is installed identically whichever consistency level is chosen, so
`GlobalCardinality/closed` uses the default BC arm and is about that propagator
alone. A closed row on the GAC arm would also trip, on the GAC arm's own unfixed
sites (#876), and would then have gone on tripping after this fix — pinning a
`KnownTrip` that says nothing about either site.

One deliberate non-axis: the lane runs **without proof logging**. `NValue`'s
H2′ is caught anyway, because its per-value work is in `prepare()`, but a
constraint whose *encoding* alone were per-value would not be. That is by
design — see below.

### Branching heuristics (#879)

The constraint lane cannot see a heuristic, and that is not a gap in the probes
but a gap in what the lane is pointed at. Seven of the thirteen value orders did
work proportional to the domain's width, and they survived every other stage of
this issue for two reasons at once: a heuristic is not a propagator, so no amount
of sharpening a constraint's row reaches one; and the rows all take the *default*
branch heuristic, which is one of the lazy ones, so nothing there ever asked a
value order to do something expensive.

The cost also lands in the worst place. A constraint's per-value site runs once at
the root, or once per propagation; a value order runs at **every branching
decision**. And the one most likely to meet a wide domain is
`split_smallest_first`, because splitting is the standard answer to "too many
values to enumerate" — so the heuristic reached for precisely because the domain
is wide was one that could not survive it.

`gcs/large_domain_audit_test.cc` now carries a second table, twenty rows: every
value order against a fixed variable order, and every variable order against a
fixed value order, so a row names one heuristic and nothing else. It needs no
stopping rule of its own — `solve_with_state()` calls `branch_generator.begin()`
*before* the trace callback, and `begin()` runs the value order up to its first
`co_yield`, so the existing "stop at the root" probe has already made exactly one
branching decision by the time it returns.

Two shapes, and only one of them is an interval query:

* **Six needed a position.** The three splits want the value at `size / 2 - 1`,
  `median` the one at `size / 2`, and `random_out` and
  `reject_random_interval` a uniformly drawn position. All six are
  `IntervalSet::nth_value()`, which walks the interval list accumulating widths:
  `O(intervals)` where counting values to reach the position was `O(n)`. That is
  the whole fix, and it is the H1a shape again — the conclusion was already a
  single value, only the search for it was per-value.
* **`random` needed laziness, not a query.** A shuffled enumeration of the domain
  really is `O(width)`; what was wrong was paying it up front. It is now
  Fisher–Yates with the array left implicit — position `j` drawn uniformly from
  `[j, size)`, with a map holding only the positions a draw has displaced — so it
  costs what the search reads rather than what the domain holds. Same permutation
  distribution, because it is the same algorithm. This is the same reason
  `smallest_first` was always fine: the guard section above calls the lazy case
  legitimate explicitly.

The **variable** orders were all clean already, `dom_wdeg`'s weighting schemes
included: they read `domain_size()` and bounds, never values. They get rows
anyway, because "no heuristic does work proportional to a domain's width" is a
property worth having checkable rather than argued — and because a row names its
heuristic, which link-checks it. That is how `variable_order::with_largest_value`
turned out to be declared and documented in the public header and never defined
at all.

**What it costs, measured per call at a fixed seed** (ns, one core of an EPYC
7643, Release, mean of a long run; `split_sm` and `median` shown, the others
track them):

| domain | `split_smallest_first` before | after | `median` before | after |
|---|---|---|---|---|
| width 4 | 131 | 67 | 214 | 66 |
| width 256 | 1 716 | 67 | 3 838 | 66 |
| width 4096 | 25 822 | 67 | 55 812 | 67 |
| width 4096, 64 holes | 26 234 | 243 | 56 504 | 243 |
| width 10⁶ | 6 317 324 | 67 | 25 540 065 | 65 |
| width 10⁸ | 629 960 951 | 68 | 2 899 422 752 | 68 |

Flat in the width, as intended, and **faster at every width including the
narrowest** — the old spelling paid for a `std::generator` frame and the
`std::function` the view application needs, where the new one copies a
two-element inline vector. The holey rows are the honest cost: `nth_value()` is
`O(intervals)`, so 64 holes cost about four times one interval, and nothing about
the domain's width enters either way.

`random` is the one place where laziness is not free. Handing out a **full**
enumeration of a narrow domain costs 25 ns per value eagerly and 79 ns lazily —
a hash-map operation where there used to be a vector index. End to end that is
invisible: a full-enumeration search over nine-value domains measured 3 940
ns/node before and 3 912 after, i.e. no difference outside noise, because a
branching decision is a per-cent of what a node costs. The trade is a constant
against an asymptote, which is the right way round.

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

Re-measured over all 75 probes after the interval rewrites landed for
`ArrayMinMax`, `Table`, `Among`, `Element`, `In`, `GlobalCardinality` and
`AllEqual/holes`, and again after #878, #875, #877 and #874 — which moved nothing
but their own rows: `Element/holey` is flat at 41 rows and 78 steps, `Abs/hole` at
30 and 78, `Abs/hole-preimage` at 26 and 113, `GlobalCardinality/closed` at 24 and
83, and none of the rewrites changes which values get removed, so no other row
could have moved either. (Checked, for #877, by diffing a whole survey run against
one from `main`: identical bar the new row.) The figures move, so re-run the
survey rather than quoting this table after touching any propagator's removal
loop — that is how the previous version of it went stale, and how the
`GlobalCardinality/hall` figures below came to be corrected.

**#874's two rows are the case for running this survey and not just the audit
lane.** With the propagation fixed, `In/vars` was flat at 88 steps but
`In/vars-single-support` read 7048 → **70048**: the rule's proof was still
per-value even though its inferences were not, because the scaffolding that rules
out the non-supporting sources' selectors emitted one line per value of
`dom(var)`, and the reason it is emitted under named one literal per value too.
The guard cannot see either — a reason is only materialised with proofs on, and
the lane runs without them — so the survey was the only thing that showed it.
The walk that fixes it is the same one the conclusions use, one interval at a
time, and the row is now flat at 93.

| | growth (opb / steps) | constraints |
|---|---|---|
| **Both** grow | 10x / 10x | `Power`, `PowerTable`, `NValue`, `Regular`, `RegularLegacy`, `RegularBacchus`, `MDD` |
| **OPB only** | 10x / 1.0x | `Cumulative` (19046 → 190046 rows; one capacity line per time point, so it is H3 on the encoding side) |
| **Steps only** | 1.0x / 10x | `GlobalCardinality/hall` (34-row OPB fixed, 43988 → 439988 steps) |
| neither | 1.0x / 1.0x | everything else, 69 of 78 |

The last row means "does not grow with the width", not "identical at both widths",
and three entries in it are worth naming so nobody reads them as a promise.
`Multiply`, `Divide` and `Modulus` grow **1.8x** in OPB rows for a 10x width, which
is the bit-width of the product rather than a per-value encoding; and `Modulus`
also moves 77 → 85 steps, **1.1x**. Both are logarithmic in the width, so neither
is a hazard and neither is something a checker feature would help with — but they
are not 1.0x, and the row's header is a threshold, not a measurement.

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
  its own survey row now (43988 → 439988), and it is the most interesting
  remaining candidate for exactly that reason.
* `Element` walked the result values its array does not support (`element.cc`),
  which for a narrow array over a wide result is mostly intervals. **Done**, and it
  collapsed as predicted: 27981 → 279981 steps became a flat 108. All three are
  now done, and each collapsed the same way, which is what leaves the paragraph
  below with a single row to stand on.

So the survey currently supports **no** VeriPB feature request at all: every row
whose steps grow at a fixed encoding is a propagator that has an interval and
spells it out. That is a real conclusion rather than a gap in the survey, and it
should be re-tested after stage 4 rather than assumed to stay true — a genuine
candidate would be a growing row whose removed set provably is not an interval,
and none of the 75 probes produces one today.

Two things kept this table wrong for longer than it should have been. The probe
sharpening of PR #849 turned exactly these three rows from `HazardNotReached` into
real hazards without the survey being re-run — sharpening a probe changes what the
survey measures. And the rows were read as feature evidence without first checking
the propagator for an interval it had already computed.

### The bad encoding cases

Eight constraints write an OPB whose size grows with the domain. They are not
all the same shape, and the difference decides whether a checker feature is the
only way out. They are filed as five issues -- the `Regular` family shares one --
and parked under tracker **#846**; nothing here is scheduled before the
propagation work in #833.

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
