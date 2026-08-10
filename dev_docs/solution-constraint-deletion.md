# Deleting logged solutions from a proof

Every solution we log costs the checker a constraint that lives for the rest
of the proof. For optimisation that is the objective-improving constraint
`soli` creates; for enumeration it is the blocking constraint `solx` creates,
which is a clause with one literal per preserved bit. We used to keep all of
them, forever, at `ProofLevel::Top`. Both are superseded long before the proof
ends, and this document is about deleting them when they are.

Read the CP 2026 paper, "Proof Logging for Projected Enumeration (and
Counting?) Problems in VeriPB", first if you have not: examples 3 and 4 there
are the enumeration recipe implemented here, and section 3's account of core
versus derived is the reason a naive `del` does not work.

**These proofs need a VeriPB from 2026-06-22 or later**, i.e. one containing
`veripb-dev` MR !193. An older checker rejects them at the root `rup >= 1`
with what looks like a missing constraint. Finding 3 below has the details,
including how to build a pre-fix checker and watch it happen.

## The obstacle: checked deletion only sees core

VeriPB keeps two constraint sets, *core* and *derived*. The input formula is
core; everything a proof derives is derived unless an explicit `core id` step
moves it. Deleting a derived constraint is free. Deleting a *core* constraint
is a **checked deletion**: the checker must re-derive the deleted constraint
from what is left. If it cannot, it does not fail --- it warns ("switching
from stronger to weaker guarantee using unchecked deletion"), drops
`strong_solution_guarantees`, and carries on. Everything downstream that
depended on the guarantee then silently stops working:

- `num_excluded_solutions` stops incrementing, so an `ENUMERATION_COMPLETE n`
  conclusion is rejected for having the wrong `n`;
- `best_valid_objective_value` stops updating, so a `BOUNDS` conclusion is
  rejected;
- `output EQUIOPTIMAL` / `EQUISATISFIABLE` / `EQUIENUMERABLE` is rejected.

Two things follow, and they are the whole design.

**First**, which set a constraint is deleted *from* is decided by where it
lives, not by whether the proof wrote `del` or `delc`. `delc` only *asserts*
that the target is core (VeriPB errors if it is not); a plain `del` on a core
constraint is still a checked deletion. So the range deletions
`forget_proof_level` already emits become checked the moment anything in the
range is core --- which is exactly the mechanism this change uses.

**Second, and this is the part that bites**: the re-derivation is attempted
with `only_core` set (`DeletionChecker::compute` sets it for the duration).
Derived constraints are invisible to it. That is free for optimisation and
expensive for enumeration, for reasons below.

The rejection is also reported a long way from its cause --- the warning names
no line. A one-line patch to VeriPB's `DeletionChecker` to include the proof
line, the constraint ID and the proof goal is on the branch
`claude/deletion-message-line-numbers` in the local VeriPB checkout; it is
worth upstreaming.

## Why the solution is stated in bits

`ProofLogger::solution` writes the assignment handed to `solx` / `soli` as bit
literals --- `i[x][b0] ~i[x][b1] i[x][b2]` --- rather than as the direct
encoding's `i[x][eq5]`. Both work: the rule propagates whatever it is given to
a full assignment before doing anything with it, and unit propagation crosses
between the two vocabularies through the same reifications either way. The
reason to prefer the bits is that they are the variables the OPB is written
over. That makes the logged solution a solution to the *formula*, in the
formula's own terms, and it makes the preserved set --- and so the projection
the `ENUMERATION_COMPLETE` conclusion is about --- the model's variables rather
than a set of atoms the proof introduced along the way. A trimmer then has to
keep the model alive to make sense of a solution line, which it must do
regardless, instead of the encoding definitions for whichever atoms the search
happened to create.

It costs proof size, because a variable is one eq atom but several bits.
Measured against `d3c9e58b`, on the enumeration instances where solution lines
are a real share of the file:

| instance | solutions | size before | size after | check before | check after |
| --- | --- | --- | --- | --- | --- |
| `frequency_square --all --size 6 --lambda 2` | 53220 | 205546954 | 224919034 | 12.37 12.37 12.50 | 12.64 12.62 12.70 |
| `regular_random --all --seed=1` | 32985 | 13947925 | 18870069 | 2.03 2.03 2.03 | 2.09 2.11 2.11 |
| `langford --all` | 52 | 978761 | 1024105 | 0.26 0.26 0.26 | 0.26 0.26 0.27 |

So 9%, 35% and 5% on size and 2--4% on checking time; peak RSS is unmoved on
`frequency_square` (644.8 MB against 644.7 MB). `regular_random` is the shape
that pays most, and it shows what the cost actually is: six variables, so a
solution line goes from six literals to eighteen, against a proof that is
otherwise small per solution. All three verify to the same conclusion before
and after.

## Optimisation

Branch and bound only ever logs a strictly better solution than the last, so
when a `soli` goes out, everything the previous one left behind is subsumed.
There are two constraints per solution:

- the objective-improving constraint VeriPB creates for the `soli` rule.
  `SolutionChecker::add_constraints_to_core` returns `true`, so this is
  **core**, and deleting it is checked;
- our own order-literal restatement `[obj < v] >= 1` that follows the `e`
  line, which is a plain `rup` and so derived, and free to delete.

The checked deletion needs no scaffolding at all. The goal is
`core \ {obj <= v_old - 1} /\ obj >= v_old |- false`, and the constraint that
discharges it --- `obj <= v_new - 1`, with `v_new < v_old` --- was put into
core by the `soli` we have just written. Both are over the same objective
terms, in the same vocabulary, so unit propagation closes it immediately.

Two ordering constraints, both load-bearing:

- the deletions go **after** the `e` line, which addresses the just-created
  constraint as `-1` and would otherwise be misdirected;
- they go **after** the new `soli`, so the discharging constraint is already
  in core when the goal is posed.

## Enumeration

Here the constraint that subsumes a blocking constraint is not the next
solution's --- it is the **backtrack clause** of a frame that refutes a
subtree the solution lies in. Any solution in that subtree satisfies all of
the frame's guesses, so "at least one guess is false" excludes it. This is
example 3 of the paper:

```
@sol1    solx x1 -x2 ~x3 ;
@x1false rup 1 -x1 >= 1 ;
         core id @x1false ;
         del id @sol1 ;
```

We do not write the `del` ourselves. `ProofLogger::solution` records the
blocking constraint at a **proof level** --- one shallower than the active
level, which is the level the finding frame's own backtrack clause is tagged
at --- and `forget_proof_level` deletes it as part of the range it already
emits, at the point that subtree is torn down. A frame at depth *d* forgets
level *d+1*, so a solution found at depth *d* --- recorded at level *d* --- is
deleted by its parent, at depth *d-1*, and discharged by that frame's clause.
A solution found at depth 0 lands at Top and stays for the whole proof, which
is right: there is no frame above it to refute it.

Note that the blocking constraint is load-bearing for the clause that
supersedes it: at a solution leaf the guesses fix every variable, so "at least
one guess is false" is only RUP *because* the blocking constraint refutes the
leaf. Emit first, delete later.

`ProofLogger::backtrack` moves its clause into core exactly when the level it
is about to forget holds core constraints. That is the whole promotion rule,
and it covers both cases: a level holding solutions' blocking constraints, and
a level holding a descendant's clause that was promoted for the same reason.

### The things that are not in the issue

Three of them.

**1. The lazily-introduced encoding definitions have to go to core.** This is
the real obstacle, and a direct consequence of `only_core`. The deletion goal
is `core /\ ~blocking(sigma) |- false`. Negating the blocking constraint fixes
every *preserved variable* to its value in sigma --- the bits, since those are
what the OPB is written over and what `solution` now states a solution in (see
"Why the solution is stated in bits" below). The backtrack clause is written
in *atoms* --- `i[x][eq0]`, `i[x][ge3]`, `~i[x][ge3]`, range literals. Getting
from one to the other needs the reifications that define those atoms:

```
red 1 i[z][b0] 2 i[z][b1] 2 ~i[z][ge2] >= 2 : i[z][ge2] -> 0 ;
red -1 i[z][b0] -2 i[z][b1] 2 i[z][ge2] >= -1 : i[z][ge2] -> 1 ;
red 1 i[z][ge1] 1 ~i[z][ge2] 2 ~i[z][eq1] >= 2 : i[z][eq1] -> 0 ;
red -1 i[z][ge1] -1 ~i[z][ge2] 1 i[z][eq1] >= -1 : i[z][eq1] -> 1 ;
```

`NamesAndIDsTracker` emits these on first use, *in the proof*, so they are
derived and the deletion check cannot see them --- and without them nothing
propagates from the bits to the atoms and the goal fails. There is no way
round it: a witness or an explicit subproof does not help, because
`check_checked_deletion` sets `only_core` regardless.

They are all emitted at `ProofLevel::Top` and never deleted, so promoting them
is safe; the witnesses only ever touch the fresh atom, never a preserved
variable, so Proposition 6 of the paper applies and the projected solution set
is unchanged. Promoting *every* Top line would be simpler but is wrong:
`DerivedCumulative` deletes abandoned Top lines through
`ProofLogger::delete_proof_lines` (issue #666), and those deletions would
become checked and fail. So the tracker marks its own lines, with
`DefinitionRecordingScope`, and they are batched into `core id` steps issued
lazily --- the first time a deletion actually needs them, and never at all in
a proof that deletes nothing.

It is *all* of them, and not just the ones the deletion goal reads --- but that
is parked rather than settled, and the honest position is worth writing down.
The narrower rule is the obvious one to try: promote only the definitional
closure of the atoms in the discharging clause, being an order atom's two
halves, an eq atom's two halves plus the two order cuts it is stated over, and
a range literal's likewise --- but not the order chain linking neighbouring
cuts, since the bits settle each cut on its own. That takes `abs_test`'s first
batch from 26 lines to 10, and verifies. Whether it is *sufficient* we cannot
currently say, because the two experiments that would answer it disagree, and
at least one of them is measuring the checker rather than us:

- Against a current checker, the narrow rule fails `skyscrapers 5` and
  `ortho_latin 5` at a shallow `rup`, with no unchecked-deletion warning
  anywhere before it. Both of those failures are VeriPB regressions, bisected
  to two unrelated commits and reported upstream as `veripb-dev` issue #210. A
  checker predating either commit verifies both proofs.
- Against that older checker, however, the narrow rule fails 24 *other* tests
  that the blanket promotion passes, mostly `linear_constraint_*`. Those are
  not diagnosed. They are either a real gap in the closure that the newer
  checker's propagation happens to paper over, or further checker bugs.

Sufficiency that moves with checker version is not something to build on in
either direction, so the blanket promotion stays until #210 is fixed and the
comparison can be re-run against a checker worth trusting. Nothing else here
depends on which way that lands: the blanket rule is a superset of the narrow
one, so it is the safe end to sit at while the question is open.

**2. Promotion cascades to the root.** Once a frame has promoted its clause,
its parent's `forget_proof_level` will delete that clause, and *that* is a
checked deletion too. The constraint that discharges it is the parent's own
backtrack clause, which is a prefix of the child's and so subsumes it --- but
only if the parent promoted as well. `ProofLogger` therefore keeps
`core_lines_by_level` alongside `proof_lines_by_level`, and the promotion rule
above reads it. At the root the clause is the empty one, `rup >= 1`, and
deleting anything against a contradictory core is trivial.

**3. The checker has to be new enough.** The first cut of this work appeared to
show that VeriPB lost a conflict when a checked deletion landed between a
constraint's last use and a later `rup`: `scp_chain_multiply_square_sat` ---
`--all` enumeration of `X * X = Z` over `X` in `-3..3`, seven solutions ---
stopped verifying, with the root's `rup >= 1` rejected as not RUP.

That diagnosis was wrong, and an earlier version of this section proposed an
upstream report that should not be filed. The failure is `veripb-dev` issue
#192, fixed by MR !193 ("never reset trailhead to higher position than
current", merged 2026-06-22); the checker installed on the machine at the time
predated the fix while still reporting version 3.0.2. Deletion position has
nothing to do with it. The *shipped* proof, with the deletion where this branch
puts it, fails at the root `rup >= 1` on a pre-fix checker and verifies on a
fixed one --- and so does every variant with the deletion moved earlier or
later. Build `veripb-dev` at `dbc46fe0^` to see it for yourself.

What survives is a requirement rather than a design constraint: these proofs
need a VeriPB from 2026-06-22 or later. An older checker rejects them at the
root with an error that reads like a missing constraint rather than a checker
bug, and `--unchecked-deletion` makes it go away, which is misleading --- there
is nothing wrong with the deletions.

That is not the only checker caveat, and "new enough" is not the same as
"correct": two later propagation regressions are reported as `veripb-dev` issue
#210. Neither affects what is shipped here, which verifies 636/636, but both
affect the narrow-promotion variant discussed above, and both are reasons to
treat a lone deletion-related verification failure as a question about the
checker until a second checker version agrees with it.

Deleting through the level forget is kept, but on its own merits rather than to
dodge anything: it puts the blocking constraint at the level that actually
refutes it, and it costs one fewer `core id` step and one fewer checked
deletion per solution than deleting next to the subsuming clause does.

**The enumeration half cannot have restarts.** A restart unwinds through
`SearchResult::RestartCutoffHit`, which forgets each level *without* emitting
the frame's backtrack clause. There is then nothing to discharge the core
deletions in that level with. `solve_with` calls
`ProofLogger::disable_solution_deletion` when restarts are enabled, and
enumeration proofs under restarts keep every blocking constraint at Top as
before. Retaining the promoted lines instead of deleting them (via
`IntervalSet::each_interval_minus`) would work and is the obvious extension if
this ever matters.

Assertion levels above `Definitions` are excluded for a related reason: at
`Links` and above the atom definitions are omitted from the proof entirely, so
(1) has nothing to promote.

**The optimisation half is unaffected by both.** This is worth stating
separately, because "nothing is deleted under restarts" is the obvious thing to
say and it is wrong. `discard_superseded_objective_constraints` is reached from
`solution` whenever there is an objective (`proof_logger.cc:371`) and carries
neither gate; `deleting_solution_constraints` and the `assertion_level` test are
read only on the enumeration path (`proof_logger.cc:336`, `486`, `880`). Nothing
here needs a backtrack clause: what discharges the deletion is the improving
constraint the *new* `soli` puts in core, and `objective_value` is declared
outside the restart loop (`solve.cc:381`), so each `soli` is still strictly
better than the last across passes. `colour --restarts 1 --prove` duly deletes
the previous solution's pair and concludes `s VERIFIED BOUNDS 2 <= obj <= 2`,
which is exactly what gets rejected if the guarantee has been dropped.
`solve_test.cc` covers both halves under restarts.

## Measurements

Checker **pinned** to `veripb-dev` f8c29244, built at
`~/claude/tmp/veripb-pinned`, because `~/.cargo/bin/veripb` was replaced
part-way through this work and both binaries report 3.0.2 (see finding 3).
Anything timed against an unpinned `veripb` on this machine is not comparable.
"before" is `d3c9e58b`; "after" is this branch. Each pair is timed
*alternately* --- before, after, before, after --- so machine drift lands on
both sides equally. Five runs each except `frequency_square`, which is four.
Times are seconds, size is the `.pbp` in bytes, and the ratio uses medians.

| instance | solutions | size before | size after | time before | time after | speedup |
| --- | --- | --- | --- | --- | --- | --- |
| `frequency_square --all --size 6 --lambda 2` | 53220 | 204569673 | 224919034 | 117.83 113.07 113.23 113.24 | 12.64 12.62 12.70 | 9.0x |
| `regular_random --all --seed=1` | 32985 | 14231970 | 18870069 | 21.54 21.46 21.42 21.41 21.25 | 2.09 2.11 2.11 2.12 2.17 | 10.1x |
| `langford --all` | 52 | 964583 | 1024105 | 0.23 0.23 0.23 0.23 0.23 | 0.26 0.26 0.27 0.27 0.27 | 0.85x |
| `talent` (optimisation) | 23 | 6592428 | 6669941 | 1.11 1.10 1.11 1.11 1.11 | 1.13 1.13 1.13 1.12 1.12 | 0.98x |

The "after" side includes stating solutions in bits, which is what the size
column mostly moved on; the section above separates the two changes.

The first `frequency_square` "before" run is a cold-cache outlier, which is
why the ratios are medians rather than means: the median is 113.235 either way,
so dropping the run by hand would change nothing. (Taking the mean instead, and
keeping the outlier, is what gives 9.6 --- which is how a wrong figure got into
an earlier version of this table.) Both sides verify in every case, and the
solution counts agree
(`ENUMERATION_COMPLETE` of 53220, 32985 and 52; `BOUNDS 6 <= obj <= 6` for
`talent`).

Peak RSS moves the wrong way on the big enumeration case: `frequency_square`
goes from 564580 KB to 644752 KB, because the encoding definitions promoted to
core are indexed differently there. `regular_random` is flat (48608 KB to
48352 KB) and `langford` is near enough (13804 KB to 14072 KB).

The shape to take from this: **the win is enumeration with many solutions, and
it is an order of magnitude.** Optimisation is free but not a speedup on
anything we have. `talent` is the longest improvement chain in the examples, at
23 logged solutions, and deleting 22 of them moves the checking time by nothing
measurable --- an objective-improving constraint is one short PB row over the
objective terms, so it is not what the checker's time goes on; the 77 kB it
gains is the bit-form `soli` lines, not the deletions. Take the optimisation
half as tidiness (and as the thing that stops a long-running branch and bound
accumulating rows without limit) rather than as a number. Small enumerations
lose slightly (`langford`, 52 solutions, 15 per cent slower and 6 per cent
bigger) because the one-off promotion of the encoding to core is not paid back
at that scale.

These figures replace an earlier set taken while the checker was being swapped
underneath them. They came out the same to within noise, so the earlier
conclusions stood up --- but they were not safe to quote at the time.

## What this does not do

- The `solx` lines themselves stay. They have to: `num_excluded_solutions`
  counts them, and that is what `ENUMERATION_COMPLETE` checks against.
- No *blocking* constraint is deleted under restarts, or above
  `AssertionLevel::Definitions`. Both restrictions are specific to the
  enumeration half; the optimisation half deletes under restarts and at every
  assertion level, as above.
- Nothing is deleted for a solution found at the root, since no frame above it
  ever refutes it.
