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
`veripb-dev` MR !193. An older checker rejects them at the root `rup >= 1`,
reported as if a constraint were missing rather than as a checker limitation,
and `--unchecked-deletion` makes it go away --- which is misleading, since there
is nothing wrong with the deletions. Every VeriPB build reports version 3.0.2
regardless of commit, so check the commit rather than `--version`.

The narrow promotion discussed below needs a newer checker still, one containing
MR !217; what ships here does not, and verifies against public VeriPB today.

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

Two of them.

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

What ships promotes *all* of them, and not just the ones the deletion goal
reads --- but that is a decision about the checker we can rely on today, not a
claim that the narrow rule is insufficient. It is not: promoting only the
definitional closure of the atoms in the discharging clause --- an order atom's
two halves, an eq atom's two halves plus the two order cuts it is stated over,
and a range literal's likewise, but *not* the order chain linking neighbouring
cuts, since the bits settle each cut on its own --- passes the whole suite,
636/636. It is also a real reduction rather than a no-op: `abs_test`'s first
batch goes from 26 promoted constraints to 10, and `langford --all` from 2604
over 124 `core id` steps to 76 over 76. "The narrow closure, measured" below has
what that buys, which is more than tidiness: it removes the one regression in
the measurement table.

The reason the blanket rule ships anyway is that the narrow one needs a checker
containing MR !217, and the narrow rule's `skyscrapers 5` proof is one of the
two cases that fail without it. CI installs the checker by cloning public
`VeriPB.git` at HEAD, so until that contains !217, narrowing turns
`skyscrapers-5` and `ortho_latin-5` red. Blanket is the superset, so it is the
safe end to sit at meanwhile, and nothing else here depends on which is used.
Switching over is a small change once the checker allows it.

**2. Promotion cascades to the root.** Once a frame has promoted its clause,
its parent's `forget_proof_level` will delete that clause, and *that* is a
checked deletion too. The constraint that discharges it is the parent's own
backtrack clause, which is a prefix of the child's and so subsumes it --- but
only if the parent promoted as well. `ProofLogger` therefore keeps
`core_lines_by_level` alongside `proof_lines_by_level`, and the promotion rule
above reads it. At the root the clause is the empty one, `rup >= 1`, and
deleting anything against a contradictory core is trivial.

Deleting through the level forget, rather than next to the subsuming clause,
puts the blocking constraint at the level that actually refutes it, and costs
one fewer `core id` step and one fewer checked deletion per solution.

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

Checker is `veripb-dev` at MR !217 (chosen so the blanket and narrow tables
below are comparable, not because these proofs need it); quote the checker
commit alongside any checking time, since the version string does not
distinguish builds. "before"
is `d3c9e58b`; "after" is this branch. Each pair is timed *alternately* ---
before, after, before, after --- so machine drift lands on both sides equally.
Five runs each except `frequency_square`, which is four.
Times are seconds, size is the `.pbp` in bytes, and the ratio uses medians.

| instance | solutions | size before | size after | time before | time after | speedup |
| --- | --- | --- | --- | --- | --- | --- |
| `frequency_square --all --size 6 --lambda 2` | 53220 | 204569673 | 224919034 | 117.19 114.45 125.08 116.78 | 12.52 12.34 12.69 12.38 | 9.4x |
| `regular_random --all --seed=1` | 32985 | 14231970 | 18870069 | 21.62 21.63 21.54 21.48 21.91 | 2.07 2.08 2.07 2.10 2.11 | 10.4x |
| `langford --all` | 52 | 964583 | 1024105 | 0.24 0.24 0.24 0.24 0.24 | 0.27 0.27 0.26 0.27 0.26 | 0.89x |
| `talent` (optimisation) | 23 | 6592428 | 6669941 | 1.13 1.18 1.14 1.12 1.12 | 1.15 1.14 1.13 1.11 1.12 | 1.00x |

The "after" side includes stating solutions in bits, which is what the size
column mostly moved on; the section above separates the two changes.

Ratios are medians because the `frequency_square` "before" side has a spread of
about ten per cent run to run --- 114.45 to 125.08, with the high run third, so
it is variance on a 200 MB proof rather than a cold cache. The other three
instances are stable to a few per cent. Both sides verify in every case and the
solution counts agree (`ENUMERATION_COMPLETE` of 53220, 32985 and 52;
`BOUNDS 6 <= obj <= 6` for `talent`).

Peak RSS moves the wrong way on the big enumeration case: `frequency_square`
goes from 564780 KB to 644768 KB, because the encoding definitions promoted to
core are indexed differently there. `regular_random` is flat (48724 KB to
48680 KB) and `langford` is near enough (14072 KB to 14312 KB).

The shape to take from this: **the win is enumeration with many solutions, and
it is an order of magnitude.** Optimisation is free but not a speedup on
anything we have. `talent` is the longest improvement chain in the examples, at
23 logged solutions, and deleting 22 of them moves the checking time by nothing
measurable --- an objective-improving constraint is one short PB row over the
objective terms, so it is not what the checker's time goes on; the 77 kB it
gains is the bit-form `soli` lines, not the deletions. Take the optimisation
half as tidiness (and as the thing that stops a long-running branch and bound
accumulating rows without limit) rather than as a number. Small enumerations
lose slightly (`langford`, 52 solutions, 12 per cent slower and 6 per cent
bigger) because the one-off promotion of the encoding to core is not paid back
at that scale.

### The narrow closure, measured

Both sides are this branch; the only difference is which encoding definitions
get promoted. Same checker and the same alternating method, blanket → narrow:

| instance | promoted ids | `.pbp` bytes | median time |
| --- | --- | --- | --- |
| `frequency_square` | 52786 → 52652 | 224919034 → 224918889 | 12.65 → 12.80 |
| `regular_random` | 7717 → 7679 | 18870069 → 18869929 | 2.08 → 2.03 |
| `langford` | 2604 → 76 | 1024105 → 1011205 | 0.26 → 0.24 |
| `talent` | 0 → 0 | 6669941 → 6669941 | 1.14 → 1.14 |

The saving is concentrated where the enumeration is *small*, which is exactly
where the blanket rule costs us. On `langford` promotion drops by a factor of 34
and the 12 per cent loss in the table above disappears completely --- 0.24 s is
what the no-deletion baseline takes, so narrowing makes the small case free
rather than merely cheaper. On the two big enumerations there is almost nothing
to save, because with tens of thousands of solutions nearly every definition is
needed by some deletion goal anyway; `frequency_square` comes out about one per
cent slower, which is the closest thing to a cost here.

`talent` promotes nothing under either rule, which is worth stating: the
optimisation half never needs a definition in core at all, since what discharges
its deletion is the new `soli`'s own improving constraint, over the objective
terms. The closure question is entirely about the enumeration half.

## What this does not do

- The `solx` lines themselves stay. They have to: `num_excluded_solutions`
  counts them, and that is what `ENUMERATION_COMPLETE` checks against.
- No *blocking* constraint is deleted under restarts, or above
  `AssertionLevel::Definitions`. Both restrictions are specific to the
  enumeration half; the optimisation half deletes under restarts and at every
  assertion level, as above.
- Nothing is deleted for a solution found at the root, since no frame above it
  ever refutes it.
