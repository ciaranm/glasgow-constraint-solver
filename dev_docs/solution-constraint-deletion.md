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
emits, at the point that subtree is torn down. So a solution found at depth
*d* is deleted by the frame at depth *d-2*, discharged by that frame's
clause. At depth 0 the level is Top and the constraint stays for the whole
proof, which is right: nothing above ever refutes it.

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
every *preserved bit* to its value in sigma. The backtrack clause is written
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

**2. Promotion cascades to the root.** Once a frame has promoted its clause,
its parent's `forget_proof_level` will delete that clause, and *that* is a
checked deletion too. The constraint that discharges it is the parent's own
backtrack clause, which is a prefix of the child's and so subsumes it --- but
only if the parent promoted as well. `ProofLogger` therefore keeps
`core_lines_by_level` alongside `proof_lines_by_level`, and the promotion rule
above reads it. At the root the clause is the empty one, `rup >= 1`, and
deleting anything against a contradictory core is trivial.

**3. VeriPB loses a later conflict if a checked deletion lands in the wrong
place.** This one is not about GCS at all, and it is why solution constraints
are deleted by the *level forget* rather than next to the clause that subsumes
them, which is what the first cut did and what the paper's example looks like.

With the first cut, `scp_chain_multiply_square_sat` --- `--all` enumeration of
`X * X = Z` over `X` in `-3..3`, seven solutions --- stopped verifying: the
root's `rup >= 1` was rejected as not RUP. Moving the *single* deletion of the
last solution's blocking constraint one rule later, from just before the
parent frame's `rup 1 ~i[Z][eq9] >= 1` to just after it, makes the proof
verify. Dumping VeriPB's live constraint database at the failing step in both
variants (`-t`, replaying `ConstraintId` / `Deleting IDs` / `Checked deletion
of ID` lines) gives **byte-identical sets of 226 constraints**, and the traces
differ in exactly one place: which of the deletion and the addition comes
first. So the checker reaches the same database and finds the conflict from
one and not the other. Unit propagation to conflict is confluent, so this
looks like state in the propagation engine that a checked deletion disturbs
--- `Database::delete_constraint` detaches from the propagator, and
`update_unique_index` merges and detaches duplicates, both inside the
`only_core` window that `DeletionChecker::compute` opens. It deserves an
upstream report; a minimal reproducer is a proof of the shape

```
solx ... ;      % a solution
rup <leaf backtrack clause> ;
core id -1 ;
del id -2 ;     % <-- here fails, one rule later verifies
rup <parent backtrack clause> ;
...
rup >= 1 ;      % rejected
```

Deleting through the level forget avoids it, because the blocking constraint
then outlives every clause derivation it took part in. That is not a proof
that the artefact cannot bite somewhere else, and it is the main reason to be
careful when changing where these deletions are emitted.

**Restarts cannot have this.** A restart unwinds through
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

## Measurements

veripb 3.0.2, this VM, each pair timed back to back in one sitting; five runs
each except `frequency_square`, which is four. Proof size is the `.pbp` in
bytes. "before" is `d3c9e58b`.

| instance | solutions | size before | size after | time before (s) | time after (s) | speedup |
| --- | --- | --- | --- | --- | --- | --- |
| `frequency_square --all --size 6 --lambda 2` | 53220 | 204569673 | 205546954 | 115.26 115.00 114.07 113.44 | 12.04 12.13 12.07 12.11 | 9.4x |
| `regular_random --all --seed 1` | 32985 | 14231970 | 13947925 | 21.09 21.16 21.17 21.28 21.21 | 1.99 1.99 1.99 1.99 1.99 | 10.6x |
| `langford --all` | 52 | 964583 | 978761 | 0.24 0.23 0.23 0.23 0.23 | 0.26 0.26 0.26 0.26 0.26 | 0.88x |
| `nonogram --all` | 1 | 41287 | 42142 | 0.00 | 0.00 | --- |
| `talent` (optimisation) | 3 | 6592428 | 6593004 | 1.11 1.12 1.11 1.13 1.11 | 1.11 1.10 1.11 1.11 1.10 | 1.00x |
| `tour` (optimisation) | --- | 3280786 | 3280868 | 0.47 0.48 0.48 0.47 0.47 | 0.48 0.48 0.48 0.48 0.48 | 0.98x |
| `table_layout` (optimisation) | --- | 5718477 | 5718529 | 0.24 0.25 0.24 0.24 0.25 | 0.25 0.24 0.25 0.24 0.24 | 1.00x |
| `p_dispersion`, `colour`, `cumulative`, `circuit_random` | --- | --- | --- | 0.00 | 0.00 | --- |

Peak RSS moves the wrong way on the big enumeration case: `frequency_square`
goes from 564 MB to 645 MB, because the encoding definitions promoted to core
are indexed differently there. `regular_random` is flat (48.6 MB to 48.4 MB).

The shape to take from this: **the win is enumeration with many solutions, and
it is an order of magnitude.** Optimisation is free but unmeasurable here ---
these instances log two or three improving solutions, so there is almost
nothing to delete; an instance with a long chain of improvements would be the
one to look at. Small enumerations lose slightly (`langford`, 52 solutions, 12
per cent slower and 1.5 per cent bigger) because the one-off promotion of the
encoding to core is not paid back.

## What this does not do

- The `solx` lines themselves stay. They have to: `num_excluded_solutions`
  counts them, and that is what `ENUMERATION_COMPLETE` checks against.
- Nothing is deleted under restarts, or above `AssertionLevel::Definitions`.
- Nothing is deleted for a solution found at the root, since no frame above it
  ever refutes it.
