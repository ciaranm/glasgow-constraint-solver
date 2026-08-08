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
range has been promoted.

**Second, and this is the part that bites**: the re-derivation is attempted
with `only_core` set. Derived constraints are invisible to it. That is fine
for optimisation and fatal for enumeration, for reasons below.

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
solution's --- it is the **backtrack clause** of whichever frame refutes the
subtree the solution was found in. Any solution in that subtree satisfies all
of the frame's guesses, so "at least one guess is false" excludes it. This is
example 3 of the paper:

```
@sol1    solx x1 -x2 ~x3 ;
@x1false rup 1 -x1 >= 1 ;
         core id @x1false ;
         del id @sol1 ;
```

`ProofLogger::solution` records each blocking constraint together with the
proof level that was active when it was logged; `ProofLogger::backtrack`, once
it has emitted its clause, deletes every recorded solution from a deeper
level. Because `solve_with_state` emits the frame's backtrack clause *before*
forgetting the level below it, the clause is always still in scope.

Note that the blocking constraint is load-bearing for the clause that replaces
it: at a solution leaf the guesses fix every variable, so "at least one guess
is false" is only RUP *because* the blocking constraint refutes the leaf. Emit
first, delete second.

### The things that are not in the issue

Three of them.

**1. The lazily-introduced encoding definitions have to go to core.** This is
the real obstacle, and it is a direct consequence of `only_core`. The deletion
goal is `core /\ ~blocking(sigma) |- false`. Negating the blocking constraint
fixes every *preserved bit* to its value in sigma. The backtrack clause is
written in *atoms* --- `i[x][eq0]`, `i[x][ge3]`, `~i[x][ge3]`, range literals.
Getting from one to the other needs the reifications that define those atoms:

```
red 1 i[z][b0] 2 i[z][b1] 2 ~i[z][ge2] >= 2 : i[z][ge2] -> 0 ;
red -1 i[z][b0] -2 i[z][b1] 2 i[z][ge2] >= -1 : i[z][ge2] -> 1 ;
red 1 i[z][ge1] 1 ~i[z][ge2] 2 ~i[z][eq1] >= 2 : i[z][eq1] -> 0 ;
red -1 i[z][ge1] -1 ~i[z][ge2] 1 i[z][eq1] >= -1 : i[z][eq1] -> 1 ;
```

`NamesAndIDsTracker` emits these on first use, *in the proof*, so they are
derived and the deletion check cannot see them --- and without them nothing
propagates from the bits to the atoms and the goal fails. They have to be
moved to core. There is no way round this: a witness or an explicit subproof
does not help, because `check_checked_deletion` sets `only_core` regardless.

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
only if the parent promoted it as well. The parent may have no solutions of
its own left to delete (the child already deleted them), so "promote when I
have solutions to delete" is not enough. `ProofLogger` therefore keeps
`core_lines_by_level` alongside `proof_lines_by_level`, and a frame promotes
its clause if it has solutions to delete **or** if the level below it holds a
promoted line. At the root the clause is the empty one, `rup >= 1`, and
deleting anything against a contradictory core is trivial.

**3. Restarts cannot have this.** A restart unwinds through
`SearchResult::RestartCutoffHit`, which forgets each level *without* emitting
the frame's backtrack clause. There is then nothing to promote and nothing to
discharge the descendants' clause deletions with, so the invariant in (2)
cannot be maintained. `solve_with` calls
`ProofLogger::disable_solution_deletion` when restarts are enabled, and
enumeration proofs under restarts keep every blocking constraint as before.
Retaining the promoted clauses instead of deleting them (via
`IntervalSet::each_interval_minus`) would work and is the obvious extension if
this ever matters.

Assertion levels above `Definitions` are excluded for a related reason: at
`Links` and above the atom definitions are omitted from the proof entirely, so
(1) has nothing to promote.

## What this does not do

- The `solx` lines themselves stay. They have to: `num_excluded_solutions`
  counts them, and that is what `ENUMERATION_COMPLETE` checks against.
- Nothing is deleted under restarts, or above `AssertionLevel::Definitions`.
- The proof gets slightly *longer*, not shorter --- the `core id` and `del id`
  steps are new text and the solution lines are unchanged. The win is in the
  checker's working set and in checking time. See the measurements below.
