# Leaving root-fixed bounds out of reasons

Once the root of a search pass has propagated to a fixpoint, every bound it
holds is a consequence of the formula alone. A reason that restates such a bound
(`x >= 3` when the root already has `x >= 3`) adds a literal that the checker
can only falsify one way, so it is dead weight. On scheduling instances that
weight is a large part of the proof. This note describes how the proof logger
leaves those literals out, what it has to write down so VeriPB still accepts the
lines, and the one rule a justification writer has to follow.

## The call

The logger does not try to work out what "the root" means. The search tells it
so, with `ProofLogger::assume_current_bounds(state)`. `solve_with_state` in
`gcs/solve.cc` makes that call at depth 0, after propagation succeeds. That
point has three relevant properties:

- **No guesses.** The call throws if any guess is active. VeriPB has no
  assumptions, so a fact the logger takes as given must be one the proof can
  derive with no decision in force.
- **It lasts as long as the level.** The snapshot belongs to the active proof
  level, which is 1 for the depth-0 frame. Level 1 survives a restart, and the
  next pass's call replaces the snapshot. `forget_proof_level` drops the
  snapshot together with the lines written at that level.
- **Presolvers and initialisers run before it,** at level 0. Nothing they write
  is filtered.

The snapshot is one entry per variable, saying which bound literals may be left
out. Only a literal that states the bound exactly qualifies: `x >= lb`,
`x < ub + 1`, and `x = v` for a variable fixed at `v`. If the root has
`x >= 5`, a reason that says `x >= 3` is weaker than the unit. Leaving it out
would need a step that VeriPB's unit propagation does not take through the bit
encoding, so it stays in.

## What backs each omission

Leaving out a literal makes the line stronger, and VeriPB still has to accept
it. There are two cases.

- **A bound that moved at the root.** The logger writes `rup 1 <lit> >= 1 ;` the
  first time a line leaves that literal out, at the snapshot's level. It
  remembers the line's ID, and a later snapshot reuses it if the bound has not
  moved again. The unit is lazy, so a variable no reason mentions costs nothing.
- **A bound still at its declared value.** The proof already has this, either
  from the bits or from the boundary pin
  (`NamesAndIDsTracker::order_literal_holds_at_top`). However, the pin is
  written when the literal's atom is first created, which is often *after* the
  snapshot. A side whose atom does not yet exist therefore stays a candidate,
  and the logger asks again when a reason first mentions it. Deciding this at
  snapshot time lost most of the scheduling saving in the first measurements.

## Which lines are filtered

The filter applies to everything rendered through `emit_under_reason`, including
the internal lines a `JustifyExplicitly` writes. Most of the saving is in those
internal lines. Each rule is handled as follows:

| rule | handling |
|---|---|
| unhinted `rup`, `a` | omits freely; VeriPB's unit propagation finds the units |
| hinted `rup` | omits only a literal with a line to cite, and puts that line's ID **before** the existing hints. VeriPB uses hints in order, and appending them was rejected. A declared bound implied by the bits alone has no line, so it stays in. |
| `ia` | keeps everything; it is checked term by term against the one line it cites |
| inside a subproof | omits only a literal whose unit is already written, since a unit written there would be scoped to the subproof |

The feature is off when the assertion level is not `Off`. The external
justifier is not yet told which units are assumed. When it is, this call is the
place to hook it in.

## The rule for justification writers

A justification that combines its own lines later and relies on reason terms
cancelling must opt out:

```cpp
ProofLogger::KeepAssumedReasonLiterals keep_reasons{logger};
```

While the guard is alive, the logger keeps every reason literal. The guard is
needed because leaving out a literal on an earlier line makes that line
stronger, but a later `pol`, `pbc` or `ia` that expected the term to cancel is
left holding a term it cannot get rid of. The four `ConditionalBound` builders
in `gcs/constraints/innards/product_justify.cc` hold this guard.
`tabulation_test` failed without it.

The test suite catches a missing guard as a rejected proof. It also catches a
filter that leaves out too much: a mutation that leaves out `x >= lb + 1` makes
35 of 356 targeted tests fail.

## What it bought

Measured on the CPAIOR 2027 scheduling pairs, j30, and the #1035 MiniZinc
corpus (49 instances; search identical; all verified):

| family | proof size | solver instructions | check time |
|---|--:|--:|--:|
| scheduling pairs (14) | 0.66 | 0.93 | 0.97 |
| j30, opt−1 (9) | 0.53 | 0.86 | 0.99 |
| MiniZinc corpus (26) | 0.87 | 0.99 | 0.99 |

Check time hardly moves, because a root-fixed literal is falsified at once and
never drives propagation. The cost is a check on every literal of every reason.
On a model where nothing is left out, such as `2011_vrp`, that is +1.3% of
instructions.
