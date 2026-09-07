# Cross-solver benchmarking: identical search trees

[benchmarking.md](benchmarking.md) compares two *builds of gcs* on in-tree
example binaries. This document covers the other axis: comparing gcs against
another solver, which is what a constraint-family document's mandatory
"cross-solver CPU performance" line has to cite (issue #868).

The harness is **not in this repository**. It lives in the `gcs-benchmarks`
repo, which is MiniZinc-driven, keeps large artifacts out of git and already
carries the Phase-0 Challenge-corpus sweep; see `bin/tree_compare.py` and
`docs/identical-tree.md` there, which hold the authoritative tables. What
follows is the method, and the numbers a family document may quote.

## The question, and why the obvious version of it is not worth asking

"gcs takes 6x the CPU of Gecode on this model" means nothing on its own,
because a solver that explores a different search tree is answering a different
question. Two solvers can differ in time because one propagates more strongly
(fewer nodes, more work per node), because one branches luckier, or because one
is simply quicker per node — and only the third is a propagator-speed claim.

So the comparison is only made where the **search tree is identical**, and that
is verified rather than assumed:

1. **Pin the search.** An unannotated model lets each solver choose its own
   variable and value order. Where an upstream model pins its own search, use it
   unmodified; otherwise rewrite the single `solve` item to
   `int_search(<array>, input_order, indomain_min, complete)` and *say which of
   the two happened*.

2. **Compare `nodes`, never `failures`.** gcs's `failures` runs about 2x
   Gecode's by convention, so a per-node figure built on it is wrong by 2x.
   `nodes` agrees exactly — to the digit, over eight million of them — when the
   trees agree.

3. **A run that was cut off carries no verdict.** Two runs stopped at the same
   time limit have node counts whose ratio is the throughput ratio restated;
   "different trees" from a pair of timeouts is an artefact. Shorten the
   instance rather than the reasoning: enumerating all solutions at a smaller
   size finishes, scales smoothly and stays deterministic. (See the same rule
   for in-tree sweeps in benchmarking.md.)

4. **Do not divide two millisecond figures.** gcs reports `solveTime` to the
   millisecond, so an instance needs to run for a second or more before a ratio
   is anything but rounding.

## Choosing the model

The family document asks for a benchmark dominated by one family, and the trap
is that the natural gcs benchmark is often a model no other solver would be
given. A disequality clique is the example: it is the right stress test for
`not_equals`, and every other solver would post an all-different global instead.

Take the model from an external suite where one exists, and prefer one that
pins its own search. `minizinc-benchmarks` turned out to contain both of the
models the `equals` family needed:

- `queens/queens.mzn` (Rafeh 2005, Stuckey 2006) is the pairwise-disequality
  decomposition, with no global in it: the unreified arm.
- `nmseq/nmseq.mzn` ("magic sequence, naive model") is `x == sum(bool2int(xs[i]
  == v))`, and pins its own `int_search`: the reified arm.

Where no such model exists, posting our own is defensible as long as the
document says so — but check the suite first, because "somebody else chose this
benchmark" is worth more than any argument about the model's quality.

## What it says about `equals`

Snapshot for citation: gcs `238c7836` (main plus three warning fixes) against
Gecode 6.3.0 via the MiniZinc 2.9.7 bundle, on an otherwise-idle Ryzen 9
9950X3D, 2026-09-07. Identical trees throughout; `gcs-benchmarks` has the full
tables and the raw numbers.

| model | arm | instance | nodes (both) | gcs / gecode |
|---|---|---|---|---|
| `queens --all` | unreified `!=` | n=12 | 292,203 | 0.93x |
| `queens --all` | unreified `!=` | n=13 | 1,513,771 | 0.94x |
| `queens --all` | unreified `!=` | n=14 | 8,396,439 | 0.97x |
| `nmseq` | reified `==` | n=100 | 767 | 6.20x |
| `nmseq` | reified `==` | n=200 | 1,567 | 6.40x |

The unreified arm is level with Gecode, marginally ahead. The reified arm is
6.3x behind, and `GCS_PROPAGATOR_STATS` localises that: 82% of propagation time
is in `Equals`, at **130,756 calls per node, 4.4% of them effectful, 52 ns per
call** — against 20.8 calls per node at 27% effectful and 48 ns on `queens`. Per
call gcs is fine; it is woken 23 times per domain change it makes. The lever is
trigger granularity, as in issues #819 and #807, not propagator cost.

## Where a strength difference shows up instead

Not every model can give a per-node number, and the failure is informative.
Swapping `queens` to `all_different` makes the trees diverge — 29,963 nodes for
gcs against 41,033 for Gecode at n=20, both finding the same first solution — so
no time comparison is available from that model, and what it does say is that
gcs's all_different is the stronger of the two here.

A family document should record that outcome in the same words: **which model
each solver was given, and whether the trees matched**. A time ratio without
that is not a measurement.
