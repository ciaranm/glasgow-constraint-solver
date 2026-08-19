# Per-rule firing counters

`GCS_SCHEDULING_RULE_STATS=1` makes `Cumulative` and `Disjunctive` print, at
exit, one line per propagation rule:

```
$ GCS_SCHEDULING_RULE_STATS=1 ./build/rcpsp --size 12 --seed 3 \
      --machine-fraction 0.8 --machine disjunctive --disjunctive-edge-finding
disjunctive_edge_finding_lb: calls=500 firings=370 already_true=21346 contradictions=0
disjunctive_edge_finding_ub: calls=500 firings=412 already_true=5754 contradictions=0
...
```

Written for the certified-scheduling paper (#729), where nearly every rule is
off by default and the reason is always a measurement.

## The four numbers

- **`calls`** — how many times the rule's sweep ran. A rule that is switched on
  is paid for here whether or not anything comes of it, which is why several of
  these are off by default.

- **`firings`** — how many times it moved a bound. This is *work done*: an
  inference that was not already true, that the solver had to justify, and that
  a proof has lines for.

- **`already_true`** — how many candidates it passed over because the conclusion
  it was about to draw already held.

- **`contradictions`** — how many times it proved the node infeasible.

## `already_true` is not a detection count, except where it is

Every rule tests the live bound and evaluates its own condition, and **which of
those two it does first differs between the encodings**, because they differ in
which is cheaper. That decides what `already_true` means:

| | order | so `firings + already_true` is |
|---|---|---|
| `Disjunctive` edge-finding | condition, then live bound | a **detection count** |
| everything else | live bound, then condition | a **candidate count** |

For the candidate rows, whether the rule's condition would *also* have held for
a skipped candidate is not evaluated and the number does not say. Getting a true
detection count everywhere would mean evaluating each condition for candidates
the rule currently skips — the expensive half of the sweep — and every solve
would pay for a number only a measurement wants.

Every rule that can skip a candidate counts it, including the time-table
pushes, so `already_true = 0` on a row with firings means *measured* zero and
not "no counter here". A row with contradictions and no calls, or firings and no
counter, is a wiring bug.

**This is the trap to avoid when quoting them.** A firing count from a
standalone simulation of a rule (`~/claude/tmp/nfnl-746/survey.py` and friends)
counts detections on random draws; `firings` here counts bound moves on a
benchmark instance. They are not two halves of one measurement, however natural
it is to put them in one sentence. Say which is which.

## They do not change the search

The increments are unconditional adds on a vector element — no environment
lookup, no map, no atomic, no lock — and the environment variable is read once,
at exit, to decide whether to print. Nothing here changes what is propagated.
That is checked two ways: `rcpsp_rule_counters_inert` pins the recursion count
with the counters compiled in, and the same instance's `.opb` and `.pbp` are
byte-identical to the ones the same commit's parent produces.

So a counter run and a timing run are the same run, and the numbers can be read
off the same sweep that produces the recursion counts.

## What they are for

Two questions a recursion count cannot answer.

**Is this rule earning its sweep?** `calls` against `firings` prices the rule
directly. A rule with millions of calls and a handful of firings is paying for a
scan it does not use, which is the argument for leaving it off by default —
and, unlike a recursion ratio, it does not need a control arm to be read.

**How much of its reach is redundant?** `already_true` against `firings` says
how much of what the rule detects some other rule (or an earlier pass of this
one) already had. On the instance above, edge-finding's lb half passes over
21346 candidates to make 370 pushes and its ub half passes over 5754 to make
412: the two halves do very different amounts of redundant work, which is
invisible in a recursion count and is why the halves have a row each.

## Adding a rule

`gcs/constraints/innards/rule_counters.hh`. Add an entry to the constraint's
`enum`, a name in the same position in the `RuleInstrumentation` construction,
and increment at the inference site. Count `already_true` wherever the rule
skips a candidate for having nothing to do; count `firings` immediately before
the `inference.infer_*` call, not after the condition, so that a `continue`
added later between them cannot silently decouple the two.

A rule with no switch of its own — the mandatory-overlap conflict, the strict
zero-length escape — still gets a `calls` count where its scan begins, so that a
row with contradictions and no calls always means a wiring bug rather than a
rule that has no sweep.

## Which rules

`Cumulative`: `time_table_lb`, `time_table_ub`, `time_table_overflow`,
`presence`, `overload`, `edge_finding_lb`, `edge_finding_ub`, `not_first`,
`not_last`.

`Disjunctive`: `mandatory_overlap`, `time_table_lb`, `time_table_ub`,
`presence`, `detectable_precedences_lb`, `detectable_precedences_ub`,
`edge_finding_lb`, `edge_finding_ub`, `not_first`, `not_last`, `overload`,
`zero_length_escape`.

Labelled by rule *family* and direction, not by strengthening: TTEF and the
energetic accounting share edge-finding's call site, and the published
not-first / not-last shares the window-energy one, because a strengthening
changes what a rule detects rather than where it infers. Only one arm of a
family can be live in a run, so which arm a row belongs to is settled by the
run's own flags.

The halves are separate because measuring one half of a symmetric rule and
doubling has been wrong here before: on `Cumulative` the two came out at 2.2%
and 51%.

## Not to be confused with

`GCS_DISJUNCTIVE_OVERLOAD_STATS`, which is still there and still separate. That
one measures what an overload *certificate* costs — bridge lines derived against
reused, window sizes, declined windows — for #730. This measures what a rule is
worth. Different question, different lifetime.
