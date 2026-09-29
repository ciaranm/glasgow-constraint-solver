# `SeqPrecedeChain`: every value `v ≥ 2` first appears after `v − 1` does

> **Maturity** production ·
> **Audited** 2026-09-29 at `c9ceea25` ·
> **Open issues** none filed by this audit; it inherits
> [`value_precede`](value_precede.md)'s, and see [Next steps](#next-steps).
> Already open and touching this family: #833 (the large-domain policy).
> Tracked under #871.

`SeqPrecedeChain(vars)` is `value_precede_chain` with the implicit chain
`1, 2, 3, …`: values of `vars` may be introduced only in order. It is the
constraint that breaks the symmetry of interchangeable values in a set
partition, and the solutions over `1..n` are the restricted-growth strings. It
is a **delegating** constraint: `prepare()` clamps the variables and then
installs a [`ValuePrecede`](value_precede.md) over the chain `1..m`, under its
own constraint ID. Everything about propagation, the encoding and the proof of
the chain is in that document; this one covers the clamp and the delegation.

Three things to know before touching it.

- **It is weaker than GAC, twice over.** Its pairs are not pairwise GAC,
  since it inherits the missing half of Law and Lee's pair algorithm:
  `x₀ ∈ −1..4`, `x₁ ∈ {2, 4}` forces `x₀ = 1`, and the root leaves
  `x₀ ∈ {−1, 0, 1}`. And pairwise GAC is weaker than chain GAC, since the
  chain is propagated pair by pair: with `x₀ ∈ {−1, 1}`, `x₁ ∈ {−1, 2}`,
  `x₂ ∈ {0, 3}` and `x₃ ∈ {3, 4}`, all three solutions have `x₀ = 1` and
  `x₁ = 2`, each pair is GAC on its own, and the root prunes nothing.
- **Its clamp row is part of the definition.** Any variable whose declared
  upper bound exceeds the array length `n` gets an OPB row `x ≤ n`. The chain
  stops at `n`, so without that row a value above `n` would satisfy the OPB,
  and the chain cannot derive it; the row is what makes the OPB say what the
  constraint means. `cake_pb_cp` writes a clamp row for every position.
- **Its encoding is `Θ(n²)` rows and `Θ(n³)` terms,** because the chain is up
  to `n` values long and `ValuePrecede` spends `Θ(n)` rows and `Θ(n²)` terms per
  value. At `n = 80` the whole OPB is 51,679 rows and 11.2 MB, of which 25,759
  rows are this family's. It is independent of width.

## What it is

### Semantics

`SeqPrecedeChain(x₀, …, x_{n−1})` holds when, for every `v ≥ 2`, each
occurrence of `v` has an occurrence of `v − 1` strictly before it. Values of 1
and below are unconstrained: 1 may appear first, and zero and the negatives may
appear anywhere.

That is also MiniZinc's reading, with one upstream edge case: its
decomposition keeps a running maximum `H[i] = max(X[i], H[i−1])` of `max(X, 0)`
and requires each step to rise by at most one, starting at most 1, which allows
a leading 1 and constrains nothing at or below 0, except that it gives `H` the
domain `lb_array(X)..ub_array(X)`. On an all-negative array that domain
excludes the 0 that `max(X, 0)` needs, so `array[1..3] of var −3..−1` with
`seq_precede_chain` is unsatisfiable through the standard library (Gecode, on
MiniZinc 2.9.7 and 2.10.1), where this class, rightly, finds 27 solutions.
**The class's own doc comment says something slightly different** in two
places: "for every positive value `v` … `v − 1` must appear earlier", which
for `v = 1` would demand a 0 first; and, there and in `seq_precede_chain.cc`,
that `v` needs "`v` distinct earlier positions", where it is `v − 1`. The
implementation, the MiniZinc reading and the brute-force oracle this audit used
all let 1 appear first; it is the comment that is wrong.

- **An empty array:** true; nothing installed.
- **No domain reaching 1:** true; nothing installed, not even a clamp.
- **A value above `n`:** impossible, since `v` needs `1, …, v − 1` at distinct
  earlier positions. The clamp below makes that explicit.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `SeqPrecedeChain` | ✓ `fzn_seq_precede_chain_int` | `unsupported`[^xnoval] | ?[^gcspy] | ✓ `seq_precede_chain` | |
| reified | `unsupported`: the stdlib's `fzn_seq_precede_chain_int_reif` is an `abort` in 2.9.7 and 2.10.1, so `b <-> seq_precede_chain(x)` fails to flatten | n/a | — | — | |

[^xnoval]: XCSP3 has no `seq_precede_chain`. Its nearest form, `precedence`
    without a `values` list, is reported unsupported (issue #150's phase 2b);
    see [`value_precede.md`](value_precede.md).

[^gcspy]: `gcspy` binds nothing in this family.

### Options

`None.`

### Variable kinds and views

As [`value_precede.md`](value_precede.md). The clamp is `define_bound` on each
variable, which works for a view, and the `seq_precede_chain_constraint_view_mixed`
lane runs the test's shapes with views mixed in.

### Reification

`None.`

### Relation to other families

- **Decomposes into:** [`ValuePrecede`](value_precede.md) over the chain
  `1..m`, where `m = min(n, max ub(x))`, carrying this constraint's ID. It
  must: `ValuePrecede` keys its labels and its flags on the ID, and two chains
  installed as unnamed children collided, which is how #449 came to be.
- **Child constraints:** that `ValuePrecede`, and nothing else.
- **Shares code:** none.
- **Presolvers:** none reads it.

## The proof model

### OPB encoding

**It is definitional:** every row is the constraint's meaning (the clamp
included, as below) or an auxiliary's definition. Two parts.

1. **The clamp**, for each variable whose declared upper bound exceeds `n`:
   ```
   x_i ≤ n                                  unlabelled
   ```
   written by `Propagators::define_bound`, which returns early, writing
   nothing, for a variable already bounded by `n`. **It is part of the
   definition**, not a derived consequence: the chain stops at `m ≤ n`, so the
   chain's rows say nothing about a value above `n`, and without the clamp such
   a value would satisfy the OPB while breaking the constraint. Nor could the
   proof derive it from the chain. Deleting the clamp rows from the OPB makes
   VeriPB reject the first clamp inference as not RUP (the fact-check's
   evidence), and deriving it would need the chain up to the largest declared
   bound, which depends on width.
2. **`ValuePrecede`'s encoding** over the chain `1..m`: see
   [`value_precede.md`](value_precede.md). With `m` up to `n`, that is `Θ(n²)`
   rows and `Θ(n³)` literal occurrences, dominated by the existence rows.

Measured whole-OPB size for `x ∈ 1..n` (`tmp/fd-ordering/bench/spc_gcs.cc`):
433 rows at `n = 7`; 3,319 rows and 424 KB at `n = 20`; 13,039 rows and 2.1 MB
at `n = 40`; 51,679 rows and 11.2 MB at `n = 80`. Those counts include the
variables' literal layer: at `n = 80`, 25,759 rows are this family's (12,959
labelled `@c`, 12,800 the `pge` flags' `@v` rows) and 25,920 the literal
layer's `@i`. **Independent of width**, because the chain is capped at
`m ≤ n`: over `−W..W` with `n = 4` it is 155 rows at `W = 10`, `10⁹` and
`2⁶¹ − 1`, the bytes growing only with the bit width, 15 KB to 92 KB
(`probes/spcwide.cc`).

### Labels

The chain's, as [`value_precede.md`](value_precede.md). The clamp rows carry
none, and nothing cites them by label.

### Cake conformity

`scp_chain_seq_precede_chain_{sat,nonexact_sat,unsat}` chain-verify, in `none`
mode, for `value_precede`'s reason (#358's literal-encoding divergence) plus
one of its own: `cake_pb_cp` emits a clamp row `@c[id][<i>cl]` for **every
position** whenever `m ≥ 1`, while the solver writes one, unlabelled, only for
each variable whose declared upper bound exceeds `n`. On the test shape
`(1..4, 1..4, 1..100, 1..4)` that is one row against cake's four. None of the
three SCP cases' domains exceeds `n`, so there the solver writes no clamp at
all; cake's rows are redundant there and the chain verifies. The fact-check
also ran clamping inputs through workflow 2 (`wide.scp`, `1..9` at `n = 3`,
and a mixed one), which pass in `none` mode.

### Proof-time state

The chain's, plus nothing: the clamp is an OPB row, and its initialiser's
inference is a RUP against that row.

## The implementation

### Initialisation and global data

`prepare()` does all the work, once, from the initial domains: the largest
declared upper bound `u`, `m = min(u, n)`; if `u > m`, it calls
`define_bound(x_i ≤ n)` for every `i`, which writes a row and installs an
initialiser only for the variables whose upper bound exceeds `n`; then, if
`m ≥ 2`, a `ValuePrecede` over `1..m`. It returns false, so this class installs
no propagator of its own.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| clamp initialiser, per clamped variable | — (once, at the root) | n/a | 1 | that variable's declared upper bound above `n` | n/a | n/a |
| the chain's pair propagators | see [`value_precede.md`](value_precede.md) | derived: every variable | `value_precede` rule 1 | `m ≥ 2` | never claims | as there |

The chain `1..m` has no repeated value, so `value_precede`'s rule 2 never fires
here.

### Mutable state and incrementality

`None` of its own.

### Interior values and optional pruning

**Offers.** `None.` **Observes.** As `ValuePrecede`: holes in every variable,
truthfully, since a hole at a chain value moves the first possible occurrence.

### Robustness and limits

**Unbounded domains.** Fine, because the chain is capped at `m ≤ n`: however
wide the declared domains, everything built from the chain is bounded by `n`,
with or without a clamp (`−2⁶¹..3` at `n = 4` has none, and is fine). Checked
by full enumerations with verifying proofs: `1..2⁶¹ − 1` at `n = 5`, 52
solutions, and `−2..2⁶¹ − 1` at `n = 4`, 372, matching brute force
(`probes/spcfull.cc`). The `±(2⁶¹ − 1)` probe above stops at 1,000 solutions,
so it checks a partial proof only.

**Negative values and zero.** Unconstrained, and tested: a fixed shape over
`−2..3`, constant entries of 0 and −1, and the probe over `−W..W`.

**Degenerate shapes.** The test's degenerate runs cover an empty array, all
constants, and a leading value other than 1. A **repeated variable** is a pair
of positions, checked by enumeration in the duplicate runs.

**Overflow.** `n` as an `Integer`, and the chain `1..m`; nothing near the
limits.

### Interval efficiency

**Fine at any width,** because the chain is capped at `m ≤ n`.

1. **The propagation side.** The chain's: membership tests, no value walks.
   The clamp is one bound per clamped variable, once.
2. **The reason side.** The chain's whole-scope generic reason, by hole run.
   The clamp's inference has no reason.
3. **The proof side.** One line per removal, and one per clamped variable.
4. **The audit lane.** One row, `SeqPrecedeChain`, pinned `Clean`, but over
   **`narrow(p, 4, 0, 3)`**: four variables in `0..3`, below the array length,
   so the row never reaches the clamp. The shape that matters for width, a wide
   declared domain, is not in the lane, and neither are holes or views; the
   test's scale case reaches `1..1000` and the probes above reach `2⁶¹ − 1`,
   and both pass.

## Inference catalogue

One rule of its own, the clamp. Every other inference is
[`value_precede`](value_precede.md)'s rule 1, `t-without-earlier-s`, for the
pairs `(v − 1, v)`, `v = 2..m`, and carries the `value_precede` hint under this
constraint's ID.

### Rule: clamp-to-length

- **Infers** — `x_i ≤ n`, at the root, for each `i` whose declared upper bound
  exceeds `n`.
- **Fires when** — once, from that variable's `define_bound` initialiser.
- **Strength** — `partial`: it is a bound, and the chain tightens it further
  (position `i` can hold at most `i + 1`, which the pair propagators reach at
  their fixpoint).
- **Algorithm** — none; one bound per clamped variable.
- **Why it is true** — a value `v` at position `i` needs `1, …, v − 1` at
  distinct positions before `i`, so `v ≤ i + 1 ≤ n`.
- **Proof technique** — `RUP` against the clamp row the model carries. The
  row is part of the encoding's definition, and the proof could not derive it
  from the chain; see [OPB encoding](#opb-encoding).
- **Reason** — none.
- **Assertion** — `x_i ≤ n`, at the assertion levels with the shared
  `initial_bound` hint rather than this family's. Measured at `Definitions`,
  four variables over `−1..9`:
  ```
  a 1 ~i[x[0]][ge5] >= 1::initial_bound:;
  ```
- **Hint** — `hints::InitialBound`, shared by every `define_bound`. It carries
  no constraint ID, so a reconstructor cannot tell which constraint's clamp it
  is from the hint alone.
- **Offline reconstructibility** — `offline`: the clause is a single bound, and
  it is RUP against an OPB row.
- **Proof size** — one line per clamped variable, once.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

- **`seq_precede_chain_test`** (`seq_precede_chain_constraint`, plus
  `seq_precede_chain_constraint_view_mixed`): fixed shapes (domains equal to
  and larger than the array length, one domain up to 100, a negative range,
  constants including 0 and −1, and #254's degenerate arrays) and 16 random
  shapes per run, eight in each of the no-proofs and proofs passes (the
  generator carries over between them), of two to five variables, each a range
  with its lower bound in `0..3` and one to three wider, or a constant in
  `0..6`. In the bare lanes it adds a
  **scale case**, five variables over `1..1000`, which must find the 52
  solutions (Bell number `B(5)`) and verify, and two chains in one problem (the
  #449 regression). With and without proofs, under plain `solve_for_tests`:
  enumeration and the proof, no consistency check. Seeded.
- **Duplicate-variable runs**, bare lanes only (as are the scale and two-chain
  runs).
- **`scp_chain_seq_precede_chain_{sat,nonexact_sat,unsat}`:** see [Cake
  conformity](#cake-conformity).
- **MiniZinc:** `seqprecedechain.mzn`.
- **Audit lane:** the `SeqPrecedeChain` row, narrow.

**Runtime caps.** No lane sets or clears one, and the default caps never fire:
56 runs bare (46 data-driven, 6 duplicate-variable, 2 scale, 2 two-chain) and
46 in `view_mixed`, all complete (`GCS_TEST_MAX_SOLUTIONS=300
GCS_TEST_MAX_RECURSIONS=1500 seq_precede_chain_test --seed=1`, at `c9ceea25`).

**What the tests do not cover.**

- **Strength**, deliberately; none is claimed.
- **Holes**, and a declared domain wider than the scale case's `1..1000`.
- **Real instances.**
- **Much of the random sweep:** most random shapes are infeasible. For seeds 1
  to 6, the no-proofs pass has 7, 5, 5, 6, 6 and 5 of its 8 infeasible, and the
  proofs pass 8, 6, 6, 7, 5 and 6 (so seed 1's proof pass checks no solution at
  all; the fact-check's count).
- **`view_mixed`** skips the duplicate-variable, scale and two-chain runs.

### Benchmarks and examples

- **In the repository:** none.
- **Corpus:** 3 posts, one each in `kidney-exchange` 2019 and 2023 and
  `products-and-shelves` 2025, over arrays of 20 to 24 (`1..20` at `n = 20`
  twice, and `1..10` at `n = 24`), none of which reaches the clamp. The busiest,
  `kidney-exchange` 2019, spends 0.17 s of a 10 s run in 933,559 calls of the
  chain's pair propagators.
- **For CPU and for proofs:** the restricted-growth-string enumeration,
  `x ∈ 1..n`, which has a Bell number of solutions. It does not reach the
  clamp either (the domains stop at `n`).

### CPU performance

*Release build of `c9ceea25`; Gecode 6.3.0; fataepyc-10, boost off,
`taskset -c 4`, fixed malloc thresholds; median of five runs; wall time of the
whole solve, proofs off; 2026-09-30.* Over `x ∈ 1..n` this constraint and
Gecode's `precede(x, [1..n])` have the same solutions (`spc_gcs.cc` mode `spc`,
`spc_gecode.cc`). Gecode's `precede` is pairwise too: one Law and Lee
propagator per consecutive pair.

| n | Search | Solutions | GCS | GCS recursions | GCS propagations | GCS failures | Gecode | Gecode nodes | Gecode propagations | Gecode failures |
|---|---|---|---|---|---|---|---|---|---|---|
| 8 | first position first, smallest value | 4,140 | 0.0043 s | 5,295 | 7,957 | 0 | 0.0033 s | 8,279 | 25,025 | 0 |
| 10 | first position first, smallest value | 115,975 | 0.115 s | 142,417 | 202,084 | 0 | 0.087 s | 231,949 | 713,470 | 0 |
| 11 | first position first, smallest value | 678,570 | 0.675 s | 820,987 | 1,139,035 | 0 | 0.507 s | 1,357,139 | 4,166,076 | 0 |
| 10 | last position first, largest value | 115,975 | 1.09 s | 562,595 | 1,225,306 | 247,823 | 0.136 s | 231,949 | 1,048,360 | 0 |

On the forward search neither solver fails, so both explore the same
assignments (their node counts differ because GCS branches over every value,
Gecode in two), and GCS takes 1.3 times Gecode's time. On the backward one the
missing forcing rule costs 247,823 failures and a factor of 8.0; see
[`value_precede.md`](value_precede.md). No row reaches the clamp.

### Proof performance

*Same build and machine; VeriPB 3.0.2 with `--force-checked-deletion`.*
Enumerating all restricted-growth strings over `1..n`:

| n | Solutions | Lines, `Off` | Bytes, `Off` | VeriPB | Lines, `Inferences` | `a` lines, `Inferences` | this family's | share of `a` lines |
|---|---|---|---|---|---|---|---|---|
| 5 | 52 | 611 | 20.6 KB | 0.01 s | 429 | 156 | 29 | 18.6% |
| 6 | 203 | 2,030 | 75.4 KB | 0.04 s | 1,584 | 566 | 85 | 15.0% |
| 7 | 877 | 7,995 | 326 KB | 0.20 s | 6,596 | 2,325 | 293 | 12.6% |

"This family's" counts the `value_precede`-hinted assertions at
`Inferences`, one per removal; the rest of the `Inferences` proof's `a` lines
are the search's, backtracking and solution blocking (at `n = 5`, 75
`::backtrack` and 52 `::solx_block` against 29 `::value_precede`). Besides
its `a` lines, that proof has the search's `solx` and `del` lines (52 and 89 at
`n = 5`), one `rup`, and no `pol` or `red`. The fully justified `Off` proof
carries the search's `solx`, backtracking and deletions, the root's RUPs, the
literal definitions (`pol` and `red` lines), and the range-literal RUPs this
family's reasons cause.

**Assertion levels.** On `x ∈ 0..4`, `n = 6`, `Off` verifies and `Definitions`,
`Links` and `Inferences` are accepted under assertions. On `x ∈ −1..9`,
`n = 4`, `Off` verifies, `Definitions` and `Inferences` are accepted under
assertions, and `Links` fails, at a `solx` (`probes/runfam.sh`). Where a
mode above `Off` is accepted, VeriPB 3.0.2 reports `s UNDER ASSERTIONS`, not
`VERIFIED`, because the family's inferences are `a` lines there, so only `Off`
checks the family. The `Links` failure is a `solx` step, not a row of this
family or of the clamp: the fact-check found `Links` failing at `−1..3` and
`−1..4` with `n = 4`, where there is no clamp, accepted under assertions at
`0..9`, `1..9` and `1..100`, where there is, and failing for `NotEquals` over
`0..3` too.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` (The one `Links` failure is the generic one; see [Proof
performance](#proof-performance).)

### Known limitations

`value_precede`'s: it does not force a value it could, and each proof line
names the whole array. Separately, the chain is propagated pair by pair, which
is weaker than chain GAC even when each pair is GAC. The fact-check ran three
plain sweeps of 20,000 instances: 47, 42 and 44 had a pairwise-GAC fixpoint
that is not GAC, and 1,046, 1,004 and 1,017 a root weaker than the
pairwise-GAC fixpoint. Three sweeps with views and repeated variables gave
21, 19 and 20, and 624, 624 and 630 (`factcheck/seq_precede_chain/`,
`plain_sweep.txt` and `mixed_sweep.txt`). And the encoding is cubic in the
array length, in terms.

### Next steps

1. **Everything in [`value_precede.md`](value_precede.md)'s next steps,**
   especially the forcing rule, which this constraint needs most: symmetry
   breaking on a set partition is where a backwards search meets it. It makes
   each pair GAC over distinct variables, not the chain: chain GAC needs an
   algorithm of its own.
2. **Correct the class comment**: `v = 1` needs nothing, and `v` needs `v − 1`
   earlier positions, not `v` (header and `seq_precede_chain.cc`). Trivial; not
   worth an issue.
3. **Give the clamp a hint that names the constraint,** or label the rows as
   cake does. Small, and only for a reconstructor's benefit.

## Prior art

As [`value_precede.md`](value_precede.md): Law and Lee (CP 2004) for the pair
algorithm, and `cake_pb_cp` for the encoding and its clamp.

## Further reading

- [`value_precede.md`](value_precede.md): everything this constraint installs.
