# `ValuePrecede`: each value in a chain first appears before the next one does

> **Maturity** production ·
> **Audited** 2026-09-29 at `c9ceea25` ·
> **Open issues** none filed by this audit yet; see [Next steps](#next-steps)
> for what it would file. Already open and touching this family: #833 (the
> large-domain policy), #868 (cross-solver comparisons; this document gives
> one, by hand). Tracked under #871.

`ValuePrecede(chain, vars)` says that for each consecutive pair `(s, t)` of
`chain`, every occurrence of `t` in `vars` has an occurrence of `s` strictly
before it. With a two-value chain it is `value_precede`; with a longer one it is
`value_precede_chain`. It is the standard symmetry-breaking constraint for
interchangeable values, and [`seq_precede_chain`](seq_precede_chain.md)
installs nothing but this. One propagator per consecutive pair, a proof-only
first-occurrence index per chain value in the encoding, and one RUP per
removal.

Three things to know before touching it.

- **It is not generalised arc consistent, or even `bounds(Z)`.** The
  propagator removes `t` from every position with no possible `s` before it,
  which is half of Law and Lee's algorithm. The other half is missing: when a
  position is fixed to `t` and only one earlier position can still hold `s`,
  that position must be `s`. Branching last position first on the largest
  value, enumerating the restricted-growth strings of length 10 takes 247,823
  failures here, and none in Gecode.
- **Its reason is the whole scope.** Every removal names every variable's
  bounds and holes, 8 to 13 literals on a six-variable probe, where the
  earlier positions' `≠ s` literals would do.
- **Its encoding is quadratic in the array per chain value.** Each chain value
  gets a proof-only index, `n` reified flags, `n` upper-bound rows and `n`
  existence rows of up to `n` terms each. That matches `cake_pb_cp` label for
  label, and it is width-independent.

## What it is

### Semantics

For `chain = (c₀, …, c_{k−1})` and `vars = (x₀, …, x_{n−1})`, `ValuePrecede`
holds when, for every `j ≥ 1`, each `i` with `x_i = c_j` has some `i' < i` with
`x_{i'} = c_{j−1}`. The convenience constructor `ValuePrecede(s, t, vars)` is
the two-value chain.

- **A chain of fewer than two values** imposes nothing. `prepare()` returns
  false, so nothing is installed and no OPB row is written.
- **An empty array** is vacuously true; the encoding writes nothing for it.
- **A value in the chain that no domain holds** is fine: its index is pinned
  to the "absent" sentinel.
- **Repeated values in the chain** are accepted, and read as the conjunction of
  the pairs. `(s, s)` says `s` never appears (it would need an earlier `s`
  before its first occurrence). `(1, 2, 1)` asks for `1 ≺ 2` and `2 ≺ 1`, so
  neither appears. MiniZinc's standard-library decomposition reads a repeated
  chain through a different route (it maps each value to the sum of its chain
  positions), but on six chains over four variables in `0..3`, four of them
  with a repeated value, that decomposition solved by Gecode (whose MiniZinc
  library does not redefine `value_precede_chain_int`), this class and a
  brute-force pairwise count all agree (`tmp/fd-ordering/mzn/repchains.sh`,
  output in `repchains.out`: e.g. `[1, 2, 1]`: 16 solutions each;
  `[2, 1, 2, 3]`: 1; the unrepeated `[3, 1, 2]`: 51).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `ValuePrecede` | ✓ `fzn_value_precede_int`, `fzn_value_precede_chain_int` | ✓ `precedence` with a `values` list[^xprec] | ?[^gcspy] | ✓ `value_precede` (chain, then variables) | |
| reified | `decompose`: the stdlib's `fzn_*_reif` | n/a | — | — | no class exists |
| `seq_precede_chain` | see [`seq_precede_chain.md`](seq_precede_chain.md) | | | | posts this class |

[^xprec]: `buildConstraintPrecedence` supports only `covered = false` with an
    explicit `values` list. `covered = true` and the form without values (whose
    chain would come from the domains' union) are reported unsupported, the
    latter as issue #150's phase 2b.

[^gcspy]: `gcspy` binds nothing in this family. CPMpy's side was not checked.

The set-valued forms (`value_precede_set`, `value_precede_chain_set`) do not
apply: the solver has no set variables. Positions matter here but no value is
an index, so an array indexed from something other than 1 cannot be
mistranslated; `valueprecede.mzn` and `valueprecedechain.mzn` cover the glue.

### Options

`None.`

### Variable kinds and views

Plain variables, constants and views are all accepted. The propagator reads
`in_domain(x, s)` and `in_domain(x, t)` and removes a value, which is the same
for any kind. The proof handles views too: the encoding names each view's
`x_i = v` through the underlying variable's literal, and the
`value_precede_constraint_view_mixed` lane runs the suite's shapes with views
mixed in.

### Reification

`None.` MiniZinc's reified forms reach the solver as the standard library's
decomposition. None appears in the corpus.

### Relation to other families

- **Decomposes into it:** [`seq_precede_chain`](seq_precede_chain.md), which
  clamps its variables and then installs a `ValuePrecede` over the chain
  `1..m`, carrying its own constraint ID so that two chains in one problem do
  not share flags (#449).
- **Child constraints:** none.
- **Shares code:** none. The reason is the generic one from `reason.hh`.
- **Presolvers:** none reads it.

## The proof model

### OPB encoding

This is `cake_pb_cp`'s encoding (`cp_to_ilp_lexicographicalScript.sml`),
reproduced row for row. For each **distinct** value `v` of the chain, with `n`
the length of `vars`:

```
pos[v] ∈ 0..n                         proof-only, a bit sum; n means "v is absent"
pos[v] ≤ n                                              @c[id][ubn_v]
[pos[v] ≥ k]  ⇔  pos[v] ≥ k,  k = 1..n                  n fully reified flags
for i in 0..n-1:
  x_i = v  ⇒  pos[v] ≤ i                                @c[id][<i>ub_v]
  [pos[v] ≥ i+1]  ∨  x_0 = v ∨ … ∨ x_i = v              @c[id][<i>ex_v]
```

The upper-bound rows cap `pos[v]` at the first occurrence and the existence
rows push it up to it, so `pos[v]` is exactly the index of `v`'s first
occurrence, or `n`. Then for each consecutive pair `(s, t)`, numbered `j`:

```
s ≠ t:   ¬[pos[t] ≥ n]  ⇒  pos[t] − pos[s] ≥ 1          @c[id][<j>pr]
s = t:   pos[s] ≥ n                                     @c[id][<j>nos]
```

**It is definitional.** Every row is the constraint's meaning or the definition
of an auxiliary.

**Size.** Per distinct chain value, `n` reified flags, `2n + 1` rows, and
`n(n + 1)/2 + n` literal occurrences in the existence rows; plus one row per
pair. So `Θ(k·n)` rows and `Θ(k·n²)` terms for `k` distinct chain values. It is
**independent of domain width**, and mentions only the `x_i = v` literals of
chain values.

### Labels

The labels are `cake_pb_cp`'s, value-keyed since #604 so that no two rows share
one. No rule cites a row by label: every inference is a plain RUP.

### Cake conformity

`scp_chain_value_precede_{sat,nonexact_sat,unsat}` all chain-verify, in `none`
mode. Measured under #604: the label sets are **identical** to cake's, and every
row of the constraint's own compares equal (`opbdiff --match-labels`: 60
matching, 3 differing, 0 only on either side, on `value_precede_sat`). The three
differing rows are the variables' boundary reifications `@i[X][ge0][r]`, the
lazy-versus-eager literal-encoding divergence (#358) that keeps every case in
that section `none`. The `pos[v] ≤ n` row exists because cake added it upstream
(`f43d14aa8`): without it an absent value leaves `pos[v]`'s top bits free when
`n` is not `2^w − 1`, and a solution would not pin the auxiliary.

### Proof-time state

- **At the root:** nothing emitted by the family.
- **Lazily:** the `pos[v] ≥ k` atoms beyond the reified flags are introduced in
  the proof on first use, as for any proof-only integer variable.
- **Deleted:** nothing.
- **Naming:** `pos[v]`'s bits are `v[id][<v>_<b>][pos]` and its flags
  `v[id][<v>_<k>][pge]`, cake's value-keyed names, so an external tool finds
  them by the constraint ID and the value.
- **Proof-only auxiliaries determined on a solution:** yes, and that is the
  load-bearing property. On a full assignment the upper-bound and existence
  rows fix `pos[v]` to the first occurrence or `n`, the bound row caps it, and
  unit propagation settles every bit.

## The implementation

### Initialisation and global data

`prepare()` returns whether the chain has two values. `define_proof_model()`
builds the encoding above. There is no initialiser; nothing is computed once at
the root.

### Propagator inventory

One propagator per consecutive pair of the chain.

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| pair `(s, t)`, `s ≠ t` | `on_change`, every variable | derived: **every variable** | 1 | a chain of two or more | never claims; is, over distinct underlying variables | yes: when `s` is absent everywhere, or the first position that could hold `s` is fixed to it |
| pair `(s, s)` | as above | as above | 2 | a repeated adjacent chain value | never claims; is not | only when `s` is absent everywhere: the fixed-to-`s` exit cannot fire, since the call has just removed `s` at `α` |

**Holes affect: every variable, and truthfully.** The pass reads
`in_domain(x_i, s)` and `in_domain(x_i, t)`, so removing `s` from strictly
inside a domain can move the first possible `s`, and change what is removed.
The column is per variable, so it cannot say that only two values of each
domain matter; that is over-reporting only for the values other than `s` and
`t`, and over-reporting only keeps somebody else's pruning on.

**Idempotence.** Never claimed. For `s ≠ t`, over distinct underlying
variables, a second call would do nothing: removing `t` cannot move the first
possible `s`. Two views of one variable break that, as `propagators.cc`'s own
note on aliasing says: with positions `[x + 1, x, y]`, chain `(1, 2)`,
`x ∈ 1..3` and `y ∈ 0..2`, the first call removes 2 from the first two
positions, which fixes `x = 3` and so moves the first possible 1 to `y`, whose
2 only a second call removes. For `s = t` a second call always has work: each
call removes `s` from the first position that has it, which moves that
position on, so emptying the array of `s` takes one call per position.

### Mutable state and incrementality

`None.` Each call scans from the front for the first possible `s` and then
prunes `t` up to it. A chain of `k` values is `k − 1` independent propagators,
each making `O(n)` membership tests per call, and each test linear in its
domain's runs (see [Interval efficiency](#interval-efficiency)). Keeping the
first possible `s` as backtrackable state would make a call `O(1)` when nothing
before it changed; on the corpus the family's calls cost 0.18 µs each (below),
so there is nothing to buy.

### Interior values and optional pruning

**Offers.** `None.` There is one arm, and it is weaker than GAC already.

**Observes.** Holes in every variable, per the inventory: a removal of `s` from
the middle of a domain can change what this family infers. So a
`ValuePrecede` over a variable **is** a reason for another family's interior
pruning on that variable to stay on, and it says so correctly through its
`on_change` triggers.

### Robustness and limits

**Unbounded domains.** Fine: the pass tests membership of two values per
position, whatever the width, and the encoding mentions only chain values.

**Negative values and zero.** Tested (`{−1, 1}` over `−1..1`). The chain may
hold integers of either sign, within `±(2⁶⁰ − 1)` since #1215 (see
[Overflow](#robustness-and-limits)).

**Degenerate shapes.** An empty array, a single constant, all constants in and
out of order, a chain of zero or one value, and chain values in no domain are
all in `value_precede_test` (per #254). A **repeated variable** in `vars` is an
ordinary pair of positions, and the duplicate runs (`{x, x, y}` and friends)
check it by enumeration: the semantics is over positions, so a repeat is not a
special case.

**Overflow.** There is something to guard. The pass does no arithmetic on
values, and the encoding's constants are positions, at most `n`, but the chain
values go into equality literals and membership tests, and those translate a
value through a view or into the literal layer. At `c9ceea25`, with
`x ∈ 0..2`:

- `ValuePrecede{INT64_MIN, 2, {x + 1}}` throws `Integer overflow:
  -9223372036854775808 - 1` with proofs off, in `State::in_domain`'s
  translation of the chain value through the view. With proofs on it throws
  the same, earlier, in `define_proof_model`, where the upper-bound row's
  literal `x + 1 = INT64_MIN` is translated to `x = INT64_MIN − 1`
  (`simplify_literal.cc`). Its solutions are `x = 0` and `x = 2`.
- `ValuePrecede{INT64_MIN, 1, {x}}`, with no view, enumerates those two
  solutions with proofs off, but with proofs on throws `Integer overflow:
  --9223372036854775808` in `define_proof_model`, while defining the literal
  `x = INT64_MIN` for the upper-bound row.
- `ValuePrecede{INT64_MIN, 1, {−x}}` throws `Integer overflow:
  --9223372036854775808` with proofs off and on, because the negated view
  negates the chain value: in `State::in_domain` with proofs off, and with
  proofs on earlier, in `define_proof_model`, where `simplify_literal.cc`
  translates the upper-bound row's literal on `−x` to one on `x`.
- `ValuePrecede{−10, 1, {x + (INT64_MAX − 2), y}}`, with `y ∈ 0..2` too, a
  moderate chain value through an extreme but representable view offset,
  throws `Integer overflow: -10 - 9223372036854775805` with proofs off, in
  `State::in_domain`, and with proofs on, earlier, in `define_proof_model`,
  where `simplify_literal.cc` translates the upper-bound row's literal on the
  view to one on `x`.

So it takes a chain value that, read through its position's view, lands at or
near an end of `Integer`, or past it. Past it overflows with proofs off too
(`State::in_domain`). At or near it overflows only with proofs on, where the
literal definitions step past it (`v + 1`, or negating `INT64_MIN`).
`ValuePrecede{INT64_MAX, 1, {x}}`, and
`ValuePrecede{0, 1, {x + (INT64_MIN + 2), y}}`, whose translated values fit,
both enumerate with proofs off and throw `Integer overflow:
9223372036854775807 + 1` with proofs on, while one step further in,
`ValuePrecede{0, 1, {x + (INT64_MIN + 3), y}}` is fine both ways. A wide
domain alone does not. Found in review and
filed as #1188; fixed by #1215 (merged 2026-10-04), which refuses a chain value
outside `±(2⁶⁰ − 1)` at construction, together with #1214 (the same day), which
refuses a view offset outside it. Probes:
`tmp/fd-codex-1005/ordering/probes/ovf.cc`,
`tmp/fd-codex-1005/ordering/factcheck/ovf3.cc`,
`tmp/fd-codex-1005/ordering/factcheck2/ovf.cc` and
`tmp/fd-codex-1005/ordering/factcheck3/vp{3,4}.cc`.

### Interval efficiency

**Fine at any width.** There is no loop over values in `value_precede.cc`.

1. **The propagation side.** Up to about `2n` `in_domain` tests per pair per
   call (the scan for `α`, then the pruning loop up to it). Each test is
   `IntervalSet::contains`, which scans the domain's interval list from the
   front and stops at the first interval reaching the value, so it is linear
   in the number of runs below the value, not logarithmic. Each removal is an
   `IntervalSet::erase`, linear in the runs the same way. A call is `O(n)`
   tests and up to `O(n · r)` work, counting the removals, for `r` the most
   runs in any domain: `O(n)` on interval domains. No value walk.
   Making the shared membership test logarithmic would help every caller, but
   should wait for a measurement that it matters here.
2. **The reason side.** The reason is `generic_reason(vars)`, built once at
   install and materialised only when a proof asks for it. It names each
   variable's two bounds and **one literal per hole run**, not per value (since
   #935). It is not minimal: see rule 1.
3. **The proof side.** One RUP line per removal. No second form, so no gate.
4. **The audit lane.** One row, `ValuePrecede`, pinned `Clean`:
   `ValuePrecede{1, 2, wide(p, 4)}`, four plain variables over `0..10⁹`. It
   does not vary holes (which the reason would name run by run), chain length,
   a repeated chain value, or views. None of those has a width-proportional
   site to find, so the gap is not one that could be hiding anything.

## Inference catalogue

Two rules: the removal of `t` behind the first possible `s`, and its special
case for a repeated chain value. A conflict is not a third rule: it arises when
the value to remove is the only one left, and the tracker asserts the attempted
literal with its reason.

Four facts hold for both.

**Each is a single RUP, and the procedure is ours.** No published justification
procedure covers value precedence. The argument, spelled out under rule 1, is a
chain of the facts in
[`justification-techniques.md`](../justification-techniques.md): the removal
stated under its reason (Theorem 2.6), opposing bounds on one bit sum
(Theorem 2.7), and a bound crossing a difference row with `B = 1`
(Theorem 2.9). Unit propagation walks it unaided, so the family writes one
line per removal and no lemma.

**The reason is the whole scope.** Every rule passes `generic_reason(vars)`:
each variable's bounds and holes. It is sound, since it contains everything the
RUP needs, but it names every position after the one being pruned as well.

**There is one wire form.** `hints::ValuePrecede`, `(constraint_id <id>)`, no
subhint. Measured on the probe enumerations: 63 annotations for a two-value
chain over six variables in `0..3`, 64 for a three-value chain, all that form.

**No justification reads `state`,** and there is no `JustifyExplicitly`.

### Rule: t-without-earlier-s

- **Infers** — `x_i ≠ t`, for a pair `(s, t)` with `s ≠ t`, at every position
  `i ≤ α`, where `α` is the first position whose domain holds `s`; at every
  position when no domain holds `s`.
- **Fires when** — any variable's domain changes, in that pair's propagator.
- **Strength** — `partial`: on its own pair, every value of `t` without an
  earlier possible `s` is removed, and nothing else. Law and Lee's algorithm
  adds the other half: if some position `β` is fixed to `t` and `α` is the only
  position before `β` that can hold `s`, then `x_α = s`. Without it the pair
  is neither GAC nor `bounds(Z)`. The smallest witness: two positions, chain
  `(0, 1)`, `x₀ ∈ {0, 2}`, `x₁ = 1`; `x₁ = 1` needs a 0 before it, so `x₀ = 0`,
  but the root keeps `x₀ ∈ {0, 2}`, so its upper bound is unsupported
  (`probes/vpwit.cc`). Checked by brute force at the root over random domains
  with holes (`tmp/fd-ordering/ordcheck.cc`, modes `vp` and `vpc`, seed 1, as
  `ordcheck vp 2000 1`): of 2,000 two-value instances, 13 fail GAC, 13
  `bounds(D)` and 12 `bounds(Z)`; of 2,000 chains of two to four values, 25
  fail each. No solution was lost in any of them. Chains are weaker again,
  since the pairs are propagated separately.
- **Algorithm** — scan for `α`, then remove `t` from positions `0..α`. `O(n)`
  membership tests.
- **Why it is true** — an occurrence of `t` at `i` needs an `s` at some
  `i' < i`, and no position before `α` can hold `s`. At `α` itself, "before"
  excludes `α`, so `t` there has no `s` before it either.
- **Proof technique** — `RUP`, our own procedure, with these preconditions:
  the reason fixes `x_{i'} ≠ s` for every `i' < i`, and the encoding has the
  upper-bound, existence and precede rows above. The removal is stated under
  the reason, so by Theorem 2.6 it is enough to refute `x_i = t` with the
  reason assumed. The upper-bound row for `t`, half-reified on `x_i = t`, then
  gives `pos[t] ≤ i` by unit propagation; since `i < n`, that bound and the
  flag's reification `pos[t] ≥ n` are opposing bounds on one bit sum
  (Theorem 2.7), so `[pos[t] ≥ n]` is false, which switches on the precede row
  `pos[t] − pos[s] ≥ 1`. Meanwhile the existence row
  `[pos[s] ≥ i] ∨ x₀ = s ∨ … ∨ x_{i−1} = s` has every disjunct but the flag
  false under the reason, so `[pos[s] ≥ i]` holds and its reification gives
  `pos[s] ≥ i`. Then the lower bound `pos[s] ≥ i`, the difference row
  `pos[t] − pos[s] ≥ 1` and the upper bound `pos[t] ≤ i` are Theorem 2.9's
  contradictory triple, with `B = 1`. When no position holds `s` the same
  chain runs with the existence rows forcing `pos[s] ≥ n` instead, against the
  same difference row and `pos[t] ≤ i < n`.
- **Reason** — `generic_reason(vars)`: every variable's bounds and hole runs.
  **Not minimal.** The derivation uses only `x_{i'} ≠ s` for `i' < i`, and the
  reason also names position `i` itself and every later one. On the six-variable
  probe the asserted clauses carry 8 to 13 literals. Built lazily, so it costs
  nothing with proofs off.
- **Assertion** — `x_i ≠ t ∨ ¬reason`. Measured at `Inferences`, removing
  `t = 2` from `x₂` with `s = 1` absent from the first two positions:
  ```
  a 1 ~i[x[2]][eq2] 1 ~i[x[0]][eq0] 1 ~i[x[1]][eq0] 1 ~i[x[2]][ge0] 1 i[x[2]][ge4] 1 ~i[x[3]][ge0] …
    >= 1::value_precede:((constraint_id _1));
  ```
  (In that run the two earlier positions had been fixed to 0, which is how
  their `≠ 1` shows up in the reason, as `= 0`.)
- **Hint** — `hints::ValuePrecede`: `originator`, the `ConstraintID`.
- **Offline reconstructibility** — `offline`. The clause names the removed
  literal, and a plain RUP against the database finds the rest; nothing needs
  choosing. A hinted RUP would need the rows for `s` and `t`, which the value-
  keyed labels name directly.
- **Proof size** — one line per removal, of `O(n + hole runs)` literals, for
  the reason. Width-independent.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` No mutation lane. The corruption to try: drop
  one earlier position's `≠ s` from the reason; the RUP should then fail,
  since that position's existence disjunct is no longer false.

### Rule: repeated-value-absent

- **Infers** — `x_α ≠ s` for a pair `(s, s)`, at the first position `α` whose
  domain holds `s`, once per call.
- **Fires when** — any variable's domain changes, in that pair's propagator.
  It is the same code as rule 1, with `t = s`: pruning up to `α` meets `s` only
  at `α`.
- **Strength** — `GAC` on its own pair, eventually: the pair means `s` never
  appears, and the propagator runs until it has removed `s` everywhere. It
  takes one call per position to get there, since each call removes only the
  first.
- **Algorithm** — as rule 1. `O(n)` membership tests per call (see [Interval
  efficiency](#interval-efficiency)), `n` calls to finish.
- **Why it is true** — the first occurrence of `s` would need an earlier `s`.
- **Proof technique** — `RUP`, ours. Under `x_α = s`, the upper-bound row
  gives `pos[s] ≤ α < n`, against the `nos` row `pos[s] ≥ n` (Theorem 2.7).
- **Reason** — `generic_reason(vars)`, as rule 1, and further from minimal:
  the derivation needs no reason at all.
- **Assertion** — `x_α ≠ s ∨ ¬reason`. Measured at `Inferences`:
  ```
  a 1 ~i[x[1]][eq2] 1 ~i[x[0]][ge0] 1 i[x[0]][ge4] 1 i[x[0]][eq2] 1 ~i[x[1]][ge0] …
    >= 1::value_precede:((constraint_id _1));
  ```
- **Hint** — `hints::ValuePrecede`: `originator`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per removal.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

- **`value_precede_test`** (`value_precede_constraint`, plus
  `value_precede_constraint_view_mixed`): 25 fixed shapes (two-, three- and
  four-value chains, values in no domain, the first position forced to `t`,
  chain values out of domain order, repeated chains `{1, 2, 1}` and `{1, 1}`,
  empty and one-value chains, negative values, constants mid-array, #254's
  degenerate arrays) and eight random ones of two to five variables. Each runs
  with and without proofs under plain `solve_for_tests`: full enumeration and
  the proof, but **no consistency check**, which is right for a propagator
  that makes no GAC claim. VeriPB runs when on the path. Seeded.
- **Duplicate-variable runs**, bare lanes only: repeated positions, by
  enumeration.
- **`scp_chain_value_precede_{sat,nonexact_sat,unsat}`:** see [Cake
  conformity](#cake-conformity).
- **MiniZinc:** `valueprecede.mzn`, `valueprecedechain.mzn`.
- **XCSP3:** `precedence.xml`.
- **Audit lane:** the `ValuePrecede` row.

**Runtime caps.** No lane sets or clears one, and the default caps never fire:
72 runs bare and 66 in `view_mixed`, all complete (`GCS_TEST_MAX_SOLUTIONS=300
GCS_TEST_MAX_RECURSIONS=1500 value_precede_test --seed=1`, and with
`--view-position=mixed`, at `c9ceea25`).

**Tightness:** no mutation lane.

**What the tests do not cover.**

- **Strength**, deliberately: no level is claimed, so none is checked. The
  missing forcing rule is invisible to the suite.
- **Holey initial domains.** Every tested domain starts as an interval. Holes
  do arise during the tests: the propagator's own removals of `t` can be
  interior (removing 2 from `0..3` at the root leaves one), a longer chain's
  other pair propagators make holes that this pair then reads, and the shared
  test brancher rejects random intervals
  (`value_order::reject_random_interval`). Under the branching pair of
  `--seed=1` (`variable_order::random(p, 1)`, `reject_random_interval(2)`), a
  three-variable `ValuePrecede{1, 2, …}` over `0..3` has a hole at all 40 of
  its trace callbacks, from the root on; across seeds 1, 2, 3, 7 and 42 it is
  29 to 40 of 36 to 40 (`tmp/fd-codex-1005/ordering/probes/holes.cc` and,
  for the seed range, `holes_seed.cc`: standalone probes, not counts from
  inside `value_precede_test`). So
  enumeration and proofs run over holey domains, though no consistency is
  checked at any node. No test posts a second constraint, so holes made by
  another constraint are not exercised.
- **Real instances:** none ported.

### Benchmarks and examples

- **In the repository:** no example or benchmark posts this class directly.
- **Corpus:** 95 `value_precede_int` posts (arrays of 22 to 144) and 125
  `value_precede_chain_int` posts (chains of one to six values, over arrays of
  2 to 1,490: `code-generator` 2020 has 83 two-value chains over two-variable
  arrays, and `community-detection` 2024 one over 1,490), across 11 of the 285
  flattened MiniZinc Challenge models: the `yumi` models (31 and 6 per
  instance), `code-generator` 2020 (95 chains), `concert-hall-cap`,
  `community-detection`, `peacable_queens` and `mondoku`.
  It never dominates a solve. Its busiest caller is `seq_precede_chain` on
  `kidney-exchange` 2019: 933,559 calls taking 0.17 s of a 10 s run, 0.18 µs a
  call (`GCS_PROPAGATOR_STATS=time`).
- **For CPU:** enumerating restricted-growth strings (below), where the number
  of solutions is a Bell number and the search order decides whether the
  missing rule matters.
- **For proof verification:** the same enumeration at `n = 5` to `7`, in
  [`seq_precede_chain.md`](seq_precede_chain.md), which posts exactly this.

### CPU performance

*Release build of `c9ceea25` (GCC 15.2.0, `-O3 -march=native`); Gecode 6.3.0,
built locally; fataepyc-10, boost off, `taskset -c 4`, fixed malloc thresholds;
median of five runs; wall time of the whole solve, proofs off; 2026-09-30.*

Enumerating every `x ∈ 1..n` with `1 ≺ 2 ≺ … ≺ n`, the chain `1..n`
(`tmp/fd-ordering/bench/spc_gcs.cc`, mode `vpc`, and `spc_gecode.cc`, which
posts Gecode's `precede(x, [1..n])`; the forward GCS runs are in
`bench/vpc_medians.txt`, the rest in `bench/spc_medians.txt`). **Gecode is
pairwise too**: over a chain it posts one Law and Lee `Precede::Single`
propagator per consecutive pair (`gecode/int/precede.cpp`), so this compares
pairwise GAC with this family's pairwise partial propagation, not with chain
GAC, which is stronger again.

| n | Search | Solutions | GCS time | GCS recursions | GCS propagations | GCS failures | Gecode time | Gecode nodes | Gecode propagations | Gecode failures |
|---|---|---|---|---|---|---|---|---|---|---|
| 10 | first position first, smallest value | 115,975 | 0.115 s | 142,417 | 202,084 | 0 | 0.087 s | 231,949 | 713,470 | 0 |
| 11 | first position first, smallest value | 678,570 | 0.673 s | 820,987 | 1,139,035 | 0 | 0.507 s | 1,357,139 | 4,166,076 | 0 |
| 10 | last position first, largest value | 115,975 | 1.09 s | 562,595 | 1,225,306 | 247,823 | 0.136 s | 231,949 | 1,048,360 | 0 |

(The last row is `SeqPrecedeChain`, which installs exactly this. The chain
`1..n` has no repeated value, so rule 2 is not exercised.)

- **In input order neither solver ever fails,** so both explore the same
  assignments (GCS branches over every value of a variable, Gecode in two, so
  their node counts differ), and GCS takes 1.3 times Gecode's time. Branching
  forwards on the smallest value never fixes a `t` before its `s` could be
  placed, so the missing rule never matters.
- **Branching backwards on the largest value exposes it.** Fixing a late
  position to a large value is exactly the case where the only earlier
  candidate for its predecessor must be forced. Gecode forces it and never
  fails; GCS finds out 247,823 times, and takes 8.0 times as long. Where a model
  sits between the two depends on its search, which is why this is a
  strength-and-cost item rather than only a strength one.

### Proof performance

See [`seq_precede_chain.md`](seq_precede_chain.md), whose probe is this
constraint over the chain `1..n`. The short version, at `n = 7`: the
fully-justified proof is 7,995 lines and verifies in 0.20 s, of which **293
lines (3.7%) are this family's**. The rest is the enumeration's own. The OPB is
433 rows at `n = 7`, and grows as `Θ(k·n)` rows and `Θ(k·n²)` terms.

**Assertion levels.** At `Off` every probe proof verifies (`probes/runfam.sh`:
two- and three-value chains, and `(2, 2)`). At `Definitions` and `Inferences`
VeriPB accepts each under assertions (`s UNDER ASSERTIONS`, not `VERIFIED`),
since this family's inferences are `a` lines there, so only `Off` checks the
family. At `Links` the two-value and three-value chains are accepted under
assertions, and `(2, 2)` is not. That failure is at a `solx` step, on a
constraint of the shared literal layer for `x[2]`, not a `value_precede` row:
it is generic, and other families' probes fail at `Links` the same way. Of
the `Inferences` assertions on the two-value probe, 63 of 4,937 carry this
family's hint; the rest are the search's.

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is justified at `Off`, and the propagator is the same
with proofs on or off. (One probe proof fails at `Links`, in the shared literal
layer, not in this family: see [Proof performance](#proof-performance).)

### Known limitations

- **It does not force a value it could.** When a position is fixed to the later
  value of a pair and only one earlier position can still hold the earlier
  value, a generalised arc consistent propagator would fix that position. This
  one waits for search to find out, which on a backwards search can cost
  hundreds of thousands of failures.
- **A chain is propagated pair by pair,** so it is weaker again than a
  chain algorithm would be.
- **Its proofs name the whole array in every step,** which makes each line
  `O(n + hole runs)` literals long.

### Next steps

1. **Add Law and Lee's forcing rule.** When a position `β` is fixed to `t`, and
   the only position before `β` that can hold `s` is `α`, infer `x_α = s`.
   Tracking the second possible position of `s`, as their algorithm does, makes
   it `O(n)` tests per call like the rest. The proof is a RUP of the same shape
   as rule 1: under `x_α ≠ s`, the existence row for `s` at `β − 1` has no true
   disjunct, and `x_β = t` gives the contradiction. Filed as #1145. It would
   make each pair GAC over distinct variables (the rule-1-plus-forcing closure
   matches brute force on 30,000 distinct-variable pairs, and differs on 182 of
   the 23,174 trials that repeat a variable:
   `factcheck/value_precede/forcing_gac.py`). A chain needs a chain algorithm
   to go further: pairwise GAC misses `x₀ = 1` in chain `(1, 2, 3)` over
   `{0, 1}, {0, 2, 3}, {2, 3}`.
2. **Give each removal its minimal reason,** `{x_{i'} ≠ s : i' < i}`, as a lazy
   reason over the prefix. It shortens every proof line from `O(n)` to `O(i)`
   literals and removes the later positions from what a reconstructor sees.
   Small; worth doing with step 1, which needs its own reason anyway.
3. **Remove a repeated chain value everywhere in one call.** Rule 2 takes `n`
   calls to empty the array; one loop over all positions does it in one. Too
   small for an issue on its own.

## Prior art

Law and Lee (*Global constraints for integer and set value precedence*, CP 2004)
give the linear-time GAC algorithm for a pair, which Gecode's `precede`
implements, applying it pair by pair to a chain. Chain GAC is strictly
stronger than pairwise GAC; this audit did not confirm who first published an
algorithm for it. The encoding here is `cake_pb_cp`'s, and this family's
proof is, as far as this audit knows, the first certified value-precedence
propagator; what is certified is the weaker half of Law and Lee.

## Further reading

- [`seq_precede_chain.md`](seq_precede_chain.md): the one caller, its clamp, and
  the measurements this document borrows.
- [`justification-techniques.md`](../justification-techniques.md): the three
  theorems rule 1 chains.
