# `ValuePrecede`: each value in a chain first appears before the next one does

> **Maturity** production ·
> **Audited** 2026-09-29 at `c9ceea25` ·
> **Open issues** filed by this audit: none left. **Fixed since the audit**:
> #1145 (the forcing half of Law and Lee was missing), by #1426, which also
> gave every inference its minimal reason and empties a repeated chain value
> in one call; see [Rule: s-forced-before-fixed-t](#rule-s-forced-before-fixed-t).
> #1188, filed from review
> (extreme chain values overflowed through views and in the proof model), by
> #1215, with #1214 for view offsets; see [Overflow](#robustness-and-limits).
> Already open and touching this family: #833 (the large-domain policy), #868
> (cross-solver comparisons; this document gives one, by hand). Tracked under
> #871.

`ValuePrecede(chain, vars)` says that for each consecutive pair `(s, t)` of
`chain`, every occurrence of `t` in `vars` has an occurrence of `s` strictly
before it. With a two-value chain it is `value_precede`; with a longer one it is
`value_precede_chain`. It is the standard symmetry-breaking constraint for
interchangeable values, and [`seq_precede_chain`](seq_precede_chain.md)
installs nothing but this. One propagator per consecutive pair, a proof-only
first-occurrence index per chain value in the encoding, and per inference a
stated helper line and a RUP.

Three things to know before touching it.

- **Each pair is generalised arc consistent over distinct variables, and a
  chain is not.** The propagator is Law and Lee's algorithm: it removes `t`
  from every position with no possible `s` before it, and when a position is
  fixed to `t` and only one earlier position can still hold `s`, it fixes that
  position to `s` (#1145). A chain is propagated pair by pair, which is weaker
  than GAC on the chain, and a repeated variable can defeat GAC on a pair.
- **Each inference states a helper before its RUP.** The reasons are minimal,
  the earlier positions' `≠ s` literals, and with a reason that small, unit
  propagation cannot always see that `x_i = t` switches the precede row on.
  So every inference first states `x_i = t ⇒ ¬[pos[t] ≥ n]`; see
  [Rule: t-without-earlier-s](#rule-t-without-earlier-s).
- **Its encoding is linear in the array per chain value.** Each chain value
  gets a proof-only index, `n` reified flags, up to `n` upper-bound rows and
  `n` existence rows of at most three terms each. That matches `cake_pb_cp`
  label for label once cake makes the same change (#1413), and it is
  width-independent.

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
    chain would come from the domains' union) are reported unsupported. The
    code's comment calls the latter issue #150's phase 2b, but #150 is closed,
    so nothing tracks it.

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
for any kind. The proof handles views too. Since #1208 the encoding names
each view's `x_i = v` by the view's own `=` literal, which the view's channel
rows tie to the underlying variable; at `c9ceea25` it was spelled through the
underlying variable's literal. At `86caad24`, `ValuePrecede{1, 2, {x + 1, y,
3 − w}}` over `0..3` writes `~p[1_view_of_x_plus_1][eq1]` in its upper-bound
row and enumerates its 36 solutions with a verifying proof
(`tmp/fd-wrapup/review/g4/probes/vpview.cc`). The
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
- **Shares code:** none.
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
  ¬[pos[v] ≥ i]  ∨  [pos[v] ≥ i+1]  ∨  x_i = v          @c[id][<i>ex_v]
```

The upper-bound rows cap `pos[v]` at the first occurrence and the existence
rows push it up to it, so `pos[v]` is exactly the index of `v`'s first
occurrence, or `n`. An existence row says `pos[v] = i ⇒ x_i = v`; at `i = 0`
its first disjunct is false and is not written. Unit propagation climbs them:
with `x_0, …, x_{i−1} ≠ v`, row 0 gives `[pos[v] ≥ 1]`, row 1 then
`[pos[v] ≥ 2]`, and so on to `[pos[v] ≥ i]`.

Where `x_i` cannot be `v`, by its declared bounds, `x_i = v` is false under the
bound rows: the upper-bound row says nothing and is not written, and the
existence row leaves the term out. The same rule applies wherever an
`x = v` term appears in Among, `GlobalCardinality` and `BinPacking`.

**Until #1413** the existence rows were cumulative,
`[pos[v] ≥ i+1] ∨ x_0 = v ∨ … ∨ x_i = v`, and every row was written whatever
the bounds. Each old row is RUP from the new rows (`i` steps up the climb
above), and the two sets pin `pos[v]` identically, so nothing that reads
`pos[v]` changed; `cake_pb_cp` makes the same change in step (#1413). Then for each consecutive pair `(s, t)`, numbered `j`:

```
s ≠ t:   ¬[pos[t] ≥ n]  ⇒  pos[t] − pos[s] ≥ 1          @c[id][<j>pr]
s = t:   pos[s] ≥ n                                     @c[id][<j>nos]
```

**It is definitional.** Every row is the constraint's meaning or the definition
of an auxiliary.

**Size.** Per distinct chain value, `n` reified flags, at most `2n + 1` rows,
and at most `3n − 1` literal occurrences in the existence rows; plus one row
per pair. So `Θ(k·n)` rows and `Θ(k·n)` terms for `k` distinct chain values;
before #1413 the existence rows alone were `n(n + 1)/2 + n` terms per value.
On `value_precede (1 2)` over 50 variables in `0..2`, they go from 2,650
literals to 298, and the OPB from 124,563 bytes to 93,095. It is **independent
of domain width**, and mentions only the `x_i = v` literals of chain values.

### Labels

The labels are `cake_pb_cp`'s, value-keyed since #604 so that no two rows share
one. No rule cites a row by label: every inference is a RUP, after at most one
RUP helper line.

### Cake conformity

`scp_chain_value_precede_{sat,nonexact_sat,unsat}` all chain-verify, in `none`
mode. Since #1413 the existence rows, and the rows about values a variable
cannot take, differ from cake's until cake makes the same change; the chain
still verifies, since each old row is RUP from the new ones and the dropped
terms are false. Measured under #604, before that: the label sets are **identical** to cake's, and every
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
- **Deleted:** each inference's helper line, which is temporary.
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
builds the encoding above, and keeps each chain value's `[pos[v] ≥ n]` flag for
the propagators' helper lines. There is no initialiser; nothing is computed
once at the root.

### Propagator inventory

One propagator per consecutive pair of the chain.

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| pair `(s, t)`, `s ≠ t` | `on_change`, every variable | derived: **every variable** | 1, 2 | a chain of two or more | never claims; is, over distinct underlying variables | yes: when `s` is absent everywhere, when rule 2 fires, or when the first position that could hold `s` is fixed to it |
| pair `(s, s)` | as above | as above | 3 | a repeated adjacent chain value | never claims; is | always, after its first call |

**Holes affect: every variable, and truthfully.** The pass reads
`in_domain(x_i, s)` and `in_domain(x_i, t)`, so removing `s` from strictly
inside a domain can move the first possible `s`, and change what is removed.
The column is per variable, so it cannot say that only two values of each
domain matter; that is over-reporting only for the values other than `s` and
`t`, and over-reporting only keeps somebody else's pruning on.

**Idempotence.** Never claimed. For `s ≠ t`, over distinct underlying
variables, a second call would do nothing: removing `t` cannot move the first
possible `s`, and forcing `s` discharges the pair. Two views of one variable
break that, as `propagators.cc`'s own note on aliasing says: with positions `[x + 1, x, y]`, chain `(1, 2)`,
`x ∈ 1..3` and `y ∈ 0..2`, the first call removes 2 from the first two
positions, which fixes `x = 3` and so moves the first possible 1 to `y`, whose
2 only a second call removes. For `s = t` one call removes `s` from every
position and disables the propagator. (Until #1145 it removed `s` only from the
first position that had it, so emptying the array took one call per position.)

### Mutable state and incrementality

`None.` Each call scans from the front for the first possible `s`, prunes `t`
up to it, and then scans on from it for whichever comes first: a second
possible `s`, or a position fixed to `t`. That second scan is Law and Lee's
`β` and `γ` in one pass. A chain of `k` values is `k − 1` independent
propagators, each making `O(n)` membership tests per call, and each test linear
in its domain's runs (see [Interval efficiency](#interval-efficiency)). Keeping
the first possible `s` as backtrackable state would make a call `O(1)` when nothing
before it changed; on the corpus the family's calls cost 0.18 µs each (below),
so there is nothing to buy.

### Interior values and optional pruning

**Offers.** `None.` There is one arm, and it is already GAC on a pair.

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
   call (the scan for `α`, the pruning loop up to it, and the forcing scan on
   from it), plus up to `n − α` singleton tests in the forcing scan. Each test is
   `IntervalSet::contains`, which scans the domain's interval list from the
   front and stops at the first interval reaching the value, so it is linear
   in the number of runs below the value, not logarithmic. Each removal is an
   `IntervalSet::erase`, linear in the runs the same way. A call is `O(n)`
   tests and up to `O(n · r)` work, counting the removals, for `r` the most
   runs in any domain: `O(n)` on interval domains. No value walk.
   Making the shared membership test logarithmic would help every caller, but
   should wait for a measurement that it matters here.
2. **The reason side.** Each reason is a list of `x_{i'} ≠ s` literals, at
   most one per position, plus `x_γ = t` for rule 2: no domain walk, so no
   width or hole dependence. They are built only when `want_reasons()` says a
   proof will read them, so with proofs off they cost nothing. With proofs on,
   a call that removes `t` from `α + 1` positions builds `O(α²)` literals,
   which is what the proof lines it writes contain.
3. **The proof side.** Per inference, one helper line and one RUP. No second
   form, so no gate.
4. **The audit lane.** One row, `ValuePrecede`, pinned `Clean`:
   `ValuePrecede{1, 2, wide(p, 4)}`, four plain variables over `0..10⁹`. It
   does not vary holes, chain length,
   a repeated chain value, or views. None of those has a width-proportional
   site to find, so the gap is not one that could be hiding anything.

## Inference catalogue

Three rules. For a pair `(s, t)` with `s ≠ t`, Law and Lee's two halves: the
removal of `t` behind the first possible `s`, and the forcing of `s` at the
only place left for it. For a repeated chain value, the removal of `s`
everywhere. A conflict is not a fourth rule: it arises when the value to remove
is the only one left, or the value to force is already gone, and the tracker
asserts the attempted literal with its reason.

Four facts hold for all three.

**Each is a RUP, and the procedure is ours.** No published justification
procedure covers value precedence. The argument, spelled out under rule 1, is a
chain of the facts in
[`justification-techniques.md`](../justification-techniques.md): the inference
stated under its reason (Theorem 2.6), opposing bounds on one bit sum
(Theorem 2.7), and a bound crossing a difference row with `B = 1`
(Theorem 2.9). Rules 1 and 2 state one helper line first, by Theorem 2.7, which
unit propagation cannot find for itself; rule 3 needs none.

**Each reason is minimal.** It names only the literals the RUP uses: the
earlier positions' `x_{i'} ≠ s`, and for rule 2 the fixed `x_γ = t`. Until
#1145 every rule passed `generic_reason(vars)`, every variable's bounds and
holes, which named every later position too. That bigger reason is also what
let unit propagation find the helper line by itself: it stated every earlier
position's domain, so `pos[t]` was pinned by its own existence rows (see
rule 1).

**There is one wire form.** `hints::ValuePrecede`, `(constraint_id <id>)`, no
subhint. Measured on the probe enumerations: 63 annotations for a two-value
chain over six variables in `0..3`, 64 for a three-value chain, all that form.

**No justification reads `state`.** Rules 1 and 2 are `JustifyExplicitly` with
`ThenRUP::Yes`, whose `emit` writes the helper line from the position and the
value it was given; the reasons are built before the inference, from the
decision's own scan.

### Rule: t-without-earlier-s

- **Infers** — `x_i ≠ t`, for a pair `(s, t)` with `s ≠ t`, at every position
  `i ≤ α`, where `α` is the first position whose domain holds `s`; at every
  position when no domain holds `s`.
- **Fires when** — any variable's domain changes, in that pair's propagator.
- **Strength** — with rule 2, `GAC` on the pair over distinct underlying
  variables: Law and Lee's algorithm. On its own it is half of it, and neither
  GAC nor `bounds(Z)`: the smallest witness was two positions, chain `(0, 1)`,
  `x₀ ∈ {0, 2}`, `x₁ = 1`, where this rule keeps `x₀ ∈ {0, 2}`
  (`tmp/fd-ordering/probes/vpwit.cc`). The suite now checks GAC at every node
  for every chain of at most two values; see [Tests](#tests). A repeated
  variable can defeat it (the audit's brute force found 182 such pairs in
  23,174, `factcheck/value_precede/forcing_gac.py`), and a longer chain is
  weaker again, since its pairs are propagated separately.
- **Algorithm** — scan for `α`, then remove `t` from positions `0..α`. `O(n)`
  membership tests.
- **Why it is true** — an occurrence of `t` at `i` needs an `s` at some
  `i' < i`, and no position before `α` can hold `s`. At `α` itself, "before"
  excludes `α`, so `t` there has no `s` before it either.
- **Proof technique** — a helper line, then `RUP`, our own procedure, with these
  preconditions: the reason fixes `x_{i'} ≠ s` for every `i' < i`, and the
  encoding has the upper-bound, existence and precede rows above.
  1. **Helper:** `x_i ≠ t ∨ ¬[pos[t] ≥ n]`, temporary. Under its negation the
     upper-bound row for `t` at `i` gives `pos[t] ≤ i`, and the flag's
     reification gives `pos[t] ≥ n`. Since `i < n`, these are opposing bounds
     on one bit sum, so unit propagation refutes them (Theorem 2.7), and the
     helper is RUP.
  2. **The removal.** By Theorem 2.6 it is enough to refute `x_i = t` with the
     reason assumed. The helper makes `[pos[t] ≥ n]` false, which switches on
     the precede row `pos[t] − pos[s] ≥ 1`. The upper-bound row for `t` gives
     `pos[t] ≤ i`. The existence rows for `s` at `0, …, i − 1` climb under the
     reason, each `x_{i'} = s` disjunct being false, to `[pos[s] ≥ i]`, and its
     reification gives `pos[s] ≥ i`. Then the lower bound `pos[s] ≥ i`, the
     difference row and the upper bound `pos[t] ≤ i` are Theorem 2.9's
     contradictory triple, with `B = 1`.

  **Why the helper is needed.** Without it, nothing makes `[pos[t] ≥ n]`
  false, and the precede row stays off. `pos[t] ≤ i` alone fixes no bit
  unless `i` sits just below a power of two, and Theorem 2.7 only bites once
  the flag is assumed true, which unit propagation never does. Until #1145
  the whole-scope reason hid this: it stated every earlier position's domain,
  so each earlier position's `x_{i'} ≠ t` climbed `pos[t]`'s own existence
  rows to `pos[t] ≥ i`. That bound and `pos[t] ≤ i` fix every bit
  (Theorem 2.8), which settles the flag. The minimal reason does not state
  `x_{i'} ≠ t`. When search had removed `t` from an earlier position by a
  decision rather than by this rule, the bare RUP failed: it removed `t` from
  the last of five positions over `1..3`, where `pos[t] ≤ 4` fixes no bit of
  a three-bit sum. The mutation runs below found this.
- **Reason** — `{x_{i'} ≠ s : i' < i}`, explicit, built only when a proof
  will read it. **Minimal:** dropping any one literal stops that position's
  existence row from climbing, and VeriPB rejects the step (mutation runs
  below).
- **Assertion** — `x_i ≠ t ∨ ¬reason`. Measured at `Inferences`, removing
  `t = 2` from `c` and then from `d`, with `s = 1` absent from `a` and `b`:
  ```
  a 1 ~i[c][eq2] 1 i[a][eq1] 1 i[b][eq1] >= 1::value_precede:((constraint_id _1));
  a 1 ~i[d][eq2] 1 i[a][eq1] 1 i[b][eq1] 1 i[c][eq1] >= 1::value_precede:((constraint_id _1));
  ```
  (`tmp/vp1145/fam/rules.cc`, mode `remove`.) Until #1145 the same removal
  named every variable's bounds as well, 8 to 13 literals on the audit's
  six-variable probe.
- **Hint** — `hints::ValuePrecede`: `originator`, the `ConstraintID`.
- **Offline reconstructibility** — `offline`. The clause names the removed
  literal, and the rest follows from the database once the helper is
  restated. The helper is fixed by the removed literal and the pair: it is
  `¬[x_i = t]` together with `t`'s absent flag, which the value-keyed name
  `v[id][<t>_<n>][pge]` finds.
- **Proof size** — three lines per removal (the helper, the RUP, the helper's
  deletion). The RUP has `i + 1` literals and the helper two. Width-independent.
- **Gaps** — `None.`
- **Tightness** — `Shown`, by hand: no lane. Each corruption below was run with
  `value_precede_test` over seeds 1, 2 and 3 (`tmp/vp1145`). Dropping the last
  literal of the reason is rejected on all three. Dropping the helper is
  accepted on all three, and is rejected on 4 of seeds 10 to 49, all at a
  removal from the last of five positions, as above. So a fixture that does not
  vary the search will not show the helper is needed.

### Rule: s-forced-before-fixed-t

- **Infers** — `x_α = s`, for a pair `(s, t)` with `s ≠ t`, when some position
  `γ > α` is fixed to `t` and no position strictly between `α` and `γ` can
  hold `s`.
- **Fires when** — as rule 1, in the same call, after it.
- **Strength** — the second half of Law and Lee's algorithm; with rule 1,
  `GAC` on the pair over distinct underlying variables (rule 1 has the
  details). Added by #1145.
- **Algorithm** — one scan forward from `α + 1`, stopping at whichever comes
  first: a position that can hold `s` (Law and Lee's `β`; nothing to force), or
  a position fixed to `t` (their `γ`; force). `O(n)` membership tests. The scan
  reads the state after rule 1's removals, which is only narrower than what the
  scan for `α` saw, so no position before `α` can hold `s`. Forcing `s`
  discharges the pair, so the propagator then disables itself.
- **Why it is true** — `x_γ = t` needs an `s` at some position before `γ`,
  and of those only `α` can still hold it.
- **Proof technique** — the same two steps as rule 1, about `γ`: the helper
  `x_γ ≠ t ∨ ¬[pos[t] ≥ n]`, then a RUP of `x_α = s` under the reason. Under
  `x_α ≠ s` and the reason, the existence rows for `s` climb past every
  position before `γ` to `[pos[s] ≥ γ]`, and `x_γ = t` gives `pos[t] ≤ γ`
  against the switched-on precede row, as before. (The reason does not say
  that `x_γ ≠ s`, but `x_γ = t` does, so the climb can go one step further;
  that changes nothing, since a larger lower bound on `pos[s]` makes the
  triple more contradictory, not less.)
- **Reason** — `{x_{i'} ≠ s : i' < γ, i' ≠ α} ∪ {x_γ = t}`, explicit, built
  only when a proof will read it. **Minimal:** dropping `x_γ = t`, or one of
  the `≠ s` literals, is rejected by VeriPB (mutation runs below).
- **Assertion** — `x_α = s ∨ ¬reason`. Measured at `Inferences`, forcing `a = 1`
  with `b ∈ {2, 3}` and `c = 2`:
  ```
  a 1 i[a][eq1] 1 i[b][eq1] 1 ~i[c][eq2] >= 1::value_precede:((constraint_id _1));
  ```
  (`tmp/vp1145/fam/rules.cc`, mode `force`.)
- **Hint** — `hints::ValuePrecede`: `originator`.
- **Offline reconstructibility** — `offline`, as rule 1: the helper is fixed
  by the clause's one negative `= t` literal.
- **Proof size** — three lines, as rule 1, of `γ + 1` literals.
- **Gaps** — `None.`
- **Tightness** — `Shown`, by hand, as rule 1: dropping the helper, dropping
  `x_γ = t` from the reason, and dropping an earlier position's `≠ s` are each
  rejected on seeds 1, 2 and 3.

### Rule: repeated-value-absent

- **Infers** — `x_i ≠ s` for a pair `(s, s)`, at every position `i` whose
  domain holds `s`, in one call.
- **Fires when** — the propagator's first call, which then disables it for
  good.
- **Strength** — `GAC` on its own pair: the pair means `s` never appears.
  Until #1145 it was the same code as rule 1 with `t = s`, which removed `s`
  only at the first position holding it, so emptying the array took `n` calls.
- **Algorithm** — one pass over the positions. `O(n)` membership tests.
- **Why it is true** — the first occurrence of `s` would need an earlier `s`.
- **Proof technique** — `RUP`, ours. Under `x_i = s`, the upper-bound row
  gives `pos[s] ≤ i < n`, against the `nos` row `pos[s] ≥ n` (Theorem 2.7). No
  helper is needed: the `nos` row is unconditional.
- **Reason** — empty. The derivation needs only the encoding.
- **Assertion** — `x_i ≠ s`. Measured at `Inferences`, chain `(2, 2)` over
  two variables in `0..3`:
  ```
  a 1 ~i[a][eq2] >= 1::value_precede:((constraint_id _1));
  a 1 ~i[b][eq2] >= 1::value_precede:((constraint_id _1));
  ```
  (`tmp/vp1145/fam/rules.cc`, mode `same`.)
- **Hint** — `hints::ValuePrecede`: `originator`.
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line per removal.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` With an empty reason there is nothing to drop.

## Evidence

### Tests

- **`value_precede_test`** (`value_precede_constraint`, plus
  `value_precede_constraint_view_mixed` and, since #1208, its `_view_mixed_late`
  twin, which posts a vacuous row over each view after the constraint): 28 fixed
  shapes (two-, three- and
  four-value chains, values in no domain, the first position forced to `t`,
  three that need rule 2 at the root or in search, chain values out of domain
  order, repeated chains `{1, 2, 1}` and `{1, 1}`, empty and one-value chains,
  negative values, constants mid-array, #254's degenerate arrays) and eight
  random ones of two to five variables. Each runs with and without proofs: full
  enumeration and the proof. Since #1145 a chain of at most two values runs
  under `solve_for_tests_checking_gac`, which **checks GAC at every node**;
  longer chains, which are not GAC, run under plain `solve_for_tests`. VeriPB
  runs when on the path. Seeded.
- **Duplicate-variable runs**, bare lanes only: repeated positions, by
  enumeration, with no consistency check, since a repeated variable can defeat
  GAC.
- **`scp_chain_value_precede_{sat,nonexact_sat,unsat}`:** see [Cake
  conformity](#cake-conformity).
- **MiniZinc:** `valueprecede.mzn`, `valueprecedechain.mzn`.
- **XCSP3:** `precedence.xml`.
- **Audit lane:** the `ValuePrecede` row.

**Runtime caps.** No lane sets or clears one, and the default caps never fire:
72 runs bare and 66 in `view_mixed`, all complete (`GCS_TEST_MAX_SOLUTIONS=300
GCS_TEST_MAX_RECURSIONS=1500 value_precede_test --seed=1`, and with
`--view-position=mixed`, at `c9ceea25`).

**Tightness:** no mutation lane. The by-hand runs are under each rule's
Tightness.

**What the tests do not cover.**

- **Strength of a chain**, deliberately: pairwise propagation is weaker than
  GAC on the chain, so only chains of at most two values are checked.
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
  enumeration, proofs and (since #1145) the GAC check run over holey domains.
  No test posts a second constraint, so holes made by another constraint are
  not exercised.
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
  of solutions is a Bell number and the search order decided whether the
  forcing rule mattered, before #1145 added it.
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
`1..n` has no repeated value, so rule 3 is not exercised.)

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

**After #1145.** *Release builds of `ebc98856` and of #1426 on it, the same
benchmark (`tmp/vp1145/bench`), fataepyc-09, `taskset -c 4`, fixed malloc
thresholds, three runs each, 2026-11-07; Gecode as above, on the same box.*

| n | Search | Before: time | recursions | failures | After: time | recursions | propagations | failures | Gecode time |
|---|---|---|---|---|---|---|---|---|---|
| 10 | first position first, smallest value | 0.109–0.112 s | 142,417 | 0 | 0.109–0.111 s | 142,417 | 202,084 | 0 | 0.086 s |
| 11 | first position first, smallest value | 0.644–0.668 s | 820,987 | 0 | 0.636–0.641 s | 820,987 | 1,139,035 | 0 | |
| 10 | last position first, largest value | 1.05 s | 562,595 | 247,823 | 0.158–0.161 s | 171,326 | 535,121 | 0 | 0.136 s |

The forward searches do identical work either side. Backwards, GCS now never
fails either, and is 1.2 times Gecode's time rather than 8; the `ValuePrecede`
chain over `1..10` (mode `vp`) gives the same counts as `SeqPrecedeChain`.

### Proof performance

See [`seq_precede_chain.md`](seq_precede_chain.md), whose probe is this
constraint over the chain `1..n`. The short version, at `n = 7`, at the audit:
the fully-justified proof is 7,995 lines and verifies in 0.20 s, of which **293
lines (3.7%) are this family's**. The rest is the enumeration's own. The OPB is
433 rows at `n = 7`, and grows as `Θ(k·n)` rows and `Θ(k·n)` terms since #1413.

**Since #1145** each inference is three lines, not one (the helper, the RUP,
and the helper's deletion), but each is shorter. Measured with the chain
`1..7` over seven variables (`tmp/vp1145/bench`, `spc_gcs.cc` mode `vp`, both
verified `s VERIFIED`):

| Search | Before: lines | bytes | VeriPB | After: lines | bytes | VeriPB |
|---|---|---|---|---|---|---|
| first position first, smallest value | 7,995 | 325,907 | 0.20 s | 8,553 | 319,367 | 0.17 s |
| last position first, largest value | 17,107 | 713,372 | 0.35 s | 10,810 | 379,795 | 0.20 s |

Forwards there are still 293 inferences, now 879 lines (10.3%), and the proof
is smaller in bytes. Backwards, the failures the forcing rule removes take
their nogoods with them.

**Assertion levels.** At `Off` every probe proof verifies (`probes/runfam.sh`:
two- and three-value chains, and `(2, 2)`). At `Definitions` and `Inferences`
VeriPB accepts each under assertions (`s UNDER ASSERTIONS`, not `VERIFIED`),
since this family's inferences are `a` lines there, so only `Off` checks the
family. At `Links` the two-value and three-value chains are accepted under
assertions, and `(2, 2)` is not. That failure is at a `solx` step, on a
constraint of the shared literal layer for `x[2]`, not a `value_precede` row:
it is generic, and other families' probes fail at `Links` the same way. Of
the `Inferences` assertions on the two-value probe, 63 of 4,937 carry this
family's hint; the rest are the search's. All of this is unchanged by #1145,
re-run on its build (`tmp/vp1145/fam/fam_new.txt`): the same verdicts, `a`
counts and hint counts at every level, and the same `(2, 2)` failure at a
`solx` step at `Links` (line 78 rather than 98, since rule 3 now empties the
array in one call).

## Status, gaps, and next steps

### Proof-logging gaps

`None.` Every inference is justified at `Off`, and the propagator is the same
with proofs on or off. The helper lines are proof-only, and the reasons are
built only when a proof reads them. (One probe proof fails at `Links`, in the shared literal
layer, not in this family: see [Proof performance](#proof-performance).)

### Known limitations

- **A chain is propagated pair by pair,** so it is weaker than a chain
  algorithm would be: pairwise GAC misses `x₀ = 1` in chain `(1, 2, 3)` over
  `{0, 1}, {0, 2, 3}, {2, 3}`.
- **A repeated variable can defeat GAC on a pair,** since the two halves of
  Law and Lee reason about positions, not variables.
- **Each inference costs three proof lines,** since the helper is stated and
  deleted every time.

### Next steps

1. **Chain GAC.** Pairwise GAC is what Gecode does too; a chain algorithm
   would be strictly stronger, and this audit did not confirm who first
   published one. No issue filed.
2. **State each helper once.** `x_i = t ⇒ ¬[pos[t] ≥ n]` holds outright, so
   it could be derived once per position and pair, at the top level, rather
   than stated and deleted per inference. That would take a proof from three
   lines per inference to about one. Small, and only worth it if this family's
   share of a proof grows.

(Until #1145 the first steps here were Law and Lee's forcing rule, minimal
reasons, and emptying a repeated chain value in one call. #1426 did all
three.)

## Prior art

Law and Lee (*Global constraints for integer and set value precedence*, CP 2004)
give the linear-time GAC algorithm for a pair, which Gecode's `precede`
implements, applying it pair by pair to a chain. Chain GAC is strictly
stronger than pairwise GAC; this audit did not confirm who first published an
algorithm for it. The encoding here is `cake_pb_cp`'s, and this family's
proof is, as far as this audit knows, the first certified value-precedence
propagator. Since #1145 it certifies the whole of Law and Lee's pair
algorithm.

## Further reading

- [`seq_precede_chain.md`](seq_precede_chain.md): the one caller, its clamp, and
  the measurements this document borrows.
- [`justification-techniques.md`](../justification-techniques.md): the
  theorems rules 1 and 2 chain.
