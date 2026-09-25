# Arithmetic: one variable is the sum, difference, product, power, quotient or remainder of two others

> **Maturity** production ·
> **Audited** 2026-09-24 at `f28fdef8`; re-audited 2026-09-25 at `61112ed0` ·
> **Open issues** filed by this audit and still open: #1067 (`Modulus`'s
> quotient magnitude is not determined by unit propagation on a solution, so
> its hints-only proofs fail VeriPB's solution check), #1068 (an aliased `Plus`
> or `Minus` converges one value per pass, under every tag), #1066 (tidying:
> draft thesis numbering, headers describing the pre-rewrite design, dead
> fields). Filed by this audit and since fixed: #1064 (corner products threw
> `IntegerOverflow`; #1079) and #1065 (`Divide` left a sign-open quotient
> unpruned; #1081). Found here but not this family's: #1063 (the engine's
> per-node state copy goes back to the kernel on every backtrack, 58% of
> `stable-goods`' run), and #1056 (the harness's idempotence checker was off
> in 100 lanes; #1086). Filed from this re-audit: #1102 (a hole at 0 in
> `Divide`'s quotient does not wake it). Already open and touching this family: #540, #724,
> #845, #880, #960, #846, #833, #868; #1038, listed here at the first pass, was
> closed by removing the short-names option (#1087). Tracked under #871.

**Re-audit, 2026-09-25.** Three fixes for this audit's issues merged after the
first pass, and a review of the document found four claims that were wrong
from the start. What each changed here:

| Issue | Fixed by | What changed in this document |
|---|---|---|
| #1064: corner products threw past 2^63 | #1079: `product_bounds` and `square_bounds` saturate each corner; `Divide` / `Modulus` refute a saturated lower corner and skip a bound whose sum would overflow | [Robustness and limits](#robustness-and-limits), [Known limitations](#known-limitations), [Next steps](#next-steps), [Proof-logging gaps](#proof-logging-gaps); four `wide-product` rows in the [audit lane](#interval-efficiency). Propagation now works at any width; **proof logging still stops at 62 bits of combined operand magnitude for `Multiply`, 63 of dividend and divisor for `Modulus`, and for `Divide` 63 of quotient and divisor with the dividend also counting** (see [Robustness and limits](#robustness-and-limits)) |
| #1065: `Divide` left a sign-open quotient unpruned | #1081: [quotient-sign](#rule-quotient-sign) fires on a weakly signed dividend; three new rules bound a sign-open divisor or quotient and its magnitude against each other; the divisor's sign follows from `x`'s and `q`'s | [quotient-sign](#rule-quotient-sign), and new [divisor-sign](#rule-divisor-sign), [sign-open-clamp](#rule-sign-open-clamp), [sign-open-magnitude-cap](#rule-sign-open-magnitude-cap), [sign-open-magnitude-nonzero](#rule-sign-open-magnitude-nonzero); [stage-bound](#rule-stage-bound), [divisor-hole-pushthrough](#rule-divisor-hole-pushthrough), the inventory, [Interior values](#interior-values-and-optional-pruning), [Tests](#tests). `arithmetic-proofs.md` gained a paragraph on the same |
| #1056: the idempotence checker was off in 100 harness lanes | #1086: the harness switches it on before anything propagates, and throws if it is off | the inventory's idempotence paragraph, [Tests](#tests) |
| — (review) | — | [product-bounds](#rule-product-bounds) claimed `bounds(Z)` on `z`; it is `bounds(R)`. [sum-interval-prune](#rule-sum-interval-prune)'s technique field hid its `pol` lemmas. [Interval efficiency](#interval-efficiency)'s headline left out `PowerTable`. [Proof-time state](#proof-time-state) gave the wrong mechanism for #1067 |

**Re-measured at `61112ed0`**, on the review build (release, unmodified): the
overflow shapes of [Robustness and limits](#robustness-and-limits), with and
without proofs, against the same probe on the `f28fdef8` build; `Divide`'s
sign-open shapes, root domains and failures, on both builds; all 12 `modulus`,
11 `divide` and 7 `multiply` chain cases at `Off` and `Inferences`; the 17
constraint, mutation and helper lanes (the four constraint tests and their
`view_mixed` twins, `plus_minus_constraint_dynamic_fallback`, the four
`plus_mutation` lanes, `product_bounds`, `wide_product`, `product_justify` and
`tabulation_test`), with the default caps and VeriPB on the `PATH`, all
passing; and the counterexamples under
[product-bounds](#rule-product-bounds). **Everything else is the first pass's,
at `f28fdef8`**: the corpus firing counts, both performance sections, the
per-firing proof sizes, the cap measurements and the uncapped lane run. None of
them was taken again, and #1081's new rules also run for `Modulus` (on the
divisor), so the `harmony` figures may have moved. `file:line` citations are to
`f28fdef8` unless they say otherwise.

Six classes over four directories, in two groups that share almost nothing
but the tabulation machinery. `Plus` and `Minus` are a unit-coefficient
linear equality of three terms, with a bounds propagator and an interval
propagator that is generalised arc consistent over distinct variables.
`Multiply`, `Power`, `Divide` and `Modulus` are cake_pb_cp's bit-product
encoding, with bounds propagators whose every inference is justified through
the product grid by the procedures of McIlree's thesis, Chapter 7.
[`arithmetic-proofs.md`](../arithmetic-proofs.md) is the design note for the
second group, and this document does not repeat it.

Three things to know before touching it.

- **Multiply is cheap per call and rarely the bottleneck.** On four of the six
  corpus models where it has the largest share of propagation time, a call
  costs 0.28–0.67 µs. On `train` 2014 our search matches Gecode's to within
  0.3% of the nodes, and we are 3.5 times slower, but `Multiply` is 5.8% of our
  propagation time there. On `opd` 2017 and `stable-goods` 2020, all
  propagation together is 8% and 15% of the run. Much of the rest is the engine
  copying tens of thousands of domains per node (#1063).
- **Its proofs are large, and mostly its own.** A `Multiply` inference costs
  about 70 proof lines on `train` 2014, where its justifications are 55% of the
  proof's lines and 71% of its bytes. A search that takes 1.5 s without proofs
  writes a 3.65 GB proof there. The derivations are per bit, never per value,
  so width is not the problem; the number of inferences is.
- **The weak and fragile spots are in `Divide` / `Modulus`, and at the
  edges.** `Modulus`'s proofs verify fully justified, but not in the
  hints-only modes, because nothing in the encoding pins its quotient
  magnitude on a solution (#1067). An aliased `Plus` or `Minus` can converge
  one value per pass, in time linear in a domain's width (#1068). Nothing in
  the suite reaches either. Two more were fixed after the first pass: `Divide`
  now prunes a sign-open quotient (#1065, #1081), and the product group's
  corner products saturate rather than throw (#1064, #1079), so propagation
  works at any width; **with proofs on, building the proof model still fails
  past about 62 bits of combined operand magnitude** (63 for `Modulus`'s
  dividend and divisor), because the encoding's rows have to fit in an
  `Integer`.

## What it is

### Semantics

| Class | Enforces | Notes |
|---|---|---|
| `Plus(a, b, result)` | `a + b = result` | |
| `Minus(a, b, result)` | `a − b = result` | |
| `Multiply(v1, v2, result)` | `v1 · v2 = result` | |
| `Power(base, exponent, result)` | `base ^ exponent = result` | MiniZinc semantics: `0^0 = 1`; a negative exponent gives `1 div base^|k|`, truncated, so `2^−5 = 0` and `(−1)^−n = ±1` by parity; `0^−n` has no support; an unrepresentable power has no support |
| `Divide(x, y, quotient)` | `x / y = quotient`, truncated towards zero | `y = 0` has no support |
| `Modulus(x, y, remainder)` | `x mod y = remainder`, remainder taking the dividend's sign | `y = 0` has no support |

Every argument is an `IntegerVariableID`: a variable, a view or a constant.
Degenerate shapes, per class:

- **Constants.** `Plus` and `Minus` fold constants into the OPB row, and an
  all-constant row is tested (#254). `Multiply` with a constant operand
  (either or both) becomes a `LinearEquality` in `prepare()`, under the
  `Multiply`'s own constraint id (`multiply.cc:84-128`). `Multiply{c1, c2, r}`
  is not tested. `Power` with a constant base and exponent becomes a value
  stage, or an initial contradiction when the power is not representable.
  `Divide` and `Modulus` put every shape, constants included, through the one
  magnitude grid; all-constant posts verify, but are not in the suite.
- **A variable exponent.** `Power` installs `innards::PowerTable`, a `Table`
  over the product of the base's and exponent's initial domains, whatever
  consistency was asked for (`power.hh:22`). It has no size budget (#845).
- **A constant zero divisor.** `Divide` and `Modulus` write a trivially false
  row and an initial contradiction, with a stats note
  (the row at `divide_modulus.cc:1086-1089`, the initialiser at `:1193-1201`, #722). A view whose underlying variable is
  fixed where the view maps to 0 takes the normal path, where the zero is pruned.
- **Aliasing.** `Plus{x, x, r}`, `Multiply{x, x, z}` (a square),
  `Multiply{x, y, x}`, `Power{x, 2, x}`, `Divide{x, x, q}` and their relatives
  are all accepted natively. The product encoding is slot-keyed, so a repeated
  operand gets one magnitude channel per slot, exactly as cake emits. Two
  different views of one variable, such as `x · −x`, are not a square: they get
  box reasoning over independent intervals.
- **Negative values and zero.** Everything is fully signed. The product
  encoding splits each operand on a reified sign atom; `Divide` and `Modulus`
  split on the dividend's sign to pin truncation, because `x = q·y + r` with
  `|r| < |y|` alone admits two quotients for any inexact division (`7 = 3·2 + 1
  = 4·2 − 1`); making the remainder take the dividend's sign picks the
  truncated one.

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Plus` | ✓ `int_plus`[^mzplus] | `decompose`[^xplus] | ✓ `x − y == z` only, over a negated view[^cplus] | ✓ `plus` | |
| `Minus` | `n/a`[^mzplus] | `decompose`[^xplus] | `decompose`[^cplus] | ✓ `minus` | reachable from the API and the `.scp` only |
| `Multiply` | ✓ `int_times` | ✓ `mul` (n-ary as a chain), `sqr` as `Multiply{a, a, r}` | ✓ `mul` | ✓ `multiply` | a constant operand becomes `LinearEquality` |
| `Power` | ✓ `int_pow` | ✓ `pow`, constant exponent only (`k = 0` and `1` are folded in the walker and post nothing); a variable exponent is reported unsupported | ✓ `pow` | ✓ `power`[^spow] | a variable exponent becomes `PowerTable` |
| `Divide` | ✓ `int_div` | ✓ `div`, into an auxiliary result[^xdiv] | ✓ `div` | ✓ `divide` | |
| `Modulus` | ✓ `int_mod` | ✓ `mod`, into an auxiliary result[^xdiv] | ✓ `mod` | ✓ `modulus` | |

[^mzplus]: `fzn_glasgow.cc:753-758` posts `Plus` for `int_plus`, but
    MiniZinc flattens sums to `int_lin_eq`, and none of the corpus's 297
    models posts `int_plus`. Nothing posts `Minus`.
[^xplus]: The XCSP3 intension walker posts `add` and `sub` as
    `LinearEquality`s into auxiliary results
    (`xcsp_glasgow_constraint_solver.cc:1386-1409`); it never posts either
    class.
[^cplus]: CPMpy's upstream GCS interface, as copied on 2026-09-23. Every
    comparison whose left-hand side is a `sum` is caught first and posted as a
    `LinearEquality` (`cpmpy_gcs.py:574`), so its two-term-`sum` branch to
    `Plus` (`:626`) is unreachable. A `sub` reaching the interface is posted
    as `Plus{x, −y, z}` over a negated view (`:622-625`); whether CPMpy's own
    flattening lets a `sub` through was not checked. `mul`, `div`, `mod` and
    `pow` go through `gcspy`'s `post_arithmetic` to the classes above.
[^spow]: `Power`'s `.scp` form is nested, `(id power (b e r))`, unlike the
    other five's flat `(id plus X Y Z)`. cake has no power encoder, so it has
    no chain case.
[^xdiv]: The intension walker gives `div` and `mod` an auxiliary result over
    `[−M, M]`, with `M` the largest magnitude of the dividend's bounds for
    `div` and of the divisor's for `mod`
    (`xcsp_glasgow_constraint_solver.cc:1526-1541`). So an XCSP3 `div`'s
    quotient always spans zero, and a `div` whose dividend's domain contains 0
    is the shape of #1065. Since #1081 a dividend in `[0, n]` (or `[−n, 0]`)
    pins the quotient's sign once the divisor's is decided; one that spans
    zero can still leave the
    quotient short of its hull (see [quotient-sign](#rule-quotient-sign)).

`frontend-support-matrix.md` has no rows for this family; its XCSP3 side sits
under the matrix's `intension (algebraic exprs)` row.

### Options

**`with_consistency()`**, per class. The variant is closed:

| Class | Accepts | Default |
|---|---|---|
| `Plus`, `Minus` | `consistency::Auto`, `BC`, `GAC`, `Dynamic`, `Tabulated` | `Auto` |
| `Multiply`, `Power`, `Divide`, `Modulus` | `consistency::Auto`, `BC`, `Tabulated` | `Auto` |

What each tag installs:

| Tag | `Plus`, `Minus` | `Multiply`, `Power`, `Divide`, `Modulus` |
|---|---|---|
| `BC` | the bounds propagator | the bounds propagator |
| `GAC` | the interval propagator, exact at every step | — |
| `Dynamic` | the interval propagator, dropping to a hull whenever a step would combine more than 1024 pairs of intervals | — |
| `Tabulated` | the bounds propagator **and** a table derived in the proof, whatever its size | the bounds propagator **and** the table, whatever its size (#880) |
| `Auto` | the table (with the bounds propagator) when two positions share a variable and the table is within budget; otherwise as `Dynamic` | the table (with the bounds propagator) when within budget; otherwise as `BC` |

- **`Auto` resolves once, in `prepare()`, from the declared domains**, not the
  root-propagated ones. It means "tabulate if small", not an
  optional-interior-pruning pair. The budget is a product of domain sizes of
  at most 100, which counts the enumeration tree's leaves; with its interior
  nodes the derivation can write up to about twice as many lines. It is
  overridable once per process by `GCS_TABULATION_THRESHOLD`
  (`tabulation.cc:234-242`), and the largest-domained variable that the others
  determine is left out of the product (`tabulation.cc:244-267`). In practice:
  - `Plus` / `Minus`: only when two positions alias, and every aliased shape
    has a determined variable to leave out. The budget is `|D(x)|` for
    `x + y = x`, `min(|D(x)|, |D(r)|)` for `x + x = r`, and 1 for `x + x = x`.
    Over distinct variables `Auto` never tabulates, because the interval
    propagator is already GAC there, and an aliased post over budget gets the
    interval propagator.
  - `Multiply`: `|D(v1)|·|D(v2)|` for distinct operands, `|D(x)|` for a
    square, whatever the result's width. A constant-operand `Multiply`
    re-implements the rule for its `LinearEquality` (`multiply.cc:90-121`,
    "keep the two in step").
  - `Power`: `|D(base)|`, whatever `k` and the result's width. The chain's
    auxiliaries are not enumerated; unit propagation pins them.
  - `Divide`: `|D(x)|·|D(y)|·|D(q)|`, since no slot is determined.
  - `Modulus`: over `x`, `y`, `r` and the quotient magnitude `|q|`, with `r`
    (and `x` when its sign is fixed) determined. `|q|` is sized
    `2^bits(max|x|)`, so an `Auto` post is not view-invariant (`058e0597`).

  On the corpus, `Auto` tabulates 57,504 of the 115,972 `int_times` posts, in
  12 models: every post in `opd` 2015 and 2017 and in `stable-goods` 2020, and
  most in `ship-schedule`. It tabulates 31 of 350 `int_div` and 6 of 420
  `int_mod`. Computed from the flattened domains with the rule above, not
  observed; #724 asks for the decision to be reported.
- **`Dynamic`** re-decides at every step of every call: an exact step
  combines `|intervals(o1)|·|intervals(o2)|` pairs, and past 1024 it prunes
  against the other operand's hull instead (`gac.cc:365-380`). 1024 is
  `default_interval_pairs_threshold()`, overridable by
  `GCS_INTERVAL_PAIRS_THRESHOLD` (`gac.cc:404-412`); the header's rationale is
  that no #192 model where GAC paid ever exceeded 289.
- **No option changes the OPB.** The tabulation is derived inside the proof
  (`tabulation.hh:119-128`); the encoding is the same under every tag.
- **Testing-only:** `Plus::with_proof_mutation()` corrupts the interval
  propagator's derivation, for the mutation lanes. "Never use this outside a
  test" (`plus.hh:77`).

### Variable kinds and views

Any `IntegerVariableID` in every position, and the proofs handle views
natively:

- **`Plus` / `Minus`** write their row over the handles as given. `Minus` has
  its own propagator over the user's `b` with signed coefficients, rather than
  running `Plus` over a synthesised `−b` view, because an unregistered view's
  `pol` terms do not cancel against the model row (`2ec1297e`).
- **The product family** takes the handles directly, with no de-viewing: its
  channel rows are written over the view, and the bound lines are stated in
  the view's own form so that its terms cancel (`arithmetic-proofs.md`, "the
  justification layer").
- **Tabulation** enumerates the underlying variables and maps values through
  the affine forms (`affine_of`).
- **cake's `.scp` grammar has no view terms**, so a view shape self-verifies
  only; see [Cake conformity](#cake-conformity).

### Reification

`None.` No class in the family has a reified form, and none is wanted: a
reified product would be a guarded copy of the encoding, which is what
#540's guarded derivation would build inside the proof instead. MiniZinc's
`int_times` and the rest have no reified FlatZinc forms.

### Relation to other families

**Into this family.** MiniZinc's `int_times`, `int_div`, `int_mod`, `int_pow`
and `int_plus`; XCSP3's `mul`, `sqr`, `div`, `mod` and `pow` inside
`intension`; CPMpy's `mul`, `div`, `mod` and `pow`, and `sub` if it reaches the interface; the
`.scp` reader.

**Posts as children.** A constant-operand `Multiply` becomes a
`LinearEquality`; a variable-exponent `Power` becomes a `PowerTable`, which
materialises a `Table`. `Power`'s chain links are **not** child constraints:
they are `k − 1` signed multiplications inside the one constraint, sharing its
id and told apart by `LinkNaming`.

**Shares code.**

- **`innards/product_encoding`, `product_justify` and `product_bounds`**,
  between `Multiply`, `Power` and `Divide` / `Modulus`. A change to
  `product_justify` is a change to all four. `Divide` / `Modulus` call the
  sign-case resolution without subproof hints.
- **`innards/tabulation`**, between all six and `LinearEquality`: the `Auto`
  budget, the in-proof table derivation, and the extensional propagator from
  `extensional_utils`, which is the table family's.
- **`innards/linear_stages`**, between `Power` and `Divide` / `Modulus`:
  gated linear rows built directly as `LinearStage`s. No `Linear` constraint
  is posted. The inferences go through `propagate_linear` and carry
  `hints::LinearEquality`.

**Presolvers.** None rewrite into or out of this family.

**Reached only through a decomposition?** No for four classes. `Minus` has
no front-end post outside the API and the `.scp`. `Plus` has MiniZinc's
`int_plus`, which the corpus never produces, and CPMpy's `sub`, if one
reaches the interface. So in practice neither is exercised by a front end.

**Candidate merge.** The family list's `abs` merge was settled as separate in
`abs.md`: `Abs` shares no code or encoding with the product group.
`Plus` / `Minus` and the product group are one family by the list's
decision, and nothing here argues for splitting them. But they share only
`tabulation`, which `LinearEquality` shares too.

## The proof model

### OPB encoding

**`Plus` and `Minus`.** One equality as two labelled halves, over each
argument's `BinEnc`, with constants folded into the degree:

```
@c[id][le]:  −a − b + result ≥ 0        (Minus: −a + b + result ≥ 0)
@c[id][ge]:   a + b − result ≥ 0        (Minus:  a − b − result ≥ 0)
```

**`Multiply`**, `x · y = z`, cake_pb_cp's signed encoding
(`product_encoding.cc`, `signed_multiply.cc:42-57`), in emission order:

- **A magnitude channel per operand slot**: a proof-only bit vector
  `BinEnc(|x|)` over `[0, max(|lb x|, |ub x|)]` of the initial bounds, with no
  bound rows, pinned by four half-reified rows `Xge0_ge`, `Xge0_le`
  (`[x ≥ 0] ⇒ mag = x`) and `Xlt0_ge`, `Xlt0_le` (`[x < 0] ⇒ mag = −x`).
  Then the same for `Y`. A square gets two magnitude vectors over the same
  `x`, one per slot.
- **The bit-product grid**: for every pair of magnitude bits a flag
  `prod_ij ⇔ a_i ∧ b_j`, fully reified by an `[r]` and an `[f]` row, and
  `S = Σ 2^(i+j) prod_ij`.
- **The result channel**: `mag_Zge0_ge`, `mag_Zge0_le` (`[z ≥ 0] ⇒ z = S`) and
  `mag_Zlt0_ge`, `mag_Zlt0_le` (`[z < 0] ⇒ −z = S`). `z` has no magnitude
  variable.
- **Six sign clauses**, `sgn_x0`, `sgn_y0`, `sgn_pp`, `sgn_nn`, `sgn_np`,
  `sgn_pn`, over the reified sign atoms. They are not implied by the rows
  above. With `x = 2` and `y = 3`, `z = −6` satisfies both channels, the grid
  and the result channel, and only `sgn_pp` excludes it. The code's comment
  calling them "all entailed for non-negative operands" is wrong unless `z`
  is non-negative too (#1066).

With `a` and `b` the magnitudes' bit widths, the constraint owns `2ab + 18`
rows. The sign clauses' atoms (`ge0`, `ge1` and `eq0` for the operands, `ge0`
for `z`) add up to 14 definition rows to the OPB. So a probe with `x, y ∈ [4,
8]` has 70 OPB rows (`2·16 + 18 + 14`, and 6 bound rows for the three
variables), and `x, y ∈ [−4, 4]` has 56. The terms are `O(ab)`, dominated by
the four result-channel rows, which carry every grid flag: **logarithmic in
width**.

**`Power`**, constant exponent `2 ≤ k ≤ 62`: `k − 1` copies of the multiply
block, one per link `prev · base = t_i`, the first a native square and the
last writing the result. `LinkNaming` prefixes each link's labels (`l<i>_`)
and bit names, and leaves a standalone `Multiply` byte-identical. The
intermediates are OPB integer variables `aux_power<idx>`, ranged by corner
products clamped to `±max(1, |zlo|, |zhi|)` of the result's initial bounds.
Every other exponent is a case analysis written as **stage rows**: equalities
as `@c[id][<role>le]` / `<role>ge`, gated `≤` rows half-reified on their gate.
A negative exponent adds `@c[id][nonzero]`, `[base ≥ 1] + [base < 0] ≥ 1`. An
unrepresentable constant power writes a single `≥ 1` over nothing. A variable
exponent writes `PowerTable`'s `Table`, `O(|D(base)|·|D(exponent)|)` rows (#845).

**`Divide` and `Modulus`**, cake's encoding (`divide_modulus.cc:1083-1182`).
Both reuse the channel and grid emitters, but not the result channel or
Multiply's sign clauses. With `A = BinEnc(|q|)` over `n_a` bits, `B =
BinEnc(|y|)` over `n_b` bits and `S` the grid sum:

| rows | `Divide` | `Modulus` |
|---|---|---|
| shared | `Y` channel (4), grid (`2·n_a·n_b`), `nonzero` `[y ≥ 1] + [y < 0] ≥ 1` (1) | the same |
| own | `Z` channel on the exposed quotient (4); `rem_pos_lo` `[x ≥ 0] ⇒ x − S ≥ 0`, `rem_pos_hi` `[x ≥ 0] ⇒ S − x + B ≥ 1`, `rem_neg_hi` `[x < 1] ⇒ −x − S ≥ 0`, `rem_neg_lo` `[x < 1] ⇒ S + x + B ≥ 1` (4); five sign clauses (5) | `id_pos_ge`, `id_pos_le` (`[x ≥ 0] ⇒ r = x − S`), `id_neg_ge`, `id_neg_le` (`[x < 1] ⇒ r = x + S`) (4); `rng_hi` `B − r ≥ 1`, `rng_lo` `B + r ≥ 1` (2); `sgn_pos` `[x ≥ 0] ⇒ r ≥ 0`, `sgn_neg` `[x < 1] ⇒ −r ≥ 0` (2) |
| total | 18 + `2·n_a·n_b` | 13 + `2·n_a·n_b` |
| `n_a` is the bit width of | `max|q|`, declared | `max|x|` |

No remainder exists in `Divide`, and no signed quotient in `Modulus`: its
quotient magnitude is a state variable whose bits appear in the grid, with no
channel and no bound rows. Both magnitudes are state variables with
registered bits, not proof-only variables. Two rows are implied by the others:
`nonzero` (with `y = 0`, `B = 0`, and then `Divide`'s gated remainder pairs
contradict each other, as do `Modulus`'s `rng_hi` and `rng_lo`), and
`Divide`'s `sgn_x0` (with `x = 0` both remainder pairs force `S = 0`, so
`|q| = 0`). They are cake's, so they stay, and
[divisor-nonzero](#rule-divisor-nonzero)'s RUP reaches `nonzero`: do not tidy
either away. A constant zero divisor writes one `≥ 1`
over nothing and nothing else.

**Definitional?** Yes, throughout: every row states the relation, a sign, a
magnitude or a bit product. `Divide` and `Modulus` pin truncation by the sign
split, which is the definition, not a consequence. The size is
`O(bits × bits)` for the product group and `O(bits)` for `Plus` / `Minus`;
nothing grows with a domain's width except `PowerTable` (#845).

### Labels

| Label | Cited by |
|---|---|
| `@c[id][le]`, `@c[id][ge]` (`Plus`, `Minus`) | [sum-bounds](#rule-sum-bounds), one half per rule; [sum-interval-prune](#rule-sum-interval-prune)'s lemmas |
| `@c[id][Xge0_ge]` … `@c[id][Ylt0_le]` | `Multiply`'s and `Power`'s channelling steps (JSP 7.3, cake flavour) and RUP hint kits; for `Divide` / `Modulus`, the magnitude stages ([stage-bound](#rule-stage-bound), [stage-gate-refutation](#rule-stage-gate-refutation)), and `Yge0_ge` / `Ylt0_le` also by [divisor-hole-pushthrough](#rule-divisor-hole-pushthrough). `Divide` / `Modulus` never call the JSP 7.3 / 7.4 helpers |
| `@x[id][i_j][prod][r]`, `[f]` | the grid bounds (JSP 7.1 cites `[f]`, JSP 7.2's per-cell lines cite `[r]`); `Multiply`'s hint kits |
| `@c[id][mag_Z*]` | [product-bounds](#rule-product-bounds), [factor-bound](#rule-factor-bound) and the square rules, through JSP 7.4 |
| `@c[id][sgn_*]` (`Multiply`) | nothing by name; only as RUP hints |
| `@c[id][rem_*]`, `@c[id][id_*]` | every `Divide` / `Modulus` rule that pushes a bound through the dividend, by line handle |
| `@c[id][rng_*]`, `@c[id][sgn_pos]`, `sgn_neg` (`Modulus`), and the `Y` and `Z` channel rows (`Divide`, `Modulus`) | [stage-bound](#rule-stage-bound) and [stage-gate-refutation](#rule-stage-gate-refutation); the channel rows also by [sign-open-clamp](#rule-sign-open-clamp) and [sign-open-magnitude-cap](#rule-sign-open-magnitude-cap), and only through RUP by [sign-open-magnitude-nonzero](#rule-sign-open-magnitude-nonzero) and, for `Divide`'s quotient, by [quotient-sign](#rule-quotient-sign)'s grid case, by line handle |
| `@c[id][nonzero]`, `Divide`'s `sgn_*` | nothing by name; reached by RUP in [divisor-nonzero](#rule-divisor-nonzero), [quotient-sign](#rule-quotient-sign), [divisor-sign](#rule-divisor-sign) and [power-zero-base](#rule-power-zero-base) |
| `Power`'s stage rows | [stage-bound](#rule-stage-bound) and [stage-gate-refutation](#rule-stage-gate-refutation), by line |

The grid's `[r]` and `[f]` labels are rebuilt from a string
(`product_encoding.cc:85-86`) rather than returned by the model. They agree
today. #1038 named this site as one that would have to change if keyed labels
moved; it was closed by removing the short-names option (#1087), so the labels
are always the verbose ones and the two cannot drift apart that way.

### Cake conformity

| Class | Chain cases | Mode |
|---|---|---|
| `Plus`, `Minus` | `plus_sat`, `plus_unsat`, `minus_sat`, `minus_unsat` | `strict`: byte-identical to cake |
| `Multiply` | 7: unsigned, signed, square and result-alias, SAT and UNSAT | `none`: chain-verified, not byte-compared |
| `Divide` | 11, over every sign pattern, zero-spanning dividends and divisors | `none` |
| `Modulus` | 12, likewise | `none` |
| `Power` | none: cake has no power encoder | — |

- **The `none` modes' stated reason is closed.** The comments cite "the #358
  lazy-vs-eager operand-ladder" difference; #358 is closed. The inventory
  agent re-ran four `Divide` / `Modulus` cases in `strict` mode: the chain
  verifies, and opbdiff fails on two benign classes only. First, cake
  defines `i[V][eq0]` atoms for operands we never define. Second, where an
  operand's declared domain is non-negative, a row whose `[v ≥ 0]` term is
  vacuous carries coefficient 1 from us and 0 from cake, in the shared atom
  definition and in the constraint's own `Zlt0_ge` / `Ylt0_ge`. `Multiply` was
  not re-run in `strict` mode. #1066 asks for the reason to be updated or the
  mode tightened.
- **The chain never isolates `Multiply`'s bounds proofs.** All seven
  `multiply` cases are tiny, so under the default `Auto` they tabulate, and
  the bounds propagator runs beside a GAC table. Whether any bounds inference
  lands in their proofs was not checked. `Divide` / `Modulus` are better
  covered: 17 of their 23 cases are over the budget and run on the bounds
  propagator alone.
- **No chain case exists for:** a view (cake's grammar has no view terms), a
  constant result, a constant-operand `Multiply` (a linear equality by then),
  a `Divide` / `Modulus` with a constant, all-constant or zero divisor, or an
  aliased `Divide` / `Modulus`. The inventory agent ran five constant shapes
  through the chain by hand, and all pass.

### Proof-time state

- **`Plus` and `Minus`**: nothing beyond the OPB. Every derivation is at
  `ProofLevel::Temporary`.
- **The product group, in the OPB**: the operand magnitudes' bits and the grid
  flags. They are determined by unit propagation on a solution, so `solx`
  can leave them out: under a fixed sign atom a channel pair is a binary
  equality, and the grid flags follow from their `[r]` and `[f]` halves.
  `Power`'s auxiliaries are real variables, pinned forwards through their
  links. **`Modulus`'s quotient magnitude is not pinned** (#1067). It has no
  channel, so on a solution the identity rows fix the grid sum `S`, and `|q|`'s
  bits would have to follow backwards through the grid. They do not, and the
  obstacle is the grid's **shape**, not the size of its weights. Each flag is
  `a_i ∧ b_j`, so once `|y|`'s bits are fixed, bit `a_i` of `|q|` stands behind
  one flag per set bit of `|y|`, each tied to `a_i` by its own equivalence and
  carrying its own coefficient `2^(i+j)`. Unit propagation reads those
  coefficients one at a time and never adds up equivalent flags. For `|y| = 3`
  and `S = 9` over three bits, the row is `p00 + 2p01 + 2p10 + 4p11 + 4p20 +
  8p21 = 9`: total weight 21, so the slacks are 12 and 9, and no single
  coefficient (at most 8) exceeds either, so nothing propagates. The same sum
  over the bits themselves, `3a0 + 6a1 + 12a2 = 9`, propagates completely:
  `a2` is false, then `a0` and `a1` are true. VeriPB 3.0.2 accepts a bare
  `soli` against that combined form and rejects it against the six-flag grid
  (Codex's miniature on #1067, re-run for the re-audit). At `Off` the proof's
  earlier lines pin `|q|`'s bounds, and its atoms' definitions carry them to
  the bits. At `Inferences` and `Backtracking` nothing does, and 3 of the 12
  `modulus` chain cases are rejected at a solution step (at `61112ed0` as at
  `f28fdef8`: `modulus_big_sat` fails at the `solx` for `x = 9`, `y = 3`,
  `r = 0`).
- **The product group, lazily at `ProofLevel::Top`**, never deleted:
  - **W-lines**, `2·a·b` hinted RUPs per grid, emitted the first time
    JSP 7.2 runs on that grid and cached in its cells: 1,352 lines for a 26 ×
    26 grid with distinct operands, by the inventory agent's probe (raw output
    not kept).
  - **Order atoms for other bound values**, created on first use by
    `def_line_for`. The sign atoms themselves (`ge0`, `ge1`, `eq0`) are OPB
    rows, written with the sign clauses. The hint kits ask only for existing
    atoms' definitions: the sign families, the reason's and the case
    literals', order bridges between them, and the concluded literal's.
    Asking for a fresh value's definition would mint a new atom per inference
    (`arithmetic-proofs.md`, "RUP hints").
  - **`Divide` / `Modulus`'s line caches**: whole grid-sum chains keyed by
    `(direction, a bound, b bound)`, the quotient filter's assumed-bound grid
    lines, and operand and assumed bound lines, all at `Top`. The dividend-side
    chains, whose keys churn with `x`'s bounds, live per propagation pass at
    `ProofLevel::Current` instead, because a `Top` copy of each cost 9 times
    the check time on `Modulus` (`arithmetic-proofs.md`, "line caches";
    `040fa3d0`).
- **Tabulation, at the root**: per accepted tuple two `red` lines introducing
  a selector literal, and per node of the enumeration tree one backtrack RUP,
  at `ProofLevel::Current`. **Skipped entirely at the assertion levels**
  (`tabulation.cc:102, 163, 172`), so a hints-only proof has no selectors.
- **Everything else is `Temporary`**, deleted by range when the justification
  ends.
- **Naming, for an external tool**: every row above is found from the
  constraint id, which every hint carries as `originator`, plus the fixed role
  names: `@c[<id>][<role>]`; grid flags `x[<id>][i_j][prod]`; magnitude bits
  `x[<id>][<axis>_<bit>][bin]`; for `Power`, a link's `l<i>_` role prefix and
  `<i>_` bit prefix. The caches' lines have no names; they are line numbers
  held in proofs-only maps.
- **Dangling with proofs off**: the product group's channel and grid handles
  are empty `optional`s and empty vectors with no model. Every dereference
  sits inside a justification closure, which never runs without a logger.

## The implementation

### Initialisation and global data

- **`prepare()`** decides everything structural, from the declared domains:
  `Multiply`'s constant-operand dispatch to `LinearEquality`; `Power`'s
  exponent dispatch; `Divide` / `Modulus`'s slots and magnitude sizes; and for
  every class whether `Auto` tabulates.
- **The tabulation initialiser**, at `InitialiserPriority::Expensive`, when
  the table is on. It enumerates the distinct underlying variables smallest
  domain first, with the largest determined variable's level replaced by one
  `value()` call, and keeps the tuples the relation accepts. Under `Auto` that
  is at most 100 leaves. Under an explicit `Tabulated`
  it is unbounded, and a wide domain runs out of memory rather than refusing
  at post time (#880). The same initialiser writes the table's derivation into
  the proof.
- **Initial contradictions**: `Power` with a constant base and exponent and no
  representable power; `Divide` / `Modulus` with a constant zero divisor.
- **`PowerTable`** materialises its whole table in `prepare()`, over the
  product of two initial domains, with no budget (#845). The large-domain
  audit lane pins this as `KnownTrip`.

Nothing else is computed at the root. A bounds propagator's first call is an
ordinary call.

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| `Plus` / `Minus` bounds | `on_bounds`, all three | derived: none | [sum-bounds](#rule-sum-bounds) | `BC`; `Tabulated`; `Auto` when tabulating | claims it | never |
| `Plus` / `Minus` interval | `on_change`, all three | derived: all three | [sum-interval-prune](#rule-sum-interval-prune), [sum-hull-fallback](#rule-sum-hull-fallback) | `GAC`; `Dynamic`; `Auto` when not tabulating (the default, and an aliased post over budget) | claims it | never |
| `Multiply` bounds | `on_bounds`, the distinct non-constant handles | derived: none | [product-bounds](#rule-product-bounds), [factor-bound](#rule-factor-bound), [zero-cofactor-contradiction](#rule-zero-cofactor-contradiction), [square-root-outer](#rule-square-root-outer), [square-root-inner](#rule-square-root-inner) | always, with two variable operands | claims it | never |
| `Power` | `on_bounds`, base, result and every link's operands, deduplicated | derived: none | [power-zero-base](#rule-power-zero-base), [stage-bound](#rule-stage-bound), [stage-gate-refutation](#rule-stage-gate-refutation), and every link's product rules | a constant exponent | claims it | never |
| `Divide` / `Modulus` | `on_bounds`, `x`, `y`, the result, `Modulus`'s `|q|` and both magnitudes | derived: none, **which under-reports `Divide`'s quotient**: [sign-open-magnitude-nonzero](#rule-sign-open-magnitude-nonzero) reads whether 0 is in `q`'s domain (see [Interior values](#interior-values-and-optional-pruning)) | [divisor-nonzero](#rule-divisor-nonzero) to [sign-open-magnitude-nonzero](#rule-sign-open-magnitude-nonzero), and the stage rules | a divisor that is not a constant zero | claims it | never |
| tabulation initialiser | — | — | [tabulate-relation](#rule-tabulate-relation), [tabulate-empty](#rule-tabulate-empty) | `Tabulated`, or `Auto` within budget (for `Plus` / `Minus`, only when aliased); `InitialiserPriority::Expensive` | n/a | n/a |
| tabulation, extensional | `on_change`, the enumerated underlying variables | derived: all of them | [table-prune](#rule-table-prune) | as the initialiser | claims it | `DisableUntilBacktrack` when no table was built |
| `Power`'s empty relation | initial contradiction | — | [power-empty-relation](#rule-power-empty-relation) | a constant base and exponent with no representable power | n/a | n/a |
| `Divide` / `Modulus`'s zero divisor | initial contradiction | — | [zero-divisor-contradiction](#rule-zero-divisor-contradiction) | a constant zero divisor | n/a | n/a |

**Delegated.** A constant-operand `Multiply` is a `LinearEquality`, and a
variable-exponent `Power` is a `Table`; their propagators are those families'.

**Idempotence.** Every propagator here claims it. All but the extensional
one, which is the table family's, get there by looping their whole pass
until a pass infers nothing:

- `Plus` / `Minus` bounds repeat after any pass that inferred something
  (`plus.cc:81-114`, `a8ee28ca`, #416). Over distinct variables that is a
  bound written across a hole of its own domain. **Under aliasing it can be
  one pass per value** (#1068).
- The interval propagator's single exact pass is already the fixpoint over
  distinct variables, because a survivor of each step keeps its support
  through the later steps (`gac.cc:53-62`). It repeats only when positions
  alias or a step fell back to a hull. Under aliasing that is also one pass
  per value on `Plus{x, y, x}` (#1068).
- `Multiply`, `Power` and `Divide` / `Modulus` loop until
  `made_progress_since_last_check()` is false.

The engine ignores the claim when two trigger positions share an underlying
variable (`propagators.cc:776-779`), which here includes `x · −x` and a
`Power` whose result is a view of its base: an under-claim, and harmless.

**Checked by this audit:** all four test binaries (`plus_minus_test`,
`multiply_test`, `power_test`, `divide_modulus_test`) at `--seed=1`, with
`GCS_CHECK_IDEMPOTENT_CLAIMS=1` in the environment and a local print
confirming the checker was on. At `f28fdef8` the harness's own lanes could
run with it silently off (#1056). All four pass, uncapped. The checker's
ability to catch a false claim was shown by a control in the `abs` audit; no
arithmetic control was run. **Since #1086** the harness switches the checker
on before anything propagates and throws if a harness solve finds it off, so
every harness solve now checks the claims; the family's four constraint tests
and their `view_mixed` twins pass that way at `61112ed0`, capped.

### Mutable state and incrementality

- **No backtrackable state** anywhere in the bounds propagators. Each call
  recomputes from the current bounds, and each computation is constant time:
  corner products, quotients, integer square roots, or two-term linear
  stages.
- **The interval propagator** keeps seven scratch vectors behind a
  `shared_ptr`, reused across wakes; each step still copies domains with
  `copy_of_values`, and builds a fresh reason per removed run. Their contents
  are dead between calls. Each call copies the three domains and
  rebuilds the Minkowski sums from scratch.
- **The tabulation's** live tuples and compact table are `State`,
  backtrackable, and the table family's.
- **Proof-side state** mutates without restore, correctly: the W-line cache in
  the grid cells, and `Divide` / `Modulus`'s `Top` line caches, name lines
  that are never deleted.
- **What maintaining more would buy.** On the propagation side, nothing: a
  call is constant time. On the proof side, every `Multiply` firing re-derives
  its chain from scratch, where `Divide` / `Modulus` cache theirs. That is
  where `Multiply`'s proof size comes from (see [Proof
  performance](#proof-performance)); #540 targets the case where a factor
  becomes fixed.
- **Dead fields**: `signed_multiply::Data`'s `x_init_lo/hi` and
  `y_init_lo/hi` are written and never read, and the header's reason for them
  is untrue (#1066).

### Interior values and optional pruning

**What this family offers:** `None.` No class installs an
optional-interior-pruning pair. `Auto` means "tabulate when small" (for
`Plus` / `Minus`, "when aliased and small"), decided once in `prepare()`.

**What this family observes** depends on the arm:

- **The product group's bounds propagators observe holes in one place only.**
  `Multiply`, `Power`, `Divide` and `Modulus` read `state.bounds`, plus two
  `O(1)` `in_domain` guards whose inference is unconditional (a zero base or
  divisor, removed once). **Since #1081, `Divide` / `Modulus` also read one
  interior value**: [sign-open-magnitude-nonzero](#rule-sign-open-magnitude-nonzero)
  infers `|v| ≥ 1` when 0 is missing from a sign-open `v`'s domain, for the
  divisor and for `Divide`'s quotient. For the divisor that read is always
  of the propagator's own removal: [divisor-nonzero](#rule-divisor-nonzero)
  takes 0 out at the top of the same pass. For the quotient it is not: a
  hole at 0 that another constraint makes is something this propagator can
  use, but its triggers are `on_bounds`, so the hole does not wake it, and its
  derived **Holes affect** omits `q`. That under-reports in the safe direction:
  never unsound, but another family's optional interior pruning on `q` can be
  switched off although `Divide` would use the removal of 0, and the inference
  waits for the next bounds wake. Found in this re-audit, by reading; #1102.
  Apart from that one value, **on their default arm over large domains, this
  is a family whose whole vocabulary is bounds.**
- **`Plus` and `Minus` observe holes on all three variables by default.** Their
  default is `Auto`, which is the interval propagator unless tabulating, and
  it reads interior values. Since `ef717662` made `Auto` mean `Dynamic` over
  distinct variables, a default `Plus` keeps other families' optional pruning
  alive on its variables. Before it, a default `Plus` over distinct variables
  ran the bounds propagator and kept none alive; only a small post that
  tabulated observed holes.
- **Tabulation observes holes** on every enumerated variable, through the
  table family's extensional propagator.

The triggers tell the truth everywhere but `Divide`'s quotient, above: no
propagator here declares `holes_affect_propagation`, and only `Divide` would
need to, for `q` alone. Otherwise the bounds propagators' `on_bounds`
triggers match what they read. The `Plus` bounds propagator's
hole-snap loop reacts only to its own writes, which `propagators.hh` counts
as unaffected.

### Robustness and limits

- **Unbounded domains.** Nothing walks a domain on any bounds path; see
  [Interval efficiency](#interval-efficiency). The limits are overflow's.
- **Negative values and zero.** Fully signed throughout. At `f28fdef8`
  `Divide`'s strength dropped sharply when an operand's sign was open (#1065);
  since #1081 it reaches the hull on every root fixture its test lists, and
  what remains short of that is under [quotient-sign](#rule-quotient-sign).
- **Degenerate shapes.** See [Semantics](#semantics). Untested: `Multiply{c1,
  c2, r}`; `Power` with `4 ≤ k ≤ 62` over a base that is not a singleton; `k =
  62` and `63`; `Power{x, k, x}` beyond `k = 2`; an all-constant, constant-zero
  or aliased `Divide` / `Modulus` in the chain.
- **Overflow.** Re-measured at `61112ed0` with one probe, against the same
  probe on the `f28fdef8` build; the first pass's figures are kept below it.
  - **Since #1079, propagation works at any width.** `product_bounds` and
    `square_bounds` saturate each corner at the end of `Integer`'s range. A
    saturated corner compared with `z`'s representable bounds either excludes
    nothing or is weaker than the true bound, so `Multiply` stays sound.
    `Divide` / `Modulus` do arithmetic on the product, so there a saturated
    lower corner refutes the node outright (`w ≤ |x|`, which is
    representable), and a bound whose sum would overflow is skipped
    (`sum_if_representable`), since past the end of the range it bounds
    nothing. Without proofs, every shape below now solves: `Multiply` with
    `x, y ∈ [0, 2^32 − 1]` and `[0, 2^40]` against `z ∈ [0, 2^60]`, `Modulus`
    and `Divide` with `x ∈ [0, 10^12]` and `y ∈ [1, 10^7]`, and `Power(x ∈ [0,
    2^31], 3, r ∈ [0, 2^61 − 1])`. At `f28fdef8` each of those threw
    `IntegerOverflow` during propagation.
  - **With proofs, the proof model still fails first, unchanged by #1079.**
    It sizes the grid's rows by the grid's largest sum, which has to fit in an
    `Integer`. The failure comes out of `solve_with`, when the proof model is
    built, not out of `Problem::post`. The headers now give the limit as 62
    bits of combined operand magnitude for `Multiply` (and so per `Power`
    link), and 63 bits of quotient and divisor magnitude for `Divide` /
    `Modulus`. Measured:
    - `Multiply`: two operands of `2^31 − 1` solve with proofs; at `2^31` and
      `2^32 − 1` it throws a `ProofError` ("cannot size the reification
      constant for a half-reified row").
    - `Modulus`, whose quotient magnitude is sized by the dividend: 33-bit
      `x` with 30-bit `y` solves; 32 + 32 and 34 + 30 throw `ProofError`. So
      63 bits of **dividend** and divisor.
    - `Divide`: the dividend counts too, because its remainder rows add `x`
      to the grid sum. With a 31-bit quotient and 31-bit divisor, dividends of
      10, 40 and 60 bits all solve. With a 32-bit quotient and 31-bit divisor,
      a dividend of up to 32 bits solves, and 33, 36, 40 and 60 bits throw
      `ProofError`. So the header's 63 holds only for a narrow dividend; in
      practice about 62.
    - When the grid would need more than about 64 bits, the error is an
      `UnimplementedException` from `power2` instead (`Multiply` at `2^40`
      per operand; `Modulus` with a 40-bit `x` and 31-bit `y`), not the
      `ProofError` the headers name.
    The `Divide`, `Modulus` and `Power` shapes above throw `ProofError` with
    proofs on, identically at `f28fdef8`. The fact-check of this re-audit
    measured the `Divide` / `Modulus` widths. **This is now the family's only
    width limit, and it is the proof's, not the propagator's.**
  - **`Plus` / `Minus`** are unchanged: `Integer`'s checked arithmetic throws
    on overflow, and nothing in either propagator catches it. The
    tabulation's acceptance test uses `add_overflows` / `sub_overflows`, so an
    overflowing tuple is rejected, not thrown.
  - **One `Power` edge survives, now documented** (`power.hh`): the
    constant-exponent path treats no base of magnitude two as having a
    representable power above `k = 62`, but `(−2)^63 = INT64_MIN` is one.
    `Power(x ∈ [−2, 2], 63, constant INT64_MIN)` still throws `IntegerOverflow`
    at `61112ed0`, as at `f28fdef8`; and, unchanged too, the variable-exponent
    path (`k ∈ [62, 63]`) finds `x = −2`.
  - **At `f28fdef8`**, before #1079: `Multiply`'s corner products threw once
    `|x|·|y|` could pass 2^63, whatever `z`'s domain (`Integer overflow:
    4294967295 * 4294967295` at `2^32 − 1`, during propagation, where the
    header said install time). `Divide` / `Modulus`'s magnitude corners threw
    in the same way; `Modulus` with `x ∈ [0, 10^12]`, `y ∈ [1, 10^7]` threw
    `1099511627775 * 10000000`, whose first factor is the quotient magnitude's
    starting bound, `2^40 − 1`, the shape `db5a9276` had fixed before the S3
    rewrite reintroduced corner products. `Power`'s auxiliaries' ranges
    saturated at posting time, but each link propagated through the same
    unguarded corners (`2305843009213693951 * 1518500249`).

  Every failure left fails loudly, never unsoundly. The large-domain audit
  lane now has a `wide-product` row per class whose corner products pass 2^63
  at the audit's width; its proof survey scales the operands down so that a
  proof can still be written.

### Interval efficiency

`Fine at any width` on every default arm **over distinct variables, with two
exceptions**. An aliased `Plus` or `Minus` can converge one value per pass
under every tag, 2.8 s at a width of 10^7 (#1068). And a `Power` with a
*variable* exponent always installs `PowerTable`, whatever consistency was
asked for, which walks `D(base) × D(exponent)` with **no budget** (#845): that
is a default dispatch, not an explicit request. The only other per-value site
is the tabulation's, which runs behind the 100-leaf budget under `Auto`, or
under an explicit `Tabulated`.

1. **Propagation.**
   - **Bounds propagators**: no value walks. The product group's only
     domain reads beyond bounds are three `O(1)` `in_domain` checks: the two
     zero guards and, since #1081, whether 0 is in a sign-open divisor's or
     quotient's domain. `Plus` /
     `Minus`'s loop repeats once per hole crossed by its own write over
     distinct variables, but under aliasing once per value (#1068), and it is
     not under `LargeDomainIterationCounter`.
   - **The interval propagator** uses `copy_of_values`,
     `IntervalSet::for_each_interval`, its own interval merge and
     `infer_not_in_range`. An exact step combines `|intervals(o1)|·|intervals(o2)|`
     pairs; the fallback combines interval sums. Both are guarded by
     `LargeDomainIterationCounter`. The repeat loop under aliasing is not, and
     it too can take one pass per value (#1068).
   - **The tabulation initialiser** walks values (`each_value_mutable`,
     `tabulation.cc:142`) by design, bounded by 100 leaves under
     `Auto` and unbounded under `Tabulated` (#880). The extensional
     propagator's support scan is per value; it is the table family's.
   - **`PowerTable`** walks `D(base) × D(exponent)` with no budget (#845).
     `power_table.cc:38` re-checks the exponent's membership for a value just
     drawn from its domain (#1066).
2. **Reasons.**
   - **The product group**: zero to six literals (divisor-nonzero and
     power-zero-base have empty reasons), never per value or per
     run, and unguarded by `want_reasons()` because they are constant size.
   - **`Plus` / `Minus` bounds**: two literals.
   - **`Plus` / `Minus` interval**: one literal per interval of two domains,
     per run, guarded by `want_reasons()`. But the lists are **rebuilt for
     every removed run of a step**, although they are the same for all of that
     step's runs, and they include holes that no lemma uses (`gac.cc:340-347`).
     So the finding work is `O(runs × (k_Y + k_Z))` per step.
3. **Proof.** No per-value line on any bounds or interval path:
   - `Plus` / `Minus`: at most `2·(interior intervals) + 2` lemmas per removed
     run, whatever the width. The interval propagator's per-value form is
     chosen only for a `{0, 1}` variable, which has no bit representation. That
     is a kind test rather than a width test, but it is harmless over two
     values.
   - The product group: per bit, `O(a·b)` terms per line. No width gate is
     needed.
   - Tabulation: per node of the enumeration tree, by construction.
4. **The audit lane** (`gcs/large_domain_audit_test.cc`), root only, proofs
   off, over `[0, 10^9]`. The outcomes are the rows' declared expectations,
   read at `61112ed0`; the lane was not run for the re-audit, since it is
   registered only in a `GCS_LARGE_DOMAIN_GUARD` build:

   | Row | Arm reached | Outcome |
   |---|---|---|
   | `Plus`, `Minus` | `Auto`, the interval propagator | `Clean` |
   | `Plus/holey`, `Minus/holey` | `GAC` | `Clean` |
   | `Plus/many-intervals` | `Auto`, falling back to the hull | `Clean` |
   | `Plus/many-intervals-gac` | `GAC` | `KnownTrip` |
   | `Multiply` | `Auto`, the bounds propagator | `Clean` |
   | `Divide`, `Modulus` | `Auto`, the bounds propagator | `Clean` |
   | `Multiply/wide-product`, `Divide/wide-product`, `Modulus/wide-product`, `Power/wide-product` (#1079) | the bounds propagators, with operands scaled from the probe width so that corner products pass 2^63; `Power` is a cube, so the link chain | `Clean` |
   | `Power` | a *variable* exponent, so `PowerTable` | `KnownTrip` |
   | `PowerTable` | `PowerTable` | `KnownTrip` |

   `Plus/two-intervals` is in its proof-size rows. **Axes the rows do not
   vary:**
   - no `BC` row for `Plus` / `Minus`, since `Auto` became `Dynamic`;
   - no `Tabulated` row for any class;
   - no view, no square, and no aliasing, which is where #1068 lives;
   - no negative or zero-spanning domain, which is where `Divide`'s
     sign-open rules and the magnitudes' bit-maximum overflow live;
   - no **constant-exponent** `Power` at the plain width: until #1079 its only
     row took the variable-exponent path; `Power/wide-product`, a cube, is now
     the link chain's one row;
   - and no proofs, where the encoding's own 62- or 63-bit limit bites. (The
     first pass also listed no operand pair wide enough for a corner product
     to pass 2^63; the `wide-product` rows are that, since #1079.)

## Inference catalogue

Facts that hold across the family:

- **No justification reads `state`.** Every bound value a derivation uses is
  captured before the inference and carried by the reason: the "far side"
  rule of `arithmetic-proofs.md`. The interval propagator's lemma emitter
  reads captured copies of the same domain lists its reason was built from.
- **Hints carry the constraint id only.** `hints::Plus`, `hints::Minus`,
  `hints::Multiply`, `hints::Power`, `hints::Divide` and `hints::Modulus` each
  hold `ConstraintID originator`; the wire form is the class name with
  `(constraint_id <id>)`. The interval propagator's `hints::PlusNotInRange` /
  `MinusNotInRange` add the subhint `not_in_range`. `hints::Plus` also holds
  a `pol_line`, which is not serialised. **Three mismatches an external tool
  must know about:**
  - `Power`'s link inferences carry `hints::Multiply`, with the `Power`'s id
    and no link index;
  - `Power`'s and `Divide` / `Modulus`'s stage inferences carry
    `hints::LinearEquality`, even for an inequality stage;
  - only `Power`'s zero-base, empty-relation and tabulation inferences carry
    `hints::Power`.

  A reconstructor dispatching on the wire name would look for a `Multiply` or
  a `LinearEquality` with that id and find a `Power` or a `Divide`. The link
  looks recoverable from the reason's variables, since each link's operand
  pair is distinct, but that is argued, not tested.
- **The product group follows McIlree's thesis, Chapter 7**, in cake's
  sign-magnitude flavour rather than the thesis's two's complement: Justification
  Subprocedures 7.1 (grid-sum lower bound, pure cutting planes) and 7.2
  (grid-sum upper bound, per-row subproofs), 7.3 and 7.4 (channelling), and
  Procedures 7.6 (product bounds), 7.7 and 7.8 (multiplicand bounds). The
  code's comments use the draft thesis's numbers, 7.5 and 7.6/7.7 (#1066).
  `Divide` and `Modulus` use 7.1, 7.2 and the multiplicand-bound refutation,
  but not 7.3 or 7.4: their operands are magnitudes already, channelled to the
  signed variables by linear stages.
  **Every JSP 7.1 or 7.2 chain contains `ia` lines**, restating operand
  bounds, and **every 7.2 chain contains `proof by contradiction` subproofs**,
  one per row. So any rule below that cites such a chain uses both, even
  when its entry names only the `pol` that consumes the chain.
  Sign cases are resolved by `conclude_by_sign_cases`, which is ours: one
  proof by contradiction whose subproof adds each live sign pattern's premise
  to the negated goal and cuts one sign dimension at a time. `[v ≥ 0]` and
  `[v < 0]` are complementary atoms, so no separate zero cases are needed.
- **Two derivation shapes close an inference.** `Multiply` and `Power` pass
  `ThenRUP::No` and emit their own closing **hinted** RUP, citing the sign-case
  resolution's line and the concluded literal's definitions; the larger kit of
  channel rows, sign clauses, grid `[r]` halves and atom definitions is on the
  per-case JSP 7.4 RUPs.
  `Divide` and `Modulus` pass `ThenRUP::Yes`, so the inferred literal follows
  by a hint-free RUP; their subproofs are hint-free too, because their premises
  drag view bits into the cut.
- **Vocabulary.** The product group uses two techniques this document adds to
  [Appendix A](TEMPLATE.md#appendix-a-proof-technique-vocabulary): `ia`
  (VeriPB's implied-constraint step), and `proof by contradiction` (a `red`
  with the empty witness and a subproof). The `ia` restatement of an operand
  bound is load-bearing: citing the definition directly verifies or not
  depending on coefficient values (`arithmetic-proofs.md`, "the justification
  layer").
- **Tightness.** Mutation lanes exist for `Plus`'s interval propagator only
  (three lanes and a control). Every other rule's field is `Not shown`.
- **`partial`, below,** always means bound pushes (or a value removal, where
  the entry says so) on the variables the entry's **Infers** names, short of
  `bounds(Z)` on the whole relation.
- **Firing counts.** Where an entry gives corpus counts, they come from local
  counters in this audit's build, over the runs listed under [Benchmarks and
  examples](#benchmarks-and-examples).

### Rule: sum-bounds

- **Infers** — a bound on one of `a`, `b`, `result` from the other two's
  bounds: six pushes per pass for `Plus` (`result ≥ lb(a) + lb(b)`, `result ≤
  ub(a) + ub(b)`, `a ≥ lb(result) − ub(b)`, …) and six for `Minus`. A wipe-out
  arrives as a contradiction from the same `infer`.
- **Fires when** — the `Plus` / `Minus` bounds propagator, on any bound
  change, under `BC`, `Tabulated` and a tabulating `Auto`. Not under the
  default arm. No MiniZinc corpus model posts either class.
- **Strength** — `bounds(Z)` on all three over distinct variables, at the
  fixpoint the loop reaches; conclusions snap into the domains. A
  unit-coefficient sum of integer intervals takes every integer in between,
  so here `bounds(R)` and `bounds(Z)` coincide; a brute-force check of 3,000
  random `BC` posts at `61112ed0` found no unsupported bound in the 1,837
  roots that did not fail. Under
  aliasing, `partial`: `x + x = r` with `x ∈ [0, 10]`, `r ∈ [0, 5]` leaves `x
  ≤ 5`, where `bounds(Z)` gives `x ≤ 2`.
- **Algorithm** — interval arithmetic on a unit-coefficient equality,
  constant time per pass. The loop repeats after any pass that inferred
  something. Over distinct variables that means a bound written across a hole
  of its own domain, so the passes are bounded by holes crossed. Under
  aliasing it can be **one pass per value** of a domain (#1068).
- **Why it is true** — from `a + b = result`, `result` lies between the sums
  of the bounds, and each operand between the differences.
- **Proof technique** — `pol` then `RUP`: `pol` adds the half of the equality
  whose coefficient on the concluded variable survives to the two reason
  literals' defining rows, skipping a constant's, at `Temporary`
  (`plus.cc:32-52`); the conclusion is then RUP. A three-term instance of
  the linear justification (JP 3.15, per
  [justification-techniques.md](../justification-techniques.md)). With no
  model, only the RUP is emitted.
- **Reason** — exactly two bound literals, the other two variables' bounds.
  Minimal. Built unconditionally, at constant size.
- **Assertion** — `reason ⇒ [v ≥ k]` or `reason ⇒ [v ≤ k]`.
- **Hint** — `hints::Plus` / `hints::Minus`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`: the id locates the row, and the
  concluded variable and direction pick the half.
- **Proof size** — one `pol` and one RUP, whatever the width.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` It runs alone only under `BC`, which two
  tagged rows test over small solid domains, solutions only. It also runs
  beside the table under the `Tabulated` rows and every tabulating aliased
  `Auto` row. Nothing directs the hole-snap repeat.

### Rule: sum-interval-prune

- **Infers** — `X ∉ [lo, hi]` for each maximal run of `X`'s domain outside the
  signed Minkowski sum of the other two domains, for `X` each of `result`,
  `a` and `b` in turn. A run covering the whole domain is a contradiction.
- **Fires when** — the interval propagator, on any domain change, under
  `GAC`, `Dynamic` and the default `Auto` over distinct variables.
- **Strength** — `GAC` over distinct variables, when no step fell back to a
  hull: one pass is the fixpoint. Under aliasing a domain read as one operand
  is stale when pruned as another, so the pass repeats and the result is
  `partial`: sound, but short of GAC.
- **Algorithm** — `signed_sum` combines every pair of intervals, sorting only
  when both lists have more than one interval, then merges:
  `O(k_1·k_2·log(k_1·k_2))` in **intervals**. Finding the runs to remove is
  a merge, `O(k_X + k_supported)`.
- **Why it is true** — `X = −c_X(c_1·o_1 + c_2·o_2)`, so a value of `X`
  outside that set of sums has no support.
- **Proof technique** — `pol` then `RUP`, ours (no published procedure;
  `large-domains.md` states it). The lemmas are `pol`s, each saturated into a
  clause, at `Temporary`, each "one of the bounds propagator's six rules,
  stated at an interval's endpoints" (`gac.cc:214-232`); one RUP then closes
  the conclusion. Not a `RUP sequence`: the lemmas are cutting-planes lines,
  not RUP steps. For a removed run of `X`, each interval of `Y` defines a window
  of `Z`, the third variable. Then there is an optional prefix lemma, in which
  `Z`'s near bound pushes `Y` past every window below it. Each interior
  interval of `Y` gets a pair: `Y` pushes `Z` into the hole holding its
  window, and `Z` pushes `Y` past the interval. An optional suffix lemma
  pushes `Z` past its far bound. `X` itself is never pushed; its run is the
  conclusion. The closing RUP walks `Y` upwards through the reason's hole
  literals. `Y` is the operand with fewer intervals (`gac.cc:238-316`). The emitter
  checks that every lemma's conditions contradict its half and throws
  otherwise.
- **Reason** — `Y`'s and `Z`'s domains, stated exactly as the lists the
  support was computed from: `var = v` for a point, otherwise its bounds and
  one `∉` per hole. One literal per interval, per removed run. Not minimal:
  holes in the prefix and suffix regions are stated though no lemma uses them.
  Guarded by `want_reasons()`; without reasons it is `JustifyUsingRUP` and
  `NoReason`.
- **Assertion** — `reason ⇒ [X ∉ [lo, hi]]`, a range literal. The per-value
  form is chosen when `X` has no bit representation, which for these
  arguments means a `{0, 1}` variable: a kind test, harmless over two values.
- **Hint** — `hints::PlusNotInRange` / `MinusNotInRange`: `originator`
  (`ConstraintID`), subhint `not_in_range`.
- **Offline reconstructibility** — `hinted`: the run is in the assertion, both
  other domains are in the reason, and the walk operand is recomputable by the
  same rule.
- **Proof size** — at most `2·(interior intervals of Y) + 2` lemmas and a RUP
  per removed run, **independent of width**. Measured elsewhere: "608 lines
  at every width from 10^2 to 10^9" for `Plus/two-intervals` (`5bf08790`'s
  message), not re-measured here.
- **Gaps** — `None.`
- **Tightness** — **shown, for `Plus`.**
  - **Lanes:** `plus_mutation_lemmas` (no lemmas at all),
    `plus_mutation_hole_lemmas` (stop at the first interior interval) and
    `plus_mutation_window_holes` (state `Z` by its hull in the reason) each
    expect VeriPB to reject, and `plus_mutation_control` verifies the honest
    proof.
  - **The fixture:** `a` takes `w`'s hole only under a decision, through an
    `EqualsIf`, so the hole is not a root fact. `OmitLemmas` is rejected
    earlier, at the root run `[49, 60]`, whose windows lie past `a`'s bounds.
  - **`Minus` is not shown, by design** (`plus_minus_mutations.hh:18-20`).

### Rule: sum-hull-fallback

- **Infers** — as [sum-interval-prune](#rule-sum-interval-prune), but against
  `o_1 + hull(o_2)` and then `hull(o_1) + o_2`.
- **Fires when** — the interval propagator under `Dynamic` or the default
  `Auto`, on a step whose exact form would combine more than 1024 pairs of
  intervals. A fallback forces another pass. Directed by the
  `plus_minus_constraint_dynamic_fallback` lane, with the threshold set to 0.
- **Strength** — `partial`: at least the six bound rules' pruning, plus any gap
  wider than the other operand's range. Not GAC, and not claimed to reach
  `bounds(D)`.
- **Algorithm** — `O(k_1 + k_2)` interval sums per sub-step.
- **Why it is true** — a hull is a superset of its domain, so a value
  unsupported against it is unsupported against the domain.
- **Proof technique** — `pol` then `RUP`, as sum-interval-prune: saturated
  `pol` lemmas and one closing RUP. The hull is the shorter list,
  so it is the walked operand `Y`, and the windows still fall against `Z`'s
  holes: interior lemma pairs occur here too.
- **Reason** — as sum-interval-prune, with the hull operand stated by its
  bounds only. `hints.hh:72-74` says the reason states both domains
  "exactly"; under the fallback it does not (#1066).
- **Assertion** — as sum-interval-prune.
- **Hint** — as sum-interval-prune.
- **Offline reconstructibility** — `hinted`, as sum-interval-prune; a
  reconstructor sees a bounds-only operand in the reason.
- **Proof size** — as sum-interval-prune.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: product-bounds

- **Infers** — `z ≤ max` and/or `z ≥ min` of `x·y` over the current box, as one
  batch. For a square, the hull of `x²` over `x`'s interval. A wipe-out
  arrives as a contradiction when a bound is applied.
- **Fires when** — the `Multiply` propagator and every `Power` link, every
  pass, when a corner tightens `z`. Under every tag, since the bounds
  propagator is always installed. **The most common inference in the
  family**: on `train` 2014 `instance.1` over 20 s, 8,592,614 firings, 859,127 of them
  moving both bounds; on `opd` 2017 to its 17th solution, 553,230.
- **Strength** — `bounds(R)` on `z`, for distinct operands and for a
  square: the corners (or `lo²`, `hi²` and 0 for a square) give the **exact**
  image of the box, so every value between them, `z`'s surviving bounds
  included, is `x·y` for some real `x` and `y` in their bounds. **Not
  `bounds(Z)`**, which the first pass claimed: intersecting the exact hull
  with `z`'s domain can leave an endpoint no integer product reaches. Under
  `BC`, `x·y = z` with `x, y ∈ 2..4` and `z ∈ 5..15` is a fixed point, and
  none of the seven solutions has `z` equal to 5 or 15 (they take `z ∈ {6, 8,
  9, 12}`). The square is the same: `x·x = z` with `x ∈ −3..3` and `z ∈ 2..8`
  reaches `x ∈ −2..2`, `z ∈ 2..4`, and both solutions have `z = 4`. On 3,000
  random boxes under `BC`, each domain an interval of up to 9 values within
  `−6..14`, 131 of the 1,692 roots that did not fail (7.7%) left an
  integer-unsupported bound on `z`, 5 of them at both ends; for squares, 50 of 1,243 (4%), and never
  on `x`. All checked at `61112ed0` by brute-force probe. Under the default
  `Auto`, both examples are within the tabulation budget, and the square's
  root then reaches `z = 4`.
- **Algorithm** — four corner products, or two squares, in constant time. The
  propagation rule is the standard one (Apt and Zoeteweij; Schulte and
  Stuckey).
- **Why it is true** — `x·y` over a box takes its extremes at the corners; `x²`
  over an interval spanning zero has minimum 0, and otherwise takes its
  minimum at the endpoint of least magnitude.
- **Proof technique** — `ia`, `pol`, `hinted RUP` and `proof by contradiction`,
  by thesis Justification Procedure 7.6, cake flavour
  (`signed_multiply.cc:123-187`):
  1. four operand-bound lines, each an `ia` citing the bound atom's
     definition, or a RUP for a constant or a primitive atom;
  2. per live sign pattern (at most four; a square's mixed patterns are dead):
     channel each operand to its magnitude (JSP 7.3), then, **only for the
     directions being inferred**, the grid-sum bound (JSP 7.1 or 7.2), then
     channel the grid sum to `z` (JSP 7.4, a `pol` against `mag_Z` and a
     hinted RUP of the bound);
  3. per direction, `conclude_by_sign_cases` with subproof hints, and a
     closing hinted RUP citing its line and the literal's definitions.

  Preconditions: the premises' sum terms cancel exactly against the negated
  goal, which is why the subproof's RUPs can be hinted. Order-bridge `pol`
  lines are derived for each reason and case literal, because unit
  propagation cannot cross between two order atoms of one variable.
- **Reason** — `{x ≥ x_lo, x ≤ x_hi, y ≥ y_lo, y ≤ y_hi}`, shared by both
  directions. Not minimal: a non-negative box needing only upper bounds still
  cites the lower ones.
- **Assertion** — `reason ⇒ [z ≤ hi]` and/or `reason ⇒ [z ≥ lo]`.
- **Hint** — `hints::Multiply`: `originator` (`ConstraintID`), the `Power`'s
  own for a link.
- **Offline reconstructibility** — `hinted`: the id locates the encoding by
  label, the box is the reason, and the bound is the assertion.
- **Proof size** — per firing, `O(live patterns × directions × n)` lines,
  each `O(m)` terms, with `n` and `m` the operands' bit widths: per bit, never
  per value. Plus `2nm` W-lines at `Top`, once per grid. Measured by the
  inventory agent on a root-only probe at this commit: about `11n + 63` lines
  with one live pattern and both directions, and `36n + 76` with four.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: factor-bound

- **Infers** — `t ≤ hi` and/or `t ≥ lo` for the target `t ∈ {x, y}`, from the
  cofactor's and `z`'s bounds. An empty range is inferred as two crossing
  bounds and wipes the domain.
- **Fires when** — the `Multiply` propagator and every `Power` link, for
  distinct operands only, after product-bounds: `x`, then `y`. On `train`
  2014 `instance.1` over 20 s, 2,577,941 upper bounds and no lower bounds; on `ship-schedule`
  2014, 522 lower and 54 upper.
- **Strength** — `partial`. The quotient filter is JaCoP's `IntDomain` case
  split, "sound but not exact" (`product_bounds.hh:142-144`): corner quotients
  can leave an unsupported endpoint, and a zero-spanning cofactor gives only
  `[−max|z|, max|z|]`. On the random boxes under
  [product-bounds](#rule-product-bounds), 37 of the 1,692 roots that did not
  fail left an integer-unsupported bound on `x`, and 36 on `y`. `product_bounds_test` pins the known inexactness, and
  `multiply.hh`'s "bounds consistent multiplication" overstates it (#1066).
- **Algorithm** — no filter when 0 lies in both the cofactor's and `z`'s
  bounds; otherwise drop a zero endpoint and take floor and ceiling corner
  quotients. Constant time.
- **Why it is true** — with the cofactor bounded away from zero on one side,
  `t = z / cofactor` lies between the extreme corner quotients. With the
  cofactor spanning zero and `z` excluding zero, `|t| ≤ |z|`, because a
  non-zero cofactor has magnitude at least 1.
- **Proof technique** — `ia`, `pol`, `hinted RUP`, `RUP` and `proof by
  contradiction`, by thesis Justification Procedures 7.7 and 7.8: refute the
  excluded range. One side of it is an assumed atom, introduced by `ia`; the
  far side is the target's current bound, from the reason. Per live pattern:
  - channel both operands, lifting a spanning cofactor's magnitude to 1 under
    `[cof ≠ 0]` by a RUP;
  - derive **both** grid-sum bounds and both result channellings;
  - clash, by `pol` and `saturate`, with whichever of `z`'s bounds is
    violated. The code throws `UnexpectedException` if neither is.

  Then `conclude_by_sign_cases`, using the clash clauses directly, and the
  closing hinted RUP.
- **Reason** — `{z ≥ z_lo, z ≤ z_hi, cof ≥ cof_lo, cof ≤ cof_hi}` and the
  target's current bound on the far side. Not minimal: only one of `z`'s
  bounds does the clash.
- **Assertion** — `reason ⇒ [t ≤ hi]` / `reason ⇒ [t ≥ lo]`.
- **Hint** — `hints::Multiply`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`, as product-bounds. Which of `z`'s
  bounds clashes is recomputable from the reason's values.
- **Proof size** — `O(live patterns × n)` lines of `O(m)` terms. Measured by
  the inventory agent: about `11n + 51` lines with one live pattern, and about
  `22n + 70` per firing with a spanning cofactor. **Suspected waste**: each pattern
  derives both grid bounds and both result channellings, and uses one side.
  The same waste in product-bounds was removed by `0eaeaa48`. Not measured in
  isolation.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: zero-cofactor-contradiction

- **Infers** — a contradiction.
- **Fires when** — for distinct operands, when the cofactor is fixed to 0 and
  `z`'s bounds exclude 0. Fired on no corpus run counted here.
- **Strength** — `checker`, on the sub-case of a fixed zero cofactor.
- **Algorithm** — constant time.
- **Why it is true** — `0 · t = 0`, which is not in `z`'s domain.
- **Proof technique** — `RUP`, hint-free. `[cof = 0]` zeroes its magnitude
  bits and so the grid; a sign clause gives `[z ≥ 0]`; the result channel gives
  `z = 0`, against `[z ≠ 0]`. The thesis says the same case "follows by RUP"
  (§7.3.3).
- **Reason** — `{cofactor = 0, z ≠ 0}`. Weaker than the `z` bounds actually
  observed, but sufficient.
- **Assertion** — `[cofactor ≠ 0] ∨ [z = 0]`.
- **Hint** — `hints::Multiply`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `offline`.
- **Proof size** — one hint-free RUP, whose check costs `O(live database)`.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: square-root-outer

- **Infers** — `x ≤ isqrt(z_hi)` and `x ≥ −isqrt(z_hi)`.
- **Fires when** — a square (`x` in both slots, the same handle), after
  product-bounds, when `z_hi ≥ 0` and the bound tightens. On the corpus only
  `gbac` and `routing-flexible` post squares; over 20 s the two square rules
  together fired 28,565 times on `gbac` 2016 and 151,702 on `routing-flexible`
  2017.
- **Strength** — with square-root-inner, `bounds(Z)` on `x`: the two give the
  exact hull of `{x : x² ∈ [z_lo, z_hi]}` (`product_bounds_test` checks
  `square_filter`, which the propagator inlines rather than calls). An integer
  `x` at either end of that hull has `x²` in `[z_lo, z_hi]` by construction;
  the brute-force check under [product-bounds](#rule-product-bounds) found no
  counterexample on `x` in 1,243 roots. `z` is only `bounds(R)`.
- **Algorithm** — integer Newton `isqrt`, `O(log z)` iterations.
- **Why it is true** — `x² ≤ z_hi ⇔ |x| ≤ ⌊√z_hi⌋`.
- **Proof technique** — `ia`, `pol`, `hinted RUP`, `RUP` and `proof by
  contradiction`, as [factor-bound](#rule-factor-bound), with the
  cofactor sharing the target's excluded range, so that the refuted product is
  `(t ± 1)²`. The outer clamp runs before the inner lift, so that every refuted
  branch is uniformly too big or too small, which is when the box-shaped case
  refutations apply.
- **Reason** — `{z ≥ z_lo, z ≤ z_hi, x ≥ cur_lo, x ≤ cur_hi}`: both of `x`'s
  bounds, because the cofactor is the target.
- **Assertion** — `reason ⇒ [x ≤ u]` / `reason ⇒ [x ≥ −u]`.
- **Hint** — `hints::Multiply`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`.
- **Proof size** — as factor-bound, one live pattern per sign. The inventory
  agent's square probes wrote 319 to 1,119 lines for several firings at 5 to
  25 bits.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: square-root-inner

- **Infers** — with `m = ⌈√z_lo⌉` and `z_lo > 0`: `x ≥ m` when no value `≤ −m`
  remains, else `x ≤ −m` when no value `≥ m` remains.
- **Fires when** — a square, after the outer clamp, against the tightened
  domain. Counted together with square-root-outer.
- **Strength** — `bounds(Z)` on `x`, together with square-root-outer.
- **Algorithm** — `ceil_isqrt`, `O(log z)`.
- **Why it is true** — `x² ≥ z_lo > 0 ⇔ |x| ≥ m`.
- **Proof technique** — `ia`, `pol`, `hinted RUP`, `RUP` and `proof by
  contradiction`, as square-root-outer. The excluded middle `(−m, m)`
  contains 0, so the zero case is refuted through the grid against `z`'s
  positive range, as a `[x ≠ 0]` unit.
- **Reason** — as square-root-outer.
- **Assertion** — `reason ⇒ [x ≥ m]` / `reason ⇒ [x ≤ −m]`.
- **Hint** — `hints::Multiply`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`.
- **Proof size** — as square-root-outer.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: power-zero-base

- **Infers** — `base ≠ 0`.
- **Fires when** — the `Power` propagator with a negative constant exponent,
  while 0 is in the base's domain: once, in effect, at the root.
- **Strength** — `partial`, a value removal.
- **Algorithm** — one `in_domain` check.
- **Why it is true** — `0^−n` is undefined under MiniZinc's semantics.
- **Proof technique** — `RUP` against `@c[id][nonzero]`.
- **Reason** — empty.
- **Assertion** — `[base ≠ 0]`.
- **Hint** — `hints::Power`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: power-empty-relation

- **Infers** — a contradiction at the root.
- **Fires when** — `Power` with a constant base and exponent whose power is not
  representable (an overflow, or `0^−n`). An initial contradiction.
- **Strength** — `checker`.
- **Algorithm** — `checked_integer_power` in `prepare()`.
- **Why it is true** — the relation has no tuple.
- **Proof technique** — `RUP` against the `≥ 1` row over nothing.
- **Reason** — none.
- **Assertion** — the empty clause.
- **Hint** — `hints::Power`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: stage-bound

- **Infers** — bound pushes on the terms of one linear stage.
- **Fires when** — the `Power` or `Divide` / `Modulus` propagator, every pass,
  for each stage whose gate holds on the bounds (`linear_stages.cc:26-35`).
  - **`Power`**: `k = 0` gives `result = 1`, and `k = 1` gives `base = result`.
    A negative `k` gives `base ≥ 2 ⇒ result = 0` and `base < −1 ⇒ result = 0`
    (with the `nonzero` row). A `k` above 62 gives `−1 ≤ base ≤ 1` and `base =
    0 ⇒ result = 0` instead. Both give `base = 1 ⇒ result = 1` and `base = −1
    ⇒ result = ±1` by parity. A constant base gives `result = base^k`.
  - **`Divide`**: the channels of `|q|` and `|y|` as eight gated stages.
  - **`Modulus`**: `r − |y| ≤ −1` and `−r − |y| ≤ −1`, ungated; `r ≥ 0` gated
    on `x ≥ 0` and `r ≤ 0` gated on `x < 1`; the four `|y|` stages.
- **Strength** — `partial`: `bounds(Z)` on each stage's own row. Every
  stage has at most two terms, all with coefficient ±1, where the sweep's
  `bounds(R)` is also `bounds(Z)`. The stages are gated on an operand's sign,
  so a stage never carries a magnitude bound to an operand whose sign is
  open. At `f28fdef8` nothing else did either, which was half of #1065; since
  #1081, [sign-open-clamp](#rule-sign-open-clamp) and
  [sign-open-magnitude-cap](#rule-sign-open-magnitude-cap) do it for the
  divisor and for `Divide`'s quotient.
- **Algorithm** — `propagate_linear` over stages of at most two terms. The
  linear family's rule: see [linear.md](linear.md).
- **Why it is true** — each stage is a row of the encoding, or the half of one
  that its gate selects.
- **Proof technique** — the linear family's `pol` then `RUP`, with the gate as
  an extra reason literal. The stages are built directly as `LinearStage`s
  over rows this family's model wrote; no `Linear` constraint is posted.
- **Reason** — the linear family's, plus the gate literal.
- **Assertion** — `reason ⇒` a bound on one term.
- **Hint** — `hints::LinearEquality`: `originator` (`ConstraintID`), the
  `Power`'s, `Divide`'s or `Modulus`'s own id, also for an inequality stage.
- **Offline reconstructibility** — `hinted`, by the linear family's argument,
  once the tool knows the id is not a `LinearEquality`'s. The stage's row is
  found by its role label.
- **Proof size** — the linear family's, over two terms.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: stage-gate-refutation

- **Infers** — the negation of a stage's gate, such as `base ≠ 1`, `base < 2`
  or `x ≤ −1`, when the gated row is already violated on the bounds.
- **Fires when** — the same propagators, for each gated stage whose gate does
  not yet hold (`linear_stages.hh:114-152`). For `Divide` this refutes a
  sign of `q` or `y` from its magnitude's bounds; for `Modulus`, also `x`'s
  sign from `r`'s bounds.
- **Strength** — `partial`.
- **Algorithm** — the row's least possible left-hand side, in its terms.
- **Why it is true** — the contrapositive of a half-reified row.
- **Proof technique** — `pol` (`justify_linear_contrapositive`) then `RUP`.
- **Reason** — one bound literal per term of the row.
- **Assertion** — `reason ⇒ ¬gate`.
- **Hint** — `hints::LinearEquality`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`, as stage-bound.
- **Proof size** — one `pol` and one RUP.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: divisor-nonzero

- **Infers** — `y ≠ 0`.
- **Fires when** — the `Divide` / `Modulus` propagator, every pass, while 0
  is in `y`'s domain: in effect once, at the root. No corpus run counted here
  reaches it, because every corpus divisor is positive.
- **Strength** — `partial`, a value removal.
- **Algorithm** — one `in_domain` lookup.
- **Why it is true** — `y = 0` is outside the relation.
- **Proof technique** — `RUP` against `@c[id][nonzero]`.
- **Reason** — empty.
- **Assertion** — `[y ≠ 0]`.
- **Hint** — `hints::Divide` / `hints::Modulus`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: quotient-sign

- **Infers** — `q ≥ 0` or `q ≤ 0`, for `Divide` only.
- **Fires when** — `x`'s sign is decided, strictly or weakly, and `y`'s
  strictly: `x ≥ 1 ∧ y ≥ 1 ⇒ q ≥ 0`, `x ≥ 1 ∧ y ≤ −1 ⇒ q ≤ 0`, the two
  mirrors, and, **since #1081**, the same four with `x ≥ 0` or `x ≤ 0` in
  place of the strict sign, since `x = 0` gives `q = 0`; the weak case
  concluding `q ≥ 0` also needs `|y|`'s lower bound at least 1, since its grid
  derivation uses it. At `f28fdef8` it fired
  only on strictly signed operands, and never on the corpus runs counted
  there; the new cases have not been counted on the corpus.
- **Strength** — `partial`. With [divisor-sign](#rule-divisor-sign) and the
  three sign-open rules, `Divide` now reaches the
  hull at the root on every fixture `divide_modulus_test` lists, including
  `x ∈ [0, 20]`, `y ∈ [3, 4]`, `q ∈ [−1, 50]`, where the first pass measured
  `q` left at `[−1, 50]` against a hull of `[0, 6]`. Re-measured under `BC`
  and branching on `x`, `y`, `q` in order, enumerating all solutions: that
  fixture goes from 102 failures to none, and `x ∈ [0, 100]`, `y ∈ [1, 10]`,
  `q ∈ [−100, 100]` from 2,000 to none. **What remains short of the hull**, per the test's own
  comment: an operand whose sign is open needs a case split the propagator
  does not make (`x ∈ [−5, 20]`, `y ∈ [3, 4]` leaves `q ∈ [−6, 6]`, not `[−1,
  6]`), and a variable divisor's own bounds need not be exact (`x ∈ [−9,
  −7]`, `y ∈ [1, 3]`, `q ∈ [−6, −3]` leaves `y = 1`, and with it `q = −6`).
- **Algorithm** — a handful of bound reads.
- **Why it is true** — a truncated quotient of same-sign operands is at least
  0, and of opposite-sign operands at most 0; a zero dividend gives 0.
- **Proof technique** — `RUP` against the sign clauses `sgn_pp`, `sgn_pn`,
  `sgn_nn` or `sgn_np`, for the strict cases and for `q ≤ 0` from a weak
  sign, where `sgn_x0` (`x = 0 ⇒ q ≤ 0`) closes the zero case. **`q ≥ 0` from a
  weak sign has no sign clause for `x = 0`**, so it goes through the grid:
  once per constraint, at `ProofLevel::Top`, a `pol` gives `[q < 0] ⇒ |q| ≥ 1`
  off the quotient's channel, and a JSP 7.1 chain (`ia`, `pol`) gives `[q <
  0] ∧ [|y| ≥ 1] ⇒ S ≥ 1`; the inference then closes by a hint-free `RUP`
  against the remainder rows' `S ≤ 0` at `x = 0`. No case split on `x = 0` is
  needed: under the negated claim the sign clause forces `x` out of the
  strict case, and `x ≥ 0` with `x < 1` pins `x`'s bits by unit propagation
  (`31fe23b8`'s comment).
- **Reason** — the two sign literals, minimal, except for `q ≥ 0` from a
  weak sign, which adds `|y| ≥ 1`. That literal must stay: the cached grid
  line carries `[q < 0]` and `[|y| ≥ 1]` as its own terms, and unit
  propagation does not reliably reach `|y| ≥ 1` from `y`'s sign through the
  channel (`divide_modulus.cc`, at `61112ed0`).
- **Assertion** — `[x ⋯] ∧ [y ⋯] ⇒ [q ≥ 0]` / `[q < 1]`, and `[x ≥ 0] ∧ [y ≥ 1]
  ∧ [|y| ≥ 1] ⇒ [q ≥ 0]` (or the mirror) for the grid case. For example, `x <
  1 ∧ y ≥ 1 ⇒ q < 1` is `a 1 ~i[q][ge1] 1 i[x][ge1] 1 ~i[y][ge1] >= 1`.
- **Hint** — `hints::Divide`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `offline`, except `q ≥ 0` from a weak
  sign, which is `hinted`: the id locates the grid and the channel, and the
  reason gives the bound the JSP 7.1 chain needs.
- **Proof size** — one line; the grid case adds its `Top` lines once, a JSP
  7.1 chain of `O(n_a)` lines.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` The root-hull fixtures fail on the old
  propagator (`78f22dee`'s message), which shows the rule matters to
  strength, not that its derivation is tight.

### Rule: divisor-sign

- **Infers** — `y ≥ 1` or `y ≤ −1`, for `Divide` only. New in #1081.
- **Fires when** — `x` and `q` both have strictly decided signs and `y`'s
  sign is open: same signs give `y ≥ 1`, opposite signs give `y ≤ −1`.
- **Strength** — `partial`.
- **Algorithm** — six bound reads.
- **Why it is true** — the sign clauses read backwards: a strictly signed
  quotient of a strictly signed dividend fixes the divisor's sign, and `y = 0`
  is outside the relation.
- **Proof technique** — `RUP` against `sgn_pp`, `sgn_pn`, `sgn_nn` or `sgn_np`,
  with `@c[id][nonzero]` excluding `y = 0`.
- **Reason** — the two sign literals. Minimal.
- **Assertion** — `[x ⋯] ∧ [q ⋯] ⇒ [y ≥ 1]` / `[y < 0]`. For `x ∈ [5, 20]`,
  `q ∈ [2, 50]`, `y ∈ [−4, 4]`: `a 1 i[y][ge1] 1 ~i[x][ge1] 1 ~i[q][ge1] >= 1`.
- **Hint** — `hints::Divide`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: product-interval-empty

- **Infers** — a contradiction.
- **Fires when** — the `Divide` / `Modulus` propagator, when its local interval
  for the grid sum `S = |q|·|y|` is empty. The interval is the magnitudes'
  corner product, intersected with what the gated remainder or identity rows
  allow from `x` (and `r`) once `x`'s sign is decided, or with the hull of
  both branches when it is not. Each bound remembers which of these set it.
  On `harmony` 2024 over 20 s, 7,088 times.
- **Strength** — `partial`.
- **Algorithm** — constant-time arithmetic on bounds.
- **Why it is true** — both sides are valid bounds on `S`, so an empty
  intersection is a contradiction.
- **Proof technique** — `pol` then `RUP`, over chains that themselves contain
  `ia` lines and, for JSP 7.2, `proof by contradiction` subproofs (see the
  preamble). The two chain lines are added by `pol`, because "RUP cannot
  combine two opposing linear bounds on the grid sum". A magnitude side is a
  JSP 7.1 or 7.2 chain; a dividend side is one `pol` over
  a remainder or identity row plus cached operand bounds; an undecided sign
  is a `proof by contradiction` over `[x ≥ 0]` / `[x < 0]`.
- **Reason** — the literals of whichever side set each bound. It may repeat a
  literal when both sides are the hull.
- **Assertion** — `reason ⇒ ⊥`.
- **Hint** — `hints::Divide` / `hints::Modulus`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`: which side set each bound is
  recoverable from the reason. Magnitude bounds mean the corner product, an
  `x` sign literal means a gated row, and both of `x`'s bounds with no sign
  literal mean the hull.
- **Proof size** — constant, in lines, when the chains are cached; `O(n_a)`
  lines on a cache miss for a magnitude side. Each line citing a remainder or
  identity row carries its `n_a·n_b` grid terms. Not measured per firing.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: dividend-from-product

- **Infers** — for `Divide`, `x ≥ |q|_lo·|y|_lo` when `x ≥ 0` is decided, and
  `x ≤ −|q|_lo·|y|_lo` when `x ≤ 0` is.
- **Fires when** — the `Divide` / `Modulus` propagator, for `Divide`, with
  `x`'s sign decided. 455 times on `rotating-workforce` 2019 over 20 s.
- **Strength** — `partial`.
- **Algorithm** — one product of lower bounds.
- **Why it is true** — `rem_pos_lo` says `x ≥ S`, and `S ≥ |q|_lo·|y|_lo`;
  mirror through `rem_neg_hi`.
- **Proof technique** — `ia` (inside the chain), `pol` (a cached JSP 7.1 chain
  and `rem_pos_lo` or `rem_neg_hi`) then `RUP`.
- **Reason** — `{|q| ≥ a_lo, |y| ≥ b_lo}` and the sign literal of `x`.
- **Assertion** — `reason ⇒ [x ≥ a_lo·b_lo]`, or the mirror.
- **Hint** — `hints::Divide`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`.
- **Proof size** — as product-interval-empty.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: dividend-sign-refutation

- **Infers** — for `Divide`, `x ≤ −1` when `|q|_lo·|y|_lo > x_hi`, and `x ≥ 1`
  when it exceeds `−x_lo`, with `x`'s sign undecided.
- **Fires when** — as dividend-from-product, with `x`'s sign open. Never on
  the corpus runs counted here.
- **Strength** — `partial`.
- **Algorithm** — as dividend-from-product.
- **Why it is true** — under `x ≥ 0`, `x ≥ S ≥ |q|_lo·|y|_lo > x_hi` is
  impossible; mirror under `x ≤ 0`.
- **Proof technique** — `ia` (inside the chain), `pol` then `RUP`, as
  dividend-from-product.
- **Reason** — `{|q| ≥ a_lo, |y| ≥ b_lo}` and `x ≤ x_hi` (or `x ≥ x_lo`).
- **Assertion** — `reason ⇒ [x ≤ −1]` / `reason ⇒ [x ≥ 1]`.
- **Hint** — `hints::Divide`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`.
- **Proof size** — as product-interval-empty.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: dividend-magnitude-cap

- **Infers** — for `Divide`, `x ≤ |q|_hi·|y|_hi + |y|_hi − 1` and its negation
  as a lower bound, whatever `x`'s sign.
- **Fires when** — the `Divide` / `Modulus` propagator, for `Divide`. 13 times
  on `rotating-workforce` 2019 over 20 s.
- **Strength** — `partial`.
- **Algorithm** — one product of upper bounds.
- **Why it is true** — `|x| − S ≤ |y| − 1`, from `rem_pos_hi` and `rem_neg_lo`.
  The negated claim pins `x`'s sign, which activates the matching row.
- **Proof technique** — `ia` and `proof by contradiction` (inside the JSP 7.2
  chain), `pol` (the cached chain, `rem_pos_hi` or `rem_neg_lo`, and a cached
  `|y| ≤ b_hi`) then `RUP`.
- **Reason** — `{|q| ≤ a_hi, |y| ≤ b_hi}`.
- **Assertion** — `reason ⇒ [x ≤ cap]` / `reason ⇒ [x ≥ −cap]`.
- **Hint** — `hints::Divide`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`.
- **Proof size** — as product-interval-empty, JSP 7.2 on a miss.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: divisor-magnitude-floor

- **Infers** — for `Divide`, `|y| ≥ x_lo − w_hi + 1` when `x ≥ 0` is decided,
  or `|y| ≥ 1 − x_hi − w_hi` when `x ≤ 0` is, with `w_hi` the grid sum's upper
  bound.
- **Fires when** — as dividend-from-product. Never on the corpus runs counted
  here.
- **Strength** — `partial`, on the magnitude; it reaches `y` through
  stage-bound or divisor-hole-pushthrough.
- **Algorithm** — constant time.
- **Why it is true** — `rem_pos_hi` says `|y| ≥ x − S + 1`, and `x − S + 1 ≥
  x_lo − w_hi + 1`.
- **Proof technique** — `ia` and `proof by contradiction` (inside a JSP 7.2
  chain), `pol` (the remainder row, the grid-sum upper chain for whichever side
  set `w_hi`, and a cached bound on `x`) then `RUP`.
- **Reason** — the literals of the side that set `w_hi`, `x ≥ x_lo`, and `x`'s
  sign literal (or the mirrors).
- **Assertion** — `reason ⇒ [|y| ≥ k]`.
- **Hint** — `hints::Divide`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`.
- **Proof size** — as product-interval-empty.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: modulus-identity-bounds

- **Infers** — for `Modulus` with `x`'s sign decided, bounds both ways between
  `r` and `x` through `r = x − S` (`x ≥ 0`) or `r = x + S` (`x ≤ 0`): `r ≤ x_hi −
  w_lo`, `r ≥ x_lo − w_hi`, `x ≥ r_lo + w_lo`, `x ≤ r_hi + w_hi`, and the mirrors.
- **Fires when** — the `Divide` / `Modulus` propagator, for `Modulus`.
  **`Modulus`'s commonest rule on the corpus**: 314,413 times on `harmony`
  2024 and 8,758 on `rotating-workforce` 2019 over 20 s, all with `x ≥ 0`.
- **Strength** — `partial`.
- **Algorithm** — constant time.
- **Why it is true** — the gated identity rows, with `S` in its interval.
- **Proof technique** — `ia` and, for a JSP 7.2 side, `proof by
  contradiction` (inside the chain), then `pol` (an `id_*` row, a grid chain
  for the relevant side, and one cached operand bound) then `RUP`. The rows pair grid-lower with
  `id_*_ge` and grid-upper with `id_*_le`, so that `S` cancels.
- **Reason** — the chain side's literals, the other operand's bound, and `x`'s
  sign literal.
- **Assertion** — `reason ⇒` a bound on `r` or `x`.
- **Hint** — `hints::Modulus`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`.
- **Proof size** — as product-interval-empty.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: modulus-dividend-sign-refutation

- **Infers** — for `Modulus`, `x ≤ −1` when `S`'s interval misses `[x_lo − r_hi,
  x_hi − r_lo]`, and `x ≥ 1` when it misses the negative branch's, with `x`'s
  sign undecided.
- **Fires when** — as modulus-identity-bounds, with `x`'s sign open. Never on
  the corpus runs counted here.
- **Strength** — `partial`.
- **Algorithm** — constant time.
- **Why it is true** — under `x ≥ 0`, `S = x − r` must meet `S`'s interval;
  mirror under `x ≤ 0`.
- **Proof technique** — `ia` and `proof by contradiction` (inside the
  magnitude chain), `pol` (the chain, an `id_*` row and a cached bound on `r`)
  then `RUP`. The site of `f2605d52`'s fix: the rows must pair grid-lower with
  `id_*_ge` and grid-upper with `id_*_le`, and a transposed pairing passed
  about 99% of runs, because the final hint-free RUP closed without the
  wrong `pol`.
- **Reason** — the magnitude side's literals, one bound on `x` and one on `r`.
- **Assertion** — `reason ⇒ [x ≤ −1]` / `reason ⇒ [x ≥ 1]`.
- **Hint** — `hints::Modulus`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`.
- **Proof size** — as product-interval-empty.
- **Gaps** — `None.`
- **Tightness** — `Not shown.` The flake that found `f2605d52` was a 1%
  per-process CI failure, not a lane.

### Rule: magnitude-filter-upper

- **Infers** — `t ≤ hi` for a magnitude `t ∈ {|q|, |y|}`, with the other
  magnitude as its cofactor, by the same quotient filter as `Multiply`'s.
- **Fires when** — the `Divide` / `Modulus` propagator, when the filter's
  upper bound is below `t`'s. 63,595 times on `rotating-workforce` 2019 and
  108,801 on `harmony` 2024 over 20 s.
- **Strength** — `partial`: the filter is sound but not exact.
- **Algorithm** — constant time.
- **Why it is true** — `t ≥ hi + 1` would give `S ≥ (hi + 1)·o_lo > w_hi`.
- **Proof technique** — `ia`, `pol`, `proof by contradiction` and `RUP`:
  assume the excluded range with one `ia`, take the grid lower bound (JSP 7.1)
  against the cofactor's lower bound, add the chain for `w_hi` by `pol` with
  `saturate`, and conclude by `conclude_by_sign_cases`. With no sign
  dimensions it still emits its `red` and subproof, using the clash directly.
  When the cofactor's lower bound is 0, a RUP line `[o ≠ 0] ⇒ o ≥ 1`, the
  chain for `w_lo`, and a zero-refutation unit instead.
- **Reason** — the literals of the side that set `w_hi`, and `o ≥ o_lo`. With a
  zero cofactor endpoint, `o ≥ o_lo` is dropped and the literals of the side
  that set `w_lo` are added (`divide_modulus.cc:766-768`).
- **Assertion** — `reason ⇒ [t ≤ hi]`.
- **Hint** — `hints::Divide` / `hints::Modulus`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`: `t` is the assertion's value,
  and the cofactor's bound is in the reason.
- **Proof size** — JSP 7.1 on a miss, `2n_a + 1` lines, each up to `n_b + 1`
  terms; otherwise constant. Cached at `Top`, keyed by `(target, t, o_lo)`,
  except on the zero-endpoint path.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: magnitude-filter-lower

- **Infers** — `t ≥ lo` for a magnitude, the mirror of magnitude-filter-upper.
- **Fires when** — when the filter's lower bound exceeds both `t`'s and 0.
  60,081 times on `rotating-workforce` 2019 and 67,539 on `harmony` 2024 over
  20 s.
- **Strength** — `partial`.
- **Algorithm** — constant time.
- **Why it is true** — `t ≤ lo − 1` would give `S ≤ (lo − 1)·o_hi < w_lo`.
- **Proof technique** — as magnitude-filter-upper (`ia`, `pol`, `proof by
  contradiction` and `RUP`), with JSP 7.2, whose rows add their own
  subproofs, and the chain for `w_lo`.
- **Reason** — the literals of the side that set `w_lo`, and `o ≤ o_hi`.
- **Assertion** — `reason ⇒ [t ≥ lo]`.
- **Hint** — `hints::Divide` / `hints::Modulus`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`.
- **Proof size** — JSP 7.2 on a miss: about `3n_a + 1` lines, plus `3n_a`
  subproof lines. Always cached.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: magnitude-filter-empty

- **Infers** — a contradiction.
- **Fires when** — the cofactor magnitude is fixed at 0 but `w_lo > 0`. Never
  on the corpus runs counted here.
- **Strength** — `partial`.
- **Algorithm** — constant time.
- **Why it is true** — a zero cofactor makes `S = 0`.
- **Proof technique** — `ia` and `pol` (the JSP 7.1 chain for `w_lo`, and the
  cached `o ≤ 0` line), then `RUP`: the zero magnitude empties the grid by
  unit propagation.
- **Reason** — the literals of the side that set `w_lo`, and `o ≤ 0`.
- **Assertion** — `reason ⇒ ⊥`.
- **Hint** — `hints::Divide` / `hints::Modulus`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`.
- **Proof size** — as magnitude-filter-upper.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: divisor-hole-pushthrough

- **Infers** — `y ≤ −b_lo` when `|y| ≥ b_lo > y_hi`, and `y ≥ b_lo` when `b_lo`
  exceeds both `−y_lo` and `y_lo`.
- **Fires when** — the `Divide` / `Modulus` propagator, after the filters,
  reading `|y|`'s lower bound afresh. At `f28fdef8` it was **the only rule
  that moved a magnitude bound back onto a sign-open operand**, and it moves
  only `|y|`'s lower bound. Since #1081, [sign-open-clamp](#rule-sign-open-clamp)
  moves an upper bound, for `y` and for `Divide`'s `q`; nothing yet pushes
  `|q|`'s lower bound through the hole the way this rule does for `|y|`. The
  first branch's condition admits `y_hi = −b_lo`, a no-op inference. Never on
  the corpus runs counted here.
- **Strength** — `partial`.
- **Algorithm** — constant time.
- **Why it is true** — `|y| ≥ k` excludes `(−k, k)`.
- **Proof technique** — `ia`, `pol`, `proof by contradiction` and `RUP`: cached
  operand-bound lines (`ia`), two `pol`s against `Yge0_ge` and `Ylt0_le`, one
  a clash with `saturate`, then `conclude_by_sign_cases` over `[y ≥ 0]` /
  `[y < 0]`, then the closing RUP.
- **Reason** — `{|y| ≥ b_lo, y ≤ y_hi}` (or `y ≥ y_lo`).
- **Assertion** — `reason ⇒ [y ≤ −b_lo]` / `reason ⇒ [y ≥ b_lo]`.
- **Hint** — `hints::Divide` / `hints::Modulus`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`.
- **Proof size** — about seven lines.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: sign-open-clamp

- **Infers** — `v ≤ u` and `v ≥ −u` from `|v| ≤ u`, for `v` the divisor `y`
  (both classes) or `Divide`'s quotient `q`, when `v`'s sign is open. New in
  #1081.
- **Fires when** — the `Divide` / `Modulus` propagator, after
  divisor-hole-pushthrough, when `v`'s bound lies beyond `±u` and the
  matching sign is not decided: for the upper bound, `v_lo < 1` for the
  divisor and `v_lo < 0` for the quotient; for the lower bound, `v_hi ≥ 0`.
  A decided sign leaves the clamp to that sign's channel stage.
- **Strength** — `partial`.
- **Algorithm** — three reads: `v`'s two bounds and `|v|`'s upper bound.
- **Why it is true** — `|v| ≤ u` puts `v` in `[−u, u]` whatever its sign.
- **Proof technique** — `ia`, `pol`, `proof by contradiction` and `RUP`: a
  cached `|v| ≤ u` line (`ia`), one `pol` adding it to the channel row for the
  case that can violate the bound (`[v ≥ 0] ⇒ v ≤ |v|` for the upper bound,
  `[v < 0] ⇒ −v ≤ |v|` for the lower), at `Temporary`, then
  `conclude_by_sign_cases` over `[v ≥ 0]` / `[v < 0]`, the other case holding
  outright, and a hint-free closing RUP.
- **Reason** — `{|v| ≤ u}`. Minimal.
- **Assertion** — `[|v| ≤ u] ⇒ [v ≤ u]` / `⇒ [v ≥ −u]`. For `x ∈ [−20, 20]`,
  `y ∈ [3, 4]`, `q ∈ [−50, 50]`: `a 1 ~i[q][ge7] 1 i[aux_divide_qmag4][ge7] >=
  1`, which is `|q| ≤ 6 ⇒ q ≤ 6`.
- **Hint** — `hints::Divide` / `hints::Modulus`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`: the id locates the channel rows,
  and the reason is the one bound the derivation uses.
- **Proof size** — a constant number of lines, independent of width; not
  measured.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: sign-open-magnitude-cap

- **Infers** — `|v| ≤ max(−v_lo, v_hi)` for a sign-open `v`, the divisor or
  `Divide`'s quotient. New in #1081.
- **Fires when** — as sign-open-clamp, when `|v|`'s upper bound exceeds that
  cap and neither sign is decided: `v_hi ≥ 0`, and `v_lo < 1` for the divisor
  or `v_lo < 0` for the quotient.
- **Strength** — `partial`.
- **Algorithm** — constant time.
- **Why it is true** — a value in `[v_lo, v_hi]` has magnitude at most the
  larger of `−v_lo` and `v_hi`.
- **Proof technique** — `ia`, `pol`, `proof by contradiction` and `RUP`: two
  cached bound lines on `v` (`ia`), two `pol`s adding each to the channel row
  of its sign case, at `Temporary`, then `conclude_by_sign_cases` over `[v ≥
  0]` / `[v < 0]` and a hint-free closing RUP.
- **Reason** — `{v ≥ v_lo, v ≤ v_hi}`. Minimal.
- **Assertion** — `[v ≥ v_lo] ∧ [v ≤ v_hi] ⇒ [|v| ≤ cap]`. For `q ∈ [−5, 5]`:
  `a 1 ~i[aux_divide_qmag4][ge6] 1 ~i[q][ge-5] 1 i[q][ge6] >= 1`.
- **Hint** — `hints::Divide` / `hints::Modulus`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`, as sign-open-clamp.
- **Proof size** — a constant number of lines, independent of width; not
  measured.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: sign-open-magnitude-nonzero

- **Infers** — `|v| ≥ 1` when 0 is not in a sign-open `v`'s domain, for the
  divisor or `Divide`'s quotient. New in #1081.
- **Fires when** — the same pass, while `|v|`'s lower bound is still 0 and
  neither sign is decided, as for sign-open-magnitude-cap.
  **It reads an interior value**: whether 0 is in `v`'s domain. For the
  divisor, 0 is always gone by then, removed by
  [divisor-nonzero](#rule-divisor-nonzero) earlier in the same pass. For the
  quotient, a hole at 0 comes from another constraint, and does not wake this
  propagator; see [Interior values](#interior-values-and-optional-pruning).
- **Strength** — `partial`.
- **Algorithm** — one `in_domain` check.
- **Why it is true** — a non-zero integer has magnitude at least 1.
- **Proof technique** — `proof by contradiction` and `RUP`:
  `conclude_by_sign_cases` over `[v ≥ 0]` / `[v < 0]` with no premises, since
  in each case `[v ≠ 0]` and the channel row give `|v| ≥ 1` by unit
  propagation, then a hint-free closing RUP.
- **Reason** — `{v ≠ 0}`. Minimal.
- **Assertion** — `[v ≠ 0] ⇒ [|v| ≥ 1]`. For `q ∈ [−5, 5]` with `q ≠ 0` posted:
  `a 1 i[aux_divide_qmag4][ge1] 1 i[q][eq0] >= 1`.
- **Hint** — `hints::Divide` / `hints::Modulus`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`.
- **Proof size** — one sign-case subproof and one RUP; not measured.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: zero-divisor-contradiction

- **Infers** — a contradiction at the root.
- **Fires when** — `Divide` / `Modulus` with a divisor whose affine form is the
  constant 0. An initial contradiction, with a stats note (#722).
- **Strength** — `checker`.
- **Algorithm** — a test on `affine_of(y)`.
- **Why it is true** — no tuple has `y = 0`.
- **Proof technique** — `RUP` against the `≥ 1` row over nothing.
- **Reason** — none.
- **Assertion** — the empty clause.
- **Hint** — `hints::Divide` / `hints::Modulus`: `originator` (`ConstraintID`).
- **Offline reconstructibility** — `offline`.
- **Proof size** — one line.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: tabulate-relation

- **Infers** — nothing directly: it builds the table the extensional
  propagator runs over, and writes its derivation into the proof.
- **Fires when** — the tabulation initialiser, once, at
  `InitialiserPriority::Expensive`, under `Tabulated` or a tabulating `Auto`,
  for any class.
- **Strength** — with table-prune, `GAC` over the distinct underlying
  variables, **aliasing included**. For `Power`, the scope is the base and the
  result; the chain's auxiliaries are not in the table.
- **Algorithm** — enumerate the distinct underlying variables, smallest domain
  first, with the largest determined variable's level replaced by one
  `value()` call; keep the tuples the relation accepts, using
  overflow-checked arithmetic. **Per value, by design**: at most 100 leaves
  under `Auto`, unbounded under `Tabulated` (#880).
- **Why it is true** — the table is the relation restricted to the domains at
  the time the initialiser runs.
- **Proof technique** — `redundance` and `RUP`: two `red` lines per accepted
  tuple defining a selector value, and one backtrack RUP per node of the
  enumeration tree. That RUP is valid because every rejected complete
  assignment unit-propagates to a conflict against the structural encoding,
  and a determined variable's level can be skipped because unit propagation
  pins it (`tabulation.hh:45-67, 115-128`). For `Power`, that propagation runs
  through the whole chain of grids. Ours.
- **Reason** — none: it runs at the root.
- **Assertion** — none: the lines are a derivation, not an assertion.
  **Skipped entirely at the assertion levels.**
- **Hint** — none on these lines.
- **Offline reconstructibility** — `hinted`: a hints-only proof holds only
  table-prune's `a` lines, and a reconstructor rebuilds the table from the
  relation, which the hint's `originator` identifies, over the root domains.
  The solver's enumeration order and selector numbering are not recorded, and
  a rebuild does not need them.
- **Proof size** — one line per enumeration node and two per accepted tuple,
  at the root: bounded by the budget under `Auto`.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: tabulate-empty

- **Infers** — a contradiction at the root.
- **Fires when** — the tabulation initialiser accepts no tuple.
- **Strength** — `checker`.
- **Algorithm** — as tabulate-relation.
- **Why it is true** — the relation has no tuple over the current domains.
- **Proof technique** — `RUP`, after tabulate-relation's backtrack lines.
- **Reason** — empty.
- **Assertion** — the empty clause.
- **Hint** — the class's own hint (`hints::Plus`, `hints::Multiply`, …),
  `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`, as tabulate-relation.
- **Proof size** — one line, after the enumeration's.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

### Rule: table-prune

- **Infers** — value removals and root bound trims on the enumerated
  variables, and a contradiction when no tuple is live.
- **Fires when** — the extensional propagator, on any change to an enumerated
  variable.
- **Strength** — `GAC` over the enumerated variables.
- **Algorithm** — the table family's `propagate_extensional`, over the derived
  table. Not re-audited here.
- **Why it is true** — a value with no live tuple has no support.
- **Proof technique** — the table family's: `RUP` against the derivation's
  selector lines.
- **Reason** — the table family's.
- **Assertion** — the table family's: a removed value or bound under that
  reason.
- **Hint** — the class's own hint: `hints::Plus`, `hints::Minus`,
  `hints::Multiply`, `hints::Power`, `hints::Divide` or `hints::Modulus`,
  `originator` (`ConstraintID`).
- **Offline reconstructibility** — `hinted`, as tabulate-relation.
- **Proof size** — the table family's: one RUP per inference.
- **Gaps** — `None.`
- **Tightness** — `Not shown.`

## Evidence

### Tests

| Lane | What it covers |
|---|---|
| `plus_minus_constraint` (`plus_minus_test`), `…_view_mixed` | hand rows and 10 seeded random rows under `Auto`, **solutions only**; the same plus holey and random holey rows under `GAC` and `Dynamic`, **GAC checked at every node** (`solve_for_tests_checking_consistency`); two rows per tag, GAC-checked except under `BC`. The bare lane only: aliased rows under `Auto` and `GAC`, solutions only, and a directed fallback case |
| `plus_minus_constraint_dynamic_fallback` | the same binary with `GCS_INTERVAL_PAIRS_THRESHOLD=0`, so every step falls back |
| `plus_mutation_control`, `plus_mutation_{lemmas,hole_lemmas,window_holes}` | the interval propagator's derivation; see [sum-interval-prune](#rule-sum-interval-prune) |
| `multiply_constraint` (`multiply_test`), `…_view_mixed` | `Auto`, `BC` and `Tabulated` over small boxes, views, negatives and zero; six aliasing shapes; constant operands and a constant result; wide `Auto` rows; eight random forced-`BC` boxes, four with random view wraps; one forced `Tabulated` box. GAC checked at every node except under `BC`, on the wide rows, on the constant-operand rows and on `x · x = x`, which use plain `solve_for_tests` under every tag |
| `power_constraint` (`power_test`), `…_view_mixed` | a variable exponent, including negative exponents; `k ∈ {0, 1, 2, 3, −2, 100, −3}` under each tag; views at `k = 2, 3`; `x^2 = x`; pinned `9^19`, `10^20`, `0^0` and `0^−2` |
| `divide_modulus_constraint` (`divide_modulus_test`), `…_view_mixed` | both classes over signs and aliasing shapes (`x op x = y`, `x op y = x`, `y op x = x`), seeded random rows, and constant-slot, zero-divisor and two-constant rows; GAC checked where tabulation promises it, solutions only on the bounds propagator. **Since #1081**, for both classes under `BC`: seven root-hull fixtures over sign-open or weakly signed operands (eight for `Divide`), each checking that the root bounds are exactly the relation's hull; and four fixtures with a weakly signed dividend and a constant divisor, checking the result's bounds (the harness's `BC`, which is `bounds(Z)`) at every node |
| `product_bounds` | every `product_bounds.hh` function, exhaustively over small ranges, with the quotient filter's known inexactness pinned; since #1079, the saturating corners too |
| `wide_product` (since #1079) | #1064's shapes for all four product classes, without proofs, each solution checked against a direct listing |
| `product_justify` | 20 justification-fragment runs over 16 small boxes, each helper's claimed bound restated as a checked `ia` (except the trivial-RUP fragment): the harness for testing one helper at a time |
| `tabulation_test` | the in-proof table derivation, over `Multiply`'s encoding, with seeded random rows: the only direct test of the tabulation machinery |
| `scp_chain_*` | 4 `plus` / `minus` cases in `strict` mode; 7 `multiply`, 11 `divide` and 12 `modulus` cases in `none` mode |
| `minizinc-times`, `minizinc-div` | one MiniZinc model each |
| `xcsp_intension_arithmetic` | the XCSP3 intension walker's arithmetic |
| `multiply_random` | the example, as a lane |

- **VeriPB runs inside the constraint tests** whenever it is on the `PATH`.
- **Seeded.** All four constraint test binaries, `product_justify_test` and
  `tabulation_test` call `establish_and_announce_seed`. The random rows in
  `plus_minus_test`, `multiply_test`, `divide_modulus_test` and
  `tabulation_test` consume the seed.
- **Caps.** No lane sets or clears a cap, so the suite-wide defaults apply.
  **They fire**: with the default caps (300 solutions, 1,500 nodes) in the
  environment and a local print in the harness, three unseeded runs of each
  binary truncated 8 solves per run in `multiply_test` and in
  `divide_modulus_test`, 1 in `plus_minus_test`, and none in `power_test`. A
  truncated solve checks soundness and a partial proof only. With the caps
  off (`-DGCS_TEST_CAP_DEFAULTS=OFF`), all 54 of this family's lanes in the
  table above pass, in a run on 2026-09-24 at `f28fdef8` with VeriPB on the
  `PATH`. `multiply_constraint` takes 362 s, run 24 lanes at a time.
- **Tightness.** Only `Plus`'s interval propagator has mutation lanes, with a
  control. The fixture and why it took work are under
  [sum-interval-prune](#rule-sum-interval-prune).
- **Idempotence claims** were checked by this audit at `f28fdef8`, and since
  #1086 by every harness solve in the suite; see the [Propagator
  inventory](#propagator-inventory).

**What the tests do not cover:**

- **Per-node strength of the product group's bounds propagators**, except
  on `Divide` / `Modulus`'s four weakly-signed, constant-divisor fixtures
  (#1081). `multiply_test` claims none under `BC`, which is as well: its `z`
  is only `bounds(R)` (see [product-bounds](#rule-product-bounds)). At
  `f28fdef8` this is how `Divide`'s sign-open weakness (#1065) went unseen.
- **Operand widths that overflow with proofs on.** `wide_product` and the
  audit lane's `wide-product` rows run without proofs; nothing tests that
  solving past the proof limit fails cleanly. (At `f28fdef8` nothing passed
  30 bits per operand at all; #1079 added both.)
- **The assertion levels.** No arithmetic lane runs above `AssertionLevel::Off`,
  which is why `Modulus`'s solution-step failure (#1067) went unseen.
- **`Multiply`'s bounds proofs in the verified chain**: every `multiply` chain
  case tabulates (see [Cake conformity](#cake-conformity)).
- **Shapes:** `Multiply{c1, c2, r}`; `Power` with `4 ≤ k ≤ 62` over a
  non-singleton base, at `k = 62` and `63`, and `x^k = x` beyond `k = 2`;
  `Dynamic` under aliasing, since the aliased `Auto` rows always tabulate at
  their sizes; the `Plus` bounds propagator's hole-snap loop; any constant,
  all-constant, zero-divisor or aliased `Divide` / `Modulus` chain case.
- **Front ends:** no MiniZinc `int_mod` lane, no XCSP3 `div` or `mod` lane,
  and one fixed-value Python test for each class except `Minus`, which has
  none.
- **`GCS_TABULATION_THRESHOLD`**: no test sets it. (`verbose_names = false`,
  listed here at the first pass, no longer exists: #1087.)
- **No real instance** has been ported into a data-driven test.

### Benchmarks and examples

**In the repository.** `langford` (`--plus`, tabulated by default);
`ortho_latin` (`Divide` by a constant, non-negative); `shikaku`,
`skeleton_puzzle`, `n_fractions`, `multiply_random` and `random_polynomial`
(`Multiply`). `proof-benchmarks.md`'s proof-writing group has `polynomial10`
and `nfractions` (see its own dates).

**The MiniZinc corpus** (297 models, one data file each, flattened
2026-09-05):
- **`Multiply`**: 115,972 `int_times` posts in 37 models, 56,889 of them in
  `nside` 2019 with a constant operand, so linear. `linear.md`'s share survey at
  `00797a97` (10 s each; none of this family's files changed between it and
  `f28fdef8`) saw it in 33 models, at a median of 6.0% of propagation time. The
  top shares are `ship-schedule` 2014 39.1%, `stable-goods` 2020 38.5%,
  `ship-schedule` 2012 and 2011 37%, `train` 2014 32.5% and `opd` 2017 30.6%.
  Squares are posted only by `gbac` and `routing-flexible`.
- **`Divide`**: 350 posts in 8 models, at most 8.9% of propagation
  (`rotating-workforce` 2019).
- **`Modulus`**: 420 posts in 3 models, at most 5.4% (`harmony` 2024).
- **Nothing else**: no model posts `int_plus` or `int_pow`. Every `int_div`
  and `int_mod` post has non-negative domains in every argument, so the
  corpus never reaches a negative operand of either.

**Rule counts.** Counts from local counters on eight runs, at `f28fdef8`:
`ship-schedule` 2014 to optimality; `train`
2014, `stable-goods` 2020, `rotating-workforce` 2019 and `harmony` 2024 for
20 s each; `opd` 2017 to its 17th solution; and, for squares, `gbac` 2016
and `routing-flexible` 2017 for 20 s. They fired product-bounds,
factor-bound and the square rules for `Multiply`, and for `Divide` /
`Modulus` only dividend-from-product, dividend-magnitude-cap,
product-interval-empty, the two magnitude filters and the positive branch
of modulus-identity-bounds. **Never fired** on those runs:
- zero-cofactor-contradiction;
- quotient-sign, dividend-sign-refutation and divisor-magnitude-floor;
- the negative branch of modulus-identity-bounds, and
  modulus-dividend-sign-refutation;
- divisor-nonzero, magnitude-filter-empty and divisor-hole-pushthrough.

The four rules #1081 added, [divisor-sign](#rule-divisor-sign) and the three
sign-open rules, did not exist at `f28fdef8` and have not been counted. Since
every corpus `int_div` and `int_mod` post is non-negative in every argument,
and they fire only on a sign-open operand, they are unlikely to fire there.

The stage rules were not counted.

**Recommendations.**
- **CPU, against Gecode:** `train` 2014 `instance.14` to its third
  solution, where the node counts agree to within 0.3%. But `Multiply` is only 5.8%
  of its propagation, so for `Multiply`'s own cost read the per-call figures
  instead. For the engine's cost at scale: `stable-goods` 2020 and `opd` 2017.
- **Proof verification:**
  - `ship-schedule` 2014 `3Ships`, solved to optimality: a 153 MB proof that
    verifies in about a minute.
  - `harmony` 2024 to its first solution, for `Modulus`: 33 MB.
  - Never uncapped: `train` 2014, whose `instance.14` writes 3.65 GB in
    38,092 nodes.

### CPU performance

**The matched tree.** `train` 2014 `instance.14`, to its third solution.
At `f28fdef8`, Release, on fataepyc-09 (EPYC 7643, boost off), 2026-09-24,
pinned to one core with `numactl --cpunodebind=0 --membind=0 taskset -c 8
setarch -R`, on an unmodified build. Three runs each, identical counts:

| | nodes | propagations | time |
|---|---|---|---|
| GCS (`fzn-glasgow -i -s -n 3`) | 38,092 | 5,262,919 | 1.54 s |
| Gecode 6.3.0 (`fzn-gecode -a -s -n 3`, its own flattening) | 38,078 | 5,251,282 | 0.44 s |

The same three solutions, and node and propagation counts within 0.3%. We
are 3.5 times slower. But `Multiply` is 5.8% of our propagation time here
(148,054 calls at 0.40 µs); `LinEquals`, `LessEqual` and `LinLessEqual` are
83%. So this is not a measurement of `Multiply`.

**Four `Multiply`-heavy models**, same set-up, one run each unless stated;
the GCS 60 s runs had `GCS_PROPAGATOR_STATS=time` on. The trees differ, so
the time column is not a per-node comparison. Three of
the four **tabulate** every or most `int_times` under `Auto`, which is GAC
against Gecode's bounds propagation:

| model | GCS nodes, propagations | GCS time | Gecode nodes, propagations | Gecode time | `Multiply` share of GCS propagation, per call |
|---|---|---|---|---|---|
| `ship-schedule` 2014 `3Ships`, to optimality | 4,433, 521,041 | 0.36 s | 5,856, 3,552,943 | 0.32 s | 39.4%, 0.28 µs |
| `train` 2014 `instance.1`, 60 s | 9,736,246, 129,030,256 | — | 45,515,249, 421,096,567 | — | 32.3%, 0.41 µs |
| `stable-goods` 2020 `s-d16`, 60 s, no solution either way | 33,108, 25,368,983 | — | 257,773, 67,956,473 | — | 37.6%, 0.54 µs |
| `opd` 2017 `flener_et_al_15_350_100`, to the 17th solution, 3 runs | 43,375, 2,720,224 | 60.1–61.7 s | 22,456, 1,252,279 | 3.19 s | 32.3%, 0.67 µs (from the 60 s stats run) |

**Where the time goes on the big models is not arithmetic.** Propagation, of
every kind, is 4.9 s of `opd`'s 59.6 s and 9.2 s of `stable-goods`' 59.6 s
(`GCS_PROPAGATOR_STATS=time`). On `stable-goods`, 34.4 s of the 60 is kernel
time. `State::new_epoch` copies all 30,231 domains at every node, and glibc
returns each copy to the kernel on backtrack, so the next node faults it in
again: 386 minor faults per node. Raising glibc's mmap and trim thresholds
together, with no code change, gives 3.4 times the nodes in 20 s (three runs
each way). Filed as #1063, with the profile. `opd` improves less, from
60.1–61.7 s to 54.8 s, because per-epoch copies of constraint state cost it
user time too.

**What these benchmarks exercise**: product-bounds and factor-bound, and on
`ship-schedule`, `opd` and `stable-goods` the tabulation rules. None reaches a
square, a negative operand, `Power`, `Plus` or `Minus`; see the rule counts
above.

**Measured elsewhere**, not to be put in a table with the above: #192's
`Plus` / `Minus` interval propagator went from 3.4 s to 0.1 s at the root on
3,000 intervals per operand under `Dynamic` (`ef717662`'s message;
`large-domains.md` says 3.2 s).

### Proof performance

At `f28fdef8`, same machine and date, on an unmodified build; VeriPB 3.0.2
with `--force-checked-deletion`, on one core each:

| instance | level | `.pbp` | verification |
|---|---|---|---|
| `ship-schedule` 2014 `3Ships`, to optimality (4,433 nodes; OPB 24,166 lines) | `Off` | 938,291 lines, 153 MB | 62.9 s, `VERIFIED`, optimum proved |
| | `Inferences` | 256,420 lines, 65 MB | 2.9 s, `UNDER ASSERTIONS` |
| `train` 2014 `instance.14`, to its third solution (38,092 nodes; OPB 2,416 lines) | `Off` | 19,780,475 lines, 3.65 GB | **not finished in 2 hours**; stopped |
| | `Inferences` | 2,762,927 lines, 883 MB | 17.7 s, `UNDER ASSERTIONS` |
| `harmony` 2024 `brother`, to its first solution (279 nodes) | `Off` | 366,193 lines, 33 MB | 34.4 s, `VERIFIED` |
| | `Inferences` | 17,649 lines, 3.1 MB | **rejected at its `soli`** (#1067) |

Solving with proofs took 2.1 s (`ship-schedule`) and 37.0 s (`train`) at
`Off`, against 0.36 s and 1.54 s without (wall time throughout; the proof runs
were not pinned).

**`Multiply`'s own share, measured.** A local switch made `Multiply`'s
inferences assertions (`AssertRatherThanJustifying`) instead of derivations,
everything else unchanged. The difference is `Multiply`'s derivations:

| instance | `Off` | `Multiply` asserted | `Multiply`'s derivations | per `Multiply` inference | verification, asserted |
|---|---|---|---|---|---|
| `ship-schedule` 2014 | 938,291 lines, 153 MB | 492,364 lines, 66 MB | 48% of lines, 57% of bytes | 29 lines | 59.0 s, against 62.9 s |
| `train` 2014 `instance.14` | 19,780,475 lines, 3.65 GB | 8,986,816 lines, 1.06 GB | 55% of lines, 71% of bytes | 72 lines, 17 KB | not finished in 2 hours either |

So on `train` the fully justified proof of a 1.5 s search is too large to check
in two hours, and removing `Multiply`'s derivations, 71% of its bytes, does not
bring it within that. The `Inferences` proof of the same search checks in
17.7 s.

(Bytes by `stat`, in units of 10^6; lines by `wc -l`. The per-inference figure
adds back the `a` line each asserted inference writes.) On `ship-schedule`,
`Multiply`'s derivations are half the proof's lines and about 6% of its
checking time: most of them are `pol`s and hinted RUPs, which are cheap to
check. The other half, the other constraints' derivations and the shared
layers', was not split further.

**Assertions at `Inferences`**, by wire form:

| instance | this family's | all | largest others |
|---|---|---|---|
| `ship-schedule` 2014 | `multiply` 16,072 (6.5%) | 247,451 | `equals` 96,723, `or` 34,832, `and` 34,594 |
| `train` 2014 `instance.14` | `multiply` 151,581 (5.7%) | 2,648,646 | `linear_equality` 1,287,318, `comparison` 443,358; and 428,023 with no hint, all from `LinearLessEqualIff` (the linear family's) |
| `harmony` 2024 | `modulus` 2,302 (14.7%) | 15,608 | `linear_equality` 4,847, `equals` 3,430, `abs` 1,617 |

**Per firing, and against width.** The inventory agent measured `Multiply`'s
derivations on root-only probes at this commit, one firing each; its probe
source is kept (`multiply-power-probe.cc`), but its raw outputs were not, so
these figures are its report, not re-measured here. Product
bounds cost about `11n + 63` lines with one live sign pattern and `36n + 76`
with four, where `n` is the bit width of the grid's row operand. A factor
bound costs about `11n + 51`. The W-lines are a one-off `2nm` per grid. All
are in **bits**, so a 10⁹-wide operand costs 30 bits, not 10⁹ values.
`Divide` / `Modulus`'s per-firing costs were not measured, and neither was
their own share against the shared layers.

**Measured elsewhere**: `proof-benchmarks.md` has `polynomial10` (426 MB)
and `nfractions` (146 MB), at its own dates. They should not be mixed with the
tables above.

## Status, gaps, and next steps

### Proof-logging gaps

**Every inference is justified at `AssertionLevel::Off`**, and nothing is
asserted there. Three gaps sit around that:

- **`Modulus`'s solution steps depend on what came before them** (#1067).
  (At `Definitions` every chain case verifies. At `Links` most SAT cases of
  every family fail at a solution step, because an asserted link with no
  definitions leaves an atom untied to its bits; that looks like the "not a
  self-contained proof" caveat of `solution-clause-deletion.md`, not this
  family's.)
  Its quotient magnitude is not determined by unit propagation from a
  solution's logged variables. At `Off` the proof's own inference lines and
  atom definitions happen to pin it, and every proof tried verifies. At
  `Inferences` and `Backtracking`, 3 of the 12 `modulus` chain cases and
  `harmony` 2024 are rejected at a `solx` / `soli`. At `Inferences`, those
  three are the only failures among all 104 SAT chain cases in the
  repository, of every family (at `f28fdef8`; the three `modulus` failures,
  and the `divide` and `multiply` cases passing, re-checked at `61112ed0`).
  **Why unit propagation stalls** is the grid's shape: see [Proof-time
  state](#proof-time-state). And a reconstructor does not have to reproduce
  whatever happened to pin `|q|` in the `Off` proof: any sufficient
  derivation, definition or auxiliary witness that fixes `|q|` before the
  solution step will do (Appendix C's baseline context).
- **Proofs narrow the operand range the product group can take.** Without
  proofs, since #1079, propagation works at any width. With proofs, building
  the proof model fails past 62 bits of combined operand magnitude for
  `Multiply` (and each `Power` link), 63 of dividend and divisor for
  `Modulus`, and for `Divide` 63 of quotient and divisor only while the
  dividend is narrow (about 62 in practice), because the rows' largest sums
  must fit in an `Integer`; see [Robustness and limits](#robustness-and-limits). The
  strength of the propagation never changes with proofs.
- **Hints name the wrong class** for `Power`'s links (`hints::Multiply`) and
  for every stage (`hints::LinearEquality`); see the [catalogue's
  preamble](#inference-catalogue). That is a gap for an external justifier,
  not for the proof, and is deliberately unfiled, as for other families:
  the justifier work will show what it needs.

### Known limitations

- **With proofs on, very wide operands cannot be solved**: past 62 bits of
  combined operand magnitude for `Multiply`, 63 of dividend and divisor for
  `Modulus`, and about 62 for `Divide`, whose dividend counts as well as its
  quotient and divisor. `solve_with` throws when it builds the proof model: a
  `ProofError`, or an `UnimplementedException` from `power2` once the grid
  would need more than about 64 bits. Without proofs, the corner products
  saturate (#1079; #1064 is fixed).
- **`Power(x, 63, INT64_MIN)` with a constant result throws
  `IntegerOverflow`**, the one representable power the constant-exponent path
  misses; now documented in `power.hh`.
- **`Divide` stops short of the hull** on an operand whose sign is fully
  open, which needs a case split, and on a variable divisor's own bounds; see
  [quotient-sign](#rule-quotient-sign). The weakly signed dividend of #1065
  is fixed (#1081).
- **`Divide`'s quotient under-reports its holes**: a hole at 0 made by another
  constraint does not wake it, and its derived **Holes affect** omits `q`
  (see [Interior values](#interior-values-and-optional-pruning)); #1102.
- **An aliased `Plus` or `Minus` can take time linear in a domain's width**:
  `Plus{x, y, x}` with `y ≥ 1` takes 2.8 s to fail at the root with `x` over
  `[0, 10^7]`, under every tag (#1068).
- **`Modulus` proofs written in the hints-only modes fail VeriPB's solution
  check** on some instances (#1067).
- **An explicit `consistency::Tabulated` on wide domains runs out of memory**
  rather than refusing (#880), and so does a variable-exponent `Power`, which
  tabulates whatever was asked for, by default (#845).
- **`Multiply`'s proofs are large**: about 30 to 70 lines per inference, and
  55% of the proof's lines on `train` 2014, where a 1.5 s search writes
  3.65 GB.
- **`Auto` decides from the declared domains**, before root propagation, and
  does not say what it decided (#724).
- **`x · −x` and `(x + 1)·(x − 1)` are not squares**: they get box reasoning
  over two independent intervals.
- **A view shape cannot be chain-verified**, because cake's `.scp` grammar has
  no view terms.

### Next steps

Ranked by what they buy for what they cost.

1. **#1067: log `Modulus`'s quotient magnitude in the solution.** Small. It
   makes the hints-only proofs valid, and removes the dependence of the
   `Off` proof's solution steps on earlier lines. Check that an extra,
   non-preserved variable in `solx` is sound for projected enumeration.
2. **#1068: collapse aliased `Plus` / `Minus` to their net form.** Small:
   `prepare()` already computes the net coefficients, and `x + y = x` is `y =
   0`. It removes the one width-proportional path on a default arm that is
   not `PowerTable`'s (#845).
3. **#1063 (the engine's, not this family's):** the largest CPU lever on the
   largest `Multiply` models, 3.4 times the nodes on `stable-goods` from the
   allocator alone.
4. **Shrink `Multiply`'s derivations.** First measure factor-bound's
   unused direction: each firing derives both grid bounds and both result
   channellings and uses one, and the same waste was worth removing from
   product-bounds (`0eaeaa48`). Unfiled until measured. #540 covers the case
   of a factor fixed during search.
5. **Declare `Divide`'s quotient in `holes_affect_propagation`**, or wake on
   `q`'s interior, since [sign-open-magnitude-nonzero](#rule-sign-open-magnitude-nonzero)
   reads whether 0 is in `q`'s domain. Tiny, and it only restores what another
   family's `consistency::Auto` may lose; #1102.
6. **Tests that would have caught this audit's findings.** Run the
   arithmetic chain cases at `Inferences` (#1067). Add a `BC`-forced
   `multiply` chain case, so the bounds proofs are chain-verified at all. Add
   an `int_mod` MiniZinc lane, and large-domain rows for a square, a view, an
   aliased post and a signed domain.
7. **#1066: the tidying**, including the draft thesis numbering in code
   comments and the `none` chain modes' stale reason. Add to it the headers'
   account of the proof limit (`multiply.hh`, `divide_modulus.hh`): they say
   posting throws a `ProofError`, where the throw comes from `solve_with` as
   the proof model is built, is an `UnimplementedException` from `power2` once
   the grid needs more than about 64 bits, and, for `Divide`, depends on the
   dividend's width too.

Done since the first pass: **#1064** (saturate the corner products; #1079,
which also added the large-domain rows the first pass asked for, including the
constant-exponent `Power`) and **#1065** (the ungated magnitude clamp and the
weak-sign quotient gate, by sign-case resolution as the first pass proposed,
with a per-node bounds check on weakly signed fixtures; #1081).

## Prior art

- **Bounds propagation for integer multiplication** is standard. McIlree's
  thesis takes its complete case analysis from Schulte and Stuckey (PPDP 2001)
  and from Apt and Zoeteweij (2004, *A Comparative Study of Arithmetic
  Constraints on Integer Intervals*).
- **The quotient filter** is JaCoP's `IntDomain` case breakdown.
- **The interval propagator for `Plus` / `Minus`**, GAC over Minkowski sums of
  interval lists with a hull fallback past a threshold, is ours (#192).
- **Certification.** McIlree's thesis, Chapter 7, gave the first VeriPB
  justifications for multiplication, over a two's-complement bit-product
  encoding. What is ours:
  - the move to cake_pb_cp's sign-magnitude encoding, so the model is
    chain-verified;
  - `conclude_by_sign_cases`, with complementary sign atoms in place of
    separate zero cases;
  - the RUP hint kits, and the line caches for `Divide` / `Modulus`;
  - the in-proof tabulation, which keeps every table out of the OPB;
  - `Divide`, `Modulus` and `Power` as grid-based encodings.

## Further reading

- [`arithmetic-proofs.md`](../arithmetic-proofs.md): the product group's
  design note. The encoding as cake fixes it, the justification layer helper
  by helper, the RUP hint rules and the regression that taught them, the
  `Divide` / `Modulus` line caches and why they split between `Top` and
  `Current`, and a list of hard-won rules. Read it before changing
  `product_justify`.
- [`large-domains.md`](../large-domains.md): the `Plus` / `Minus` interval
  propagator's lemma scheme and the `Dynamic` threshold's rationale, and the
  proof-size survey's arithmetic rows.
- McIlree's thesis, *Pseudo-Boolean Proof Logging for Constraint Propagation
  Algorithms*, Chapter 7: Justification Subprocedures 7.1–7.4 and Procedures
  7.6–7.8, which the product group follows. The code's comments use the
  draft's numbers (#1066).
