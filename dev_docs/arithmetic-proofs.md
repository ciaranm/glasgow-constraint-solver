# Arithmetic constraints: propagation and proofs

How Multiply, Divide, Modulus and Power propagate and justify their
inferences. The encoding is cake_pb_cp's, fixed by the verified encoding
chain (`verified_encodings/`); the proofs follow Chapter 7 of Matthew
McIlree's thesis, adapted to cake's sign-magnitude scheme. There is no
in-proof reformulation anywhere: every justification cites the OPB rows
and combines them with `pol`, `ia` and `rup` steps, hinted wherever the
conflict path is locally known.

## The encoding (fixed by cake)

For `x * y = z`, `gcs/constraints/innards/product_encoding.{hh,cc}` emits,
in this order and byte-compatibly with cake_pb_cp:

- a **magnitude channel** per operand slot: a non-negative magnitude
  bit-vector (a proof-only variable for Multiply/Power, a state variable
  with registered bits for Divide/Modulus), pinned to `|v|` by four
  half-reified rows gated on the reified sign atom: `[v>=0] => mag = v`,
  `[v<0] => mag = -v`. Slot-keyed: a repeated operand gets one channel per
  slot, exactly as cake emits for `(multiply X X Z)` — never key anything
  by variable id;
- the **bit-product grid**: fully-reified flags `prod_ij <=> a_i AND b_j`
  with deterministic `[r]`/`[f]` labels, summed with weight `2^(i+j)`;
- the **result channel** (`mag_Z*` rows) pinning `|z|` to the grid sum,
  gated on z's sign atom;
- six **sign clauses** over the reified atoms.

Divide and Modulus reuse the channel and grid emitters but replace the
result channel with cake's remainder rows (divide: `0 <= x - Sum < |y|`
split on sign(x); no remainder variable exists at all) or identity/range/
sign rows (modulus: `r = x -/+ Sum` split on sign(x)). The product
`w = |q| * |y|` exists nowhere: the propagator computes its interval
locally each call, remembering which side (magnitude corners, a gated row
via x and r, or the two gated rows' disjunction when x's sign is
undecided) established each bound, and the justifications rebuild exactly
that chain.

Power is a chain of multiply links sharing one constraint id,
disambiguated by `LinkNaming`; the first link is a native square. cake
has no power encoder, so Power self-verifies rather than chain-verifying.

## The justification layer

`gcs/constraints/innards/product_justify.{hh,cc}`, in the style of
`abs/justify.cc`: free functions passing `ConditionalBound`s — a derived
sign-case-conditional bound as its raw pol line plus its case literals.

- `derive_operand_bound` / `derive_assumed_operand_bound`: a bound line in
  V-form (view terms cancel against the V-form channel rows; never
  `_then_deview`), under the reason or under an assumed excluded-range
  atom that the driver's negated goal later supplies as a unit. Both are
  single-antecedent `ia` restatements of the bound atom's defining row,
  and the restatement is load-bearing: it renormalises the definition's
  gate coefficient to reify's choice, which the syntactic `ia` row
  implications in the grid procedures depend on. Citing the definition
  directly instead verifies or not depending on the instance's
  coefficient values — it survived a full local battery and a
  300-instance sweep, then failed power and multiply with "not
  syntactically implied" on three of five CI lanes;
- `channel_bound_to_magnitude` (thesis 7.3, cake flavour): one pol add
  against the matching channel row; directions flip on the negative
  branch; `strengthen_nonzero` lifts a useless non-positive magnitude
  lower bound to one under `[v != 0]` for spanning co-factors;
- `grid_sum_lower_bound` (thesis 7.1): pure cutting planes, O(n·m);
- `grid_sum_upper_bound` (thesis 7.2): per-row contradiction subproofs,
  with the per-cell W-lines cached in the grid; a zero magnitude takes a
  direct-RUP path (the grid empties by unit propagation);
- `channel_grid_bound_to_result` (thesis 7.4, cake flavour): pol against
  the matching mag_Z row, then one hinted RUP of the bound claim (the
  caller's kit plus the combined line and the reason/case literals'
  defs and bridges — but never definitions for the claimed bound
  itself; see the hints section). There is deliberately no standalone
  sign-atom discharge: a mixed sign case does not entail the result's
  sign when the non-negative operand may be zero; the claim's own
  negation pins the sign atom instead, or unit propagation closes
  through the sign clauses and the eq0 rows;
- `conclude_by_sign_cases`: the fixed-shape replacement for case
  resolution. One red-with-empty-witness derivation of
  `reason => conclusion`; the subproof takes each case pattern's premise
  pol-added onto the negated goal (premises that are already refutation
  clauses — factor-bound clashes — are used directly: adding the negation
  would inject its terms as free slack), closes dead cases with a RUP
  clause of the opposite atoms, emits any zero-refutation units
  (`[v=0]` empties the grid against the reason's result bounds), and runs
  the nested saturating cut one dimension at a time. Because `[v>=0]` and
  `[v<0]` are complementary atoms — unlike the thesis's two's-complement
  sign bits — no separate zero cases are needed, and a square's mixed
  patterns die as tautology clauses. The subproof's RUP steps (dead
  patterns and the closing contradiction) are hinted when the caller
  passes `SubproofRUPHints::Assemble`, which is sound exactly when the
  premises' sum terms cancel against the negated goal — product bounds
  arrange this, so multiply/squares/Power engage it; divide/modulus
  premises drag view bits and aux-atom rows into the cut result, where
  only a database-wide RUP reaches the closing conflict, so they stay
  on the default hint-free path.

Inference drivers: product bounds are thesis Procedure 7.5 (per live sign
case: channel, 7.1/7.2, channel to the result, conclude); factor and
square bounds are Procedures 7.6/7.7 — never enumerate propagator logic,
just refute the excluded range, with the far side of that range being the
target's *current* bound carried by the reason. The square's inner
square-root lift is sequenced after the outer clamp so each refuted
branch is uniformly too small or too big, which is exactly when the
box-shaped case refutations apply.

## RUP hints

VeriPB's cost model drives everything here: a hinted RUP step costs
O(hints), a hint-free one costs O(live database). Hints restrict unit
propagation to exactly the cited lines, so a hint set must cover the
*whole* conflict path or verification fails outright — half-hinting
breaks, and `RUPProofRule{}` with an engaged-but-empty vector renders
`: ;` ("restrict to nothing"), which always fails.

- Operand bounds are single-antecedent `ia` steps citing the bound
  atom's defining row (`derive_operand_bound`), falling back to RUP for
  constants, XLiteral domain boundaries and empty reasons; the
  restatement is load-bearing (see the justification layer).
- Multiply's result-bound claims carry a kit
  (`signed_multiply.cc: result_claim_hints`): channel rows, sign
  clauses, grid `[r]` halves, and the ge0/ge1/eq0 atom-definition
  families, plus per-claim additions for every reason/case literal —
  but **never for the claimed bound itself**. The claim is stated over
  the result's bits, so its own atom appears in no constraint the
  checker propagates; and because `def_line_for` *creates* missing
  atoms, hinting a per-inference value's definitions permanently mints
  fresh defining rows and ladder links at every inference. That grows
  the live database linearly with search nodes and turns every
  hint-free step's cost with it — checking goes quadratic in node
  count on wide-but-shallow trees (the PR #471 review regression:
  2–9x and climbing with instance size).
- Unit propagation cannot cross between two order atoms of the same
  variable (reason `[y>=5]` to sign-clause literal `[y>=1]`) through
  their bit-level definitions — the bits stay unpinned — and the ladder
  link lines the tracker emits at atom creation are not recorded
  anywhere citable. `product_justify::add_order_bridge_hints`
  pol-derives the needed ladder clause from the two atoms' defining
  rows, exactly as the tracker builds its own chain lines, and hints
  the fresh line.
- To debug a failing hinted claim, sed-strip the hints
  (`s/^rup ([^:]*):.*;$/rup \1;/` — note claims emitted under a reason
  render `>= K:` with no space before the colon) and re-verify: a pass
  means the hint set is incomplete, a failure means the claim itself is
  wrong. `veripb --trace-failed` shows where propagation stalls;
  `--trace-ids N..=N` shows where a cited constraint came from.

## Line caches (divide/modulus)

Divide's justifications would otherwise re-derive the same chains for
every inference in a pass, and across passes the bound values repeat
heavily. Derived lines are cached and cited instead, split by how the
cache key behaves — the veripb cost model above is why the split
matters, since divide's final claims are hint-free:

- Magnitude-corner chains (whole Subprocedure 7.1/7.2 derivations keyed
  only by `(direction, a bound, b bound)`), the quotient filter's
  assumed-bound grid lines and the operand/assumed bound lines live in
  constraint-lifetime maps at `ProofLevel::Top`. Their key populations
  stay small (hundreds), and each entry saves kilobytes per reuse.
- The x-side chains' keys churn with x's bounds; a standing copy of
  each would flood the checker's live database and tax every later
  hint-free step (a full-Top experiment cost 9x check time on
  modulus). They share a per-pass `PassChains` cache at
  `ProofLevel::Current` — justification scopes forget Temporary lines,
  and backtracking cleans Current ones up.
- Cached lines are derived under just their support literals, always a
  subset of every citing inference's reason (each merges
  `side_reason(...)` into its own), so the citing claim's negation
  discharges the guard terms.
- The derivation helpers take a defaulted `ProofLevel result_level`
  applying to the final line only; intermediates stay Temporary, since
  a pol result stands alone once emitted. Every early return must
  honour it — a trivial-bound shortcut still pinned to Temporary
  surfaces as veripb's "constraint ... has already been deleted".

## Hard-won rules

- RUP cannot combine two opposing linear bounds on the grid sum — that is
  a cutting-planes step; pol-add them before claiming a contradiction.
- Hint assembly must never route a fresh-valued literal through
  `def_line_for` / `need_pol_item_defining_literal`: those *create*
  missing atoms, permanently. Only ever ask for definitions of atoms
  that exist independently — reason literals, case literals, and the
  fixed ge0/ge1/eq0 families.
- When a checker step is hint-free by design, ask what its cost scales
  with: `perf` on veripb plus prefix-truncation timing (cut at
  `% backtracking` markers, append `conclusion NONE`) separates
  per-step cost from accumulating live-database cost in minutes.
- Syntactic `ia` implication checks are coefficient-exact, and search
  order varies with memory layout, so a proof-shape change in their
  antecedents can pass every local run and still fail on other CI
  lanes. Local batteries validate hint *completeness* (propagation
  either reaches the conflict or it does not); they do not validate
  removing a restatement that an `ia` implication depends on.
- Bounds used by a justification must be axioms (initial-domain rows,
  atom definitions) or carried by the reason; a case's liveness test must
  only consult values the proof can see the same way.
- Tabulation masks broken propagation proofs: probe with BC and large
  domains (`gcs/constraints/innards/product_justify_test.cc` is the
  fragment harness for doing this one helper at a time, with each claim
  restated as a checked `ia` — pol lines are sound whatever they compute,
  so only the restatement catches a wrong derivation).

## Known scope limits (documented, not bugs)

- View shapes self-verify (workflow 1) only: cake's scp grammar takes
  bare variables and constants, so there are no chain cases for views.
  Repeated variables *are* chain-verified (`multiply_square_*`,
  `multiply_result_alias_sat`).
- A product of two different views of one variable gets independent-
  interval box reasoning, not vertex-tight quadratic bounds.
- Divide/Modulus keep the stage-fixpoint strength floor rather than
  direct-division bounds consistency.
