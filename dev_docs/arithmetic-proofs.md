# Arithmetic constraints: propagation and proofs

How Multiply, Divide, Modulus and Power propagate and justify their
inferences. The encoding is cake_pb_cp's, fixed by the verified encoding
chain (`verified_encodings/`); the proofs follow Chapter 7 of Matthew
McIlree's thesis, adapted to cake's sign-magnitude scheme. There is no
in-proof reformulation anywhere: every justification cites the OPB rows
and combines them with `pol`, `ia` and hint-free `rup` steps.

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
  atom that the driver's negated goal later supplies as a unit;
- `channel_bound_to_magnitude` (thesis 7.3, cake flavour): one pol add
  against the matching channel row; directions flip on the negative
  branch; `strengthen_nonzero` lifts a useless non-positive magnitude
  lower bound to one under `[v != 0]` for spanning co-factors;
- `grid_sum_lower_bound` (thesis 7.1): pure cutting planes, O(n·m);
- `grid_sum_upper_bound` (thesis 7.2): per-row contradiction subproofs,
  with the per-cell W-lines cached in the grid; a zero magnitude takes a
  direct-RUP path (the grid empties by unit propagation);
- `channel_grid_bound_to_result` (thesis 7.4, cake flavour): pol against
  the matching mag_Z row, then one **hint-free** RUP of the bound claim.
  There is deliberately no standalone sign-atom discharge: a mixed sign
  case does not entail the result's sign when the non-negative operand
  may be zero; the claim's own negation pins the sign atom instead, or
  unit propagation closes through the sign clauses and the eq0 rows;
- `conclude_by_sign_cases`: the fixed-shape replacement for case
  resolution. One red-with-empty-witness derivation of
  `reason => conclusion`; the subproof takes each case pattern's premise
  pol-added onto the negated goal (premises that are already refutation
  clauses — factor-bound clashes — are used directly: adding the negation
  would inject its terms as free slack), closes dead cases with a plain
  RUP clause of the opposite atoms, emits any zero-refutation units
  (`[v=0]` empties the grid against the reason's result bounds), and runs
  the nested saturating cut one dimension at a time. Because `[v>=0]` and
  `[v<0]` are complementary atoms — unlike the thesis's two's-complement
  sign bits — no separate zero cases are needed, and a square's mixed
  patterns die as tautology clauses.

Inference drivers: product bounds are thesis Procedure 7.5 (per live sign
case: channel, 7.1/7.2, channel to the result, conclude); factor and
square bounds are Procedures 7.6/7.7 — never enumerate propagator logic,
just refute the excluded range, with the far side of that range being the
target's *current* bound carried by the reason. The square's inner
square-root lift is sequenced after the outer clamp so each refuted
branch is uniformly too small or too big, which is exactly when the
box-shaped case refutations apply.

## Hard-won rules

- VeriPB's hinted RUP restricts propagation to the hinted lines: a claim
  that needs the sign-clause chain must be emitted hint-free. (Complete
  hint sets are a planned optimisation; half-hinting breaks.)
- RUP cannot combine two opposing linear bounds on the grid sum — that is
  a cutting-planes step; pol-add them before claiming a contradiction.
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
