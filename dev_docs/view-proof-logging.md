# View proof-logging support

This document describes the proof-logging machinery that makes
`ViewOfIntegerVariableID` operands work as constraint arguments.

Background: `ViewOfIntegerVariableID` is a lightweight affine wrapper
(`±X + c`) over an underlying `SimpleIntegerVariableID`. Constraints
accept views interchangeably with the bare variable, which is convenient
in user code but historically created a gap in proof logging: VeriPB
needed to see the view's domain, atom-level axioms, and link to the
underlying variable, before any propagator-emitted constraint that
mentioned the view could be checked.

The framework now bridges that gap for constraints whose proof obligations
fit the "stage 0–4" envelope below. Constraints that need more (Abs,
AllDifferent's interior pruning) remain outside.

## What works today

The view-wrap sweep registers `add_view_wrap_sweep` entries in
`gcs/CMakeLists.txt` for each constraint that participates. Constraints
whose proof obligations stay within the "four ingredients" envelope
described below currently verify under all wraps. The two known
exceptions — Abs and AllDifferent's interior pruning — are tracked under
[Known gaps](#known-gaps).

To opt into the sweep when working on view proof-logging:

```shell
cmake -S . -B build -DGCS_ENABLE_VIEW_WRAP_SWEEP=ON
```

The harness and the `--view-wrap=N` / `--view-position=K` CLI flags are
always built; only the ctest registrations are gated. To run a single
sweep manually, invoke the test binary with the flag, e.g.
`./build/equals_test --view-wrap=11 --view-position=pall --prove eq_w11`
and verify with `veripb eq_w11.opb eq_w11.pbp`. The exact list of
registered sweeps is the source of truth — read it from
`gcs/CMakeLists.txt` rather than from memory.

## The four ingredients

The framework supplies four pieces, each lazily emitted at the right
moment so the cost is proportional to atoms actually exercised:

### 1. The view's bit vector and definitional link

When a view is first referenced (`need_view`), the framework creates a
proof-only integer variable `V` for it and emits a definitional link
constraint between `V` and the underlying `X`:

```
V - s·X = c        (encoded as a >=/<= pair on bit-form sums)
```

where `s = ±1` from `negate_first` and `c = then_add`. The pair's line
IDs are stored in `view_link_ids`. See `NamesAndIDsTracker::need_view`.

### 2. Atom-level eq-links V=v ⇔ X=k

Every time the framework introduces a new `V_eq_v` atom (via
`need_direct_encoding_for`), it also emits the matching `X=k`
reification and two RUP clauses linking them in both directions:

```
~V_eq_v ∨ X_eq_k        ≥ 1
~X_eq_k ∨ V_eq_v        ≥ 1
```

This means UP can propagate either way across the V↔X equality boundary
without having to chain through the bit vector.

### 3. Atom-level ge-links V≥v ⇔ X-condition

Every time `need_gevar` reifies a new `V_ge_v` atom on a view's
proof-only variable, it pol-derives the biconditional V↔X order-encoding
link via three operands:

```
D1: ~V_ge_v ∨ X-cond              (V≥v → X-cond)
D2: V_ge_v ∨ ~X-cond              (X-cond → V≥v)
```

The components combined for D1 are `(V_ge_v reif fwd)`, the LE half of
the view link, and `(X-atom rev)`; D2 uses the symmetric three. The
bit-form terms cancel, leaving the atom-level clause after saturation.
The X-side atom is introduced first via a recursive `need_gevar`
on the underlying, so its reif is already in F. See lines 656–686 of
`names_and_ids_tracker.cc`.

The eq-link and ge-link emissions are queued through
`emit_proof_line_now_or_at_start` so they land alongside the standard
order-encoding chain links at the top of the proof (or as the very next
line, if the proof is already past the start), not as extra OPB axioms.

### 4. Deview-form derivation for emitted constraints

When the model writer adds a constraint whose body mentions view operands,
`ProofModel::add_constraint` records the V-form line and queues a
deview-form pol derivation that materialises the same constraint in
X-form. The X-form is obtained by replacing each view term using the
appropriate view-link half (`s = +1` uses `link.first` for LE, `link.second`
for GE; `s = -1` flips). See `NamesAndIDsTracker::derive_deviewed_form_for`.

For runtime propagator emissions we do not auto-derive the deview-form
unconditionally — it produced 230 MB / 2.4 M-line proofs on
`element_test_var2d`. Callers that *need* the X-form opt in via
`emit_rup_proof_line_under_reason_then_deview`, which emits the V-form
RUP and then triggers the deview-form pol on its line content.

The opt-in pattern is exercised by `justify_abs_hole` and the other
`justify_abs_*` helpers in `gcs/constraints/abs/justify.cc`; consumers
that compose pol over the result use `PolBuilder` in deview-mode, which
substitutes a deviewed line ID at each `add(ProofLine)`. See
`PolBuilder(const NamesAndIDsTracker &)`.

## What gets emitted, and when

The lifecycle for a typical "view mentioned in a propagator inference"
goes:

1. Model phase: `need_view(V)` creates V's proof-only variable and emits
   the definitional link (two OPB constraints, IDs stored in
   `view_link_ids`).
2. Model phase: `add_constraint(body)` registers the V-form line and
   queues the deview-form pol; the auto-derive lands at the top of the
   proof file when the proof-logging phase opens.
3. Proof phase: the propagator infers a literal touching a V-atom. The
   framework's `need_proof_name` triggers `need_gevar(V, k)`, which:
   - Emits the V_ge_k reification (red pair).
   - Recursively triggers `need_gevar(X, k')` on the underlying.
   - Emits chain links from V_ge_k to its higher/lower neighbours.
   - Pol-derives D1 and D2 (the V↔X ge-link halves).
4. Proof phase: the same path for V_eq atoms goes through
   `need_direct_encoding_for`, which emits the matching X_eq reif plus
   the two eq-link RUPs.
5. Proof phase: the propagator emits its explicit pol/rup steps; any RUP
   that mentions a view operand and is consumed by downstream pol can
   use `_then_deview` to get the deviewed X-form line published as well.

## Known gaps

The framework as it stands does *not* close the proof for two
constraints under views, even with all four ingredients in place:

- **Abs.** The propagator's value-pruning RUPs (from
  `justify_abs_v1_le_v2_ub`, `justify_abs_v2_le_big_m`,
  `justify_abs_v1_ge_neg_v2_ub`, and the interior-hole step) leave behind
  shapes that the `JustifyExplicitlyThenRUP` auto-RUP cannot close by UP
  alone. The bridge it needs is a cross-constraint polynomial composition
  that UP doesn't do: typically combining the value-pruning candidate
  with the V's bit-domain bound, then chasing through the half-reified
  body. The eq-link and ge-link emissions are correctly in F by the time
  the auto-RUP runs — what's missing is a per-call pol step that
  materialises the inferred literal directly.
- **AllDifferent.** Same root cause for the Hall-set-style backtracking
  RUPs: UP can't enumerate.

A speculative partial mitigation (emitting an extra
`emit_resolution(r1, r2)` from each two-branch `justify_abs_*`) shifted
the first failure point deeper into the proof on most wraps without
fixing any of them end-to-end. The remaining failures after that
mitigation are still UP-uncomposable. We reverted the mitigation; see
the conversation history.

## Pointers for future work

If you want to close the Abs gap, the auditable path is to migrate the
non-hole `justify_abs_*` to `JustifyExplicitlyOnly` and let each function
emit a tailored pol chain that materialises its inferred literal as a
direct unit clause (so the closing RUP — if any — is trivial). This is
more code per justify function but gives explicit control over what UP
needs to see.

If the eager V↔X ge-link emission ever becomes a bottleneck for very
wide domains, the limit is bounded by atoms exercised (not domain size),
because the emission piggy-backs on `need_gevar`. The trade-off lives in
`names_and_ids_tracker.cc:656–686`.
