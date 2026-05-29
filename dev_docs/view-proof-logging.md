# View proof-logging support

`ViewOfIntegerVariableID` is a lightweight affine wrapper `±X + c` over an
underlying `SimpleIntegerVariableID`. Constraints accept a view wherever
they accept a bare variable, so the same `X` can reach several constraints
through several different wrappers. This document explains how proof
logging copes with that: first the idea (no code), then what you actually
need to keep in mind when writing propagators or touching the view
machinery.

The short version: every constraint currently registered in the view-wrap
sweep verifies under every wrap. Abs and AllDifferent — historically the
hard cases — are now in that set.

## Part 1 — The idea, on top of the thesis

This assumes you know the proof-logging foundations from chapter 3 of
Matthew's thesis. Recapping only what we build on:

- Each integer variable is represented in the pseudo-Boolean model by a
  **bit-vector** `BinEnc(X)` (magnitude bits, plus a sign bit / offset for
  variables that can go negative).
- On top of the bits sit **order atoms** `[X ≥ v]` and **equality atoms**
  `[X = v]`, each *defined* by a reified constraint against the bits
  (`[X ≥ v] ⇔ BinEnc(X) ≥ v`), together with the order-consistency chain
  (`[X ≥ v] → [X ≥ v-1]`).
- The OPB file states the constraints over these atoms/bits. The proof
  derives new facts with **RUP** (unit propagation to contradiction),
  **`pol`** (cutting-planes: add/multiply/saturate existing lines), and
  **`red`** (redundance-based introduction of fresh atoms).
- A propagator inference "literal `ℓ` follows from reason `R`" is logged
  as the clause `¬R ∨ ℓ` and discharged either by RUP or by an explicit
  derivation.

### The problem a view poses

A view `V = sX + c` (`s = ±1`, `c` an integer) is just an affine image of
`X`. The tempting move is to write every constraint over `V` by
substituting `sX + c` and reasoning in `X`'s atoms. That breaks down
because constraints are posted generically over "an operand", and one `X`
may be wrapped by several views at once. Rewriting into `X`-space makes the
atoms that appear in the OPB depend on *which* wrapper a constraint was
given, so the generic constraint-logging code can no longer treat every
operand identically.

### What we do instead

We give the view its **own encoded variable**. `V` gets its own bit-vector
`BinEnc(V)`, its own order and equality atoms, all defined by reification
exactly as chapter 3 defines them for any integer variable. From the
proof's point of view `V` is indistinguishable from a bare variable, and
*every* constraint body and propagator inference that mentions the operand
is logged purely in `V`'s atoms and bits. The generic machinery never has
to know it handed out a view.

The only thing tying `V` to `X` is a single **definitional link** axiom:

```
V − sX = c
```

emitted as a `≥`/`≤` pair over the two bit-vectors. This is the one and
only place the two encodings meet.

### Why that works

- **Everything from chapter 3 transfers for free.** `V` has the identical
  structure to a bare variable, so any fact the chapter-3 machinery can
  prove about a variable, it can prove about `V`. A constraint that is
  stated and propagated entirely in `V`-space verifies with zero awareness
  that `X` exists.
- **The link is only needed when an inference crosses representations** —
  e.g. two constraints share `X` through different views, or a
  propagator's reason is naturally about `X` but its consequence is about
  `V`. To move a fact from `V`-space to `X`-space you *add* the `V`-form
  line to the link: the `BinEnc(V)` terms cancel and an `X`-form line
  drops out (and symmetrically the other way).
- **But unit propagation cannot do that crossing by itself.** Combining a
  `V`-fact with the link is a *linear addition of two constraints*, and UP
  (hence RUP) only ever derives forced literals from individual
  constraints — it never adds two together. So a crossing must either be
  an explicit `pol` step, or be pre-supplied in a form UP *can* consume.
- **So we pre-derive the boundary as atom-level clauses.** For each atom
  actually used, the framework derives the biconditionals
  `[V ≥ v] ⇔ [X ≥ k]` and `[V = v] ⇔ [X = k]` as small clauses. Then any
  time a proof needs to carry a *single atom* across the `V`/`X` boundary,
  UP does it in one step — no bit-chasing, no `pol`. These are emitted
  lazily, only for atoms that appear, so the cost tracks the proof rather
  than the domain size.

### The three invariants that make it sound

The design is simple, but it is easy to emit something *almost* right.
Three invariants are load-bearing; both historical Abs/AllDifferent
failures were violations of the first two.

1. **Representation consistency for cancellation.** When you combine lines
   with `pol` to cancel a variable, both lines must express that variable
   in the *same* representation. Constraint bodies in the OPB are in
   `V`-form for a registered view, so a propagator operand you resolve
   against them must also be in `V`-form. Devieweing the operand to
   `X`-form first means `BinEnc(V)` and `BinEnc(X)` never meet — they are
   different variables, related only by the link axiom — so nothing
   cancels and the derivation strands.

2. **Big-M is sized to the bit-vector, not the value domain.** A
   conditional line "`reason → (bound on V)`" carries a big-M coefficient
   on the reason literals, large enough to make the line vacuous when the
   reason is false. That M must cover the full range of `BinEnc(V)` *as a
   bit-vector*, which can be **wider than `V`'s value domain**: a view of
   `[1,8]` needs a 4-bit vector spanning `0..15`. Size M from the value
   domain instead and the line is only valid *given* `V`'s domain-bound
   constraint — and folding that bound in is an addition, not a unit
   propagation, so RUP can never recover it and the line fails to verify.

3. **RUP cannot compose across constraints.** The general form of the
   above: any step that needs a linear combination — translating across
   the link, or combining an inference candidate with a domain bound —
   must be an explicit `pol`/`red`. If you find yourself hoping RUP will
   "put two constraints together", it won't.

## Part 2 — Working with views in the solver

### If you are writing a propagator

Almost always: **do nothing special.** Post over the operand and infer
over it exactly as if it were a bare variable. The framework introduces
the view's encoded variable, its atoms, and the links on demand, and
literals you place in reasons or justifications are logged in the view's
atoms automatically. A justification that only uses RUP and stays within a
single variable's atoms just works under views.

You only need to think about views when your justification emits **explicit
`pol`**:

- **Resolve `V`-form operands against `V`-form constraints.** The
  definitional/encoding lines the framework hands you for a registered
  view — half-reified constraint bodies, and the reification `Def` lines
  you fetch via `need_pol_item_defining_literal` — are in `V`-form. Emit
  the operand bounds you intend to cancel in `V`-form too. Concretely:
  emit them with `emit_rup_proof_line_under_reason` (which stays in
  `V`-form), **not** `..._then_deview` (which hands back the `X`-form
  line). This was the Abs `justify_abs_v2_le_big_m` fix. Empirically it was
  the *only* one of Abs's consequence-bound helpers that needed it — it
  resolves the operand out of *both* half-reified sign branches to get an
  unconditional bound, so both resolutions must cancel cleanly. The others
  verified either way (a single resolution plus RUP-from-reason closes via
  the atom-level link). The safe default is still: keep any operand you
  intend to cancel in `V`-form.
- **Cross to `X` only when you actually need it.** If a downstream consumer
  genuinely needs the `X`-form of a line, opt in with
  `emit_rup_proof_line_under_reason_then_deview`, or compose with a
  `PolBuilder` in deview-mode (it substitutes the deviewed line ID at each
  `add`). This is opt-in because unconditional deview derivation blew a
  single `element` test up to a 230 MB / 2.4 M-line proof.
- **Don't ask RUP to fold in a bound or the link.** If your inference
  needs the view's domain bound, or needs to move across the link, write
  the `pol` step explicitly (invariant 3).

Reasons over a view (e.g. `{v ≥ lb, v ≤ ub}`) are fine: they are logged in
the view's atoms and UP crosses to `X` through the eq/ge links if the rest
of the proof needs it.

### If you are touching the view machinery itself

- **Measure spans against the emitted representation.** Any code that
  computes a coefficient bound, big-M, or range over a term that *might* be
  a view must measure against the variable that actually appears in the
  emitted line. For a registered view that is `V`'s own bit-vector — use
  its bits — not the underlying `X`'s bits plus the offset, even though the
  latter has the same *value* range. `NamesAndIDsTracker::reify` is the
  worked example (and was invariant 2's bug): it now sizes the reification
  constant from the registered view's own bits.
- **Keep atom introduction symmetric.** Introducing an atom on `X`
  backfills the matching `V` atoms for every registered view, and
  introducing an atom on `V` introduces the matching `X` atom; registering
  a view backfills atoms that already existed on `X`. If you add a new path
  that introduces atoms, preserve that symmetry or links go missing for
  whichever side appeared first.
- **The link is the only bridge.** Keep it strictly definitional. Never
  write code that assumes `V` and `X` share bits or atoms; they share
  nothing but the link axiom.

### How the machinery is laid out

Four pieces implement the above, each emitted lazily so cost tracks atoms
actually exercised:

1. **View bit-vector + definitional link** — `NamesAndIDsTracker::need_view`
   creates `V`'s proof-only variable and emits the `V − sX = c` pair
   (`s` from `negate_first`, `c` from `then_add`), storing the line IDs in
   `view_link_ids`.
2. **Eq-links `[V=v] ⇔ [X=k]`** — `need_direct_encoding_for` emits the
   matching `X=k` reification and the two linking RUP clauses, in whichever
   order the atoms first appear.
3. **Ge-links `[V≥v] ⇔ X-cond`** — `need_gevar` `pol`-derives the
   biconditional from the relevant reification halves and the link, again
   symmetric in introduction order. These and the eq-links are queued via
   `emit_proof_line_now_or_at_start` so they land with the order-encoding
   chain at the top of the proof.
4. **Deview-form derivation** — `ProofModel::add_constraint` records the
   `V`-form body and queues a `pol` that materialises the `X`-form via the
   link (`derive_deviewed_form_for`). Runtime emissions do *not*
   auto-derive the `X`-form (size); callers opt in with
   `_then_deview` / `PolBuilder` deview-mode.

The reification big-M lives in `NamesAndIDsTracker::reify`; the operand-form
choice lives in the per-constraint `justify_*` helpers.

## Testing

There are three view policies, selected by `--view-position`:

- **uniform** (`=all`): every operand position takes the same wrap.
- **single** (`=K`): position `K` takes the wrap, the rest stay bare.
- **mixed** (`=mixed`): each position takes a *different* wrap from a fixed
  cycle (distinct large offsets, mixed signs). This is the only policy that
  puts two *different* views in one constraint at once — uniform and single
  never do — so it's the one that exercises cross-view cancellation and
  lines spanning two view bit-vectors of different widths.

`add_view_tests(name target n [mode])` in `gcs/CMakeLists.txt` registers
them, and is the source of truth for which constraints participate. It has
two tiers:

- the **mixed** test is registered **unconditionally** — it's a single cheap
  run per constraint and the most likely to catch a cross-view regression,
  so it's part of the ordinary `ctest` suite;
- the **full per-wrap sweep** (every wrap in `all_view_wraps()` × every
  position; ~18·(n+1) tests per constraint) is large and only registered
  under `-DGCS_ENABLE_VIEW_WRAP_SWEEP=ON`:

```shell
cmake -S . -B build -DGCS_ENABLE_VIEW_WRAP_SWEEP=ON
```

The harness and the `--view-wrap=N` / `--view-position=...` flags are always
built; only the per-wrap ctest registrations are gated.

Single manual run:

```shell
./build/equals_test --view-wrap=11 --view-position=all --prove eq_w11
veripb eq_w11.opb eq_w11.pbp
./build/lex_test --view-position=mixed --prove lex_mixed   # heterogeneous views
veripb lex_mixed.opb lex_mixed.pbp
```

## Status

All constraints registered in the sweep verify under all wraps, including
Abs and AllDifferent (closed once the representation-consistency and big-M
invariants above were enforced). `SmartTable` is deliberately *not* in the
sweep: it over-prunes under views, tracked in issue #238. A number of
constraints do not yet have view tests registered (e.g. `circuit`); read
`gcs/CMakeLists.txt` for the current list. Bringing one in (an
`add_view_tests(...)` line, once its test threads a `ViewWrapConfig`) is the
natural way to extend coverage — given the framework above, many should
verify with no constraint-side change.
