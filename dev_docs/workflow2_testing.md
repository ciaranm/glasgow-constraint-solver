# Workflow-2 (cake_pb_cp chain) test coverage

The solver's *own* proofs are checked by veripb in CI for essentially every
constraint (workflow 1: the data-driven `*_test` binaries). This doc is about
**workflow 2** — `cake_pb_cp` independently re-derives the OPB from the `.scp`,
veripb checks the solver's proof against *that*, and `opbdiff --match-labels`
confirms the two OPBs agree by `@label`. Workflow 2 is what protects all the
encoding/label reconciliation (names, orientations, `@c`/`@i`/`@b` labels) from
silent regression.

## The `.scp` wire format

The `.scp` is versioned, and both ends of the chain check the version. A
document is exactly four tagged sections, in order:

```
(
  (version 1)
  (variables (X -3 3) (Y 0 3))
  (constraints (_1 abs X Y))
  (prob_type enumerate)
)
```

`prob_type` is the bare atom `decide` or `enumerate`, or the list
`(minimize var)` / `(maximize var)`. `innards::write_scp` emits this and
`gcs::read_scp` consumes it, returning an objective as
`ScpModel::minimise_variable` (a `(maximize V)` comes back as the negated view,
mirroring `Problem::optional_minimise_variable()`) without posting it, so that
enumerating an optimisation document stays possible — `glasgow_scp_solver` is
the caller that hands it to `Problem::minimise()`.

For the chain to check a maximisation at all, the two ends have to agree on how
the objective is *encoded*, not just what it is. cake re-derives `(maximize V)`
as `min: -1 i[V][b0] -2 i[V][b1] ...` over V's own bits, so an offset-free
negated objective — exactly what `Problem::maximise()` stores — is deviewed the
same way rather than being hosted on its own proof-only bit vector
(`ProofModel::write_preamble`). A hosted vector is invisible to cake, and the
solver's proof would cite view-linking labels (`@c[neg_view_of_V][viewle]`)
that cake's OPB has no counterpart for, failing the chain on an unknown label.

The reader rejects any version other than 1
outright rather than guessing at an unknown grammar, which is what makes a
future format change a clean failure instead of a misread. Upstream's reference
for the format lives outside this repo (cake's `SEXP_FORMAT.md`); the reader is
the authority for what we accept, and `cake_pb_cp` for what the verified encoder
accepts.

## Writer/reader symmetry is a requirement, not a nicety

`gcs::read_scp` must have a case for **every** keyword `Constraint::s_expr()`
can write. The chain runner's first step re-solves the `.scp` with
`glasgow_scp_solver`, so a keyword the reader has never heard of fails the chain
before `cake_pb_cp` is even invoked — and the failure looks like a solver bug,
not a coverage gap. This is not automatic: `s_expr()` is a per-constraint
override, so a new constraint can introduce a keyword and nothing notices.

Two checks enforce it, between them covering everything that writes a `.scp`:

- **Constraint tests, in process.** `verify_proof_and_dispose` calls
  `test_innards::check_scp_writer_reader_symmetry`, which reads the test's own
  `.scp` back and fails if a keyword has no case
  (`ScpUnsupportedConstraintError`). A new constraint's own test is what catches
  the omission.
- **Examples, benchmarks and frontends.** `run_test_and_verify.bash` runs
  `glasgow_scp_solver --parse-only` over the `.scp` the run wrote. That binary
  exits **2** for an unknown keyword and **1** for any other read failure, and
  only 2 fails the test. Its path comes from `build/scp_solver_path`, which
  CMake generates beside the binaries, so no `add_test` registration needed
  changing; the check simply skips outside a build tree. This lane matters
  because some constraints are only ever posted by an example — `LexSmartTable`
  wrote the un-parseable keyword `lex` for months precisely because its only
  caller is `examples/smart_table_lex`.

Two narrower things neither check demands:

- **Not every instance need round-trip.** A view operand renders as
  `(-X + 17)`, which the grammar does not parse; a plain `ScpReadError` is
  tolerated. Only a missing *keyword* fails. The cost is that a model whose
  first unreadable thing is a view hides any bad keyword later in the same file
  — `n_queens` is one — which is part of why both lanes exist.
- **Test-fixture constraints are exempt**, by the `test_...` naming convention
  (`test_tabulated_product`, `test_product_fragment`). Use that prefix for an
  ad-hoc Constraint that exists only to drive one piece of proof machinery.

Worth knowing what this caught when it was turned on: `difference` and
`cumulative_optional` had no reader case at all, and neither showed up in a hand
audit of `constraint_type()` overrides done a fortnight earlier. It also turned
up a genuine writer bug — `DifferenceConstraints::s_expr` rendered a
half-reified edge's condition with `s_expr_term_of(Literal)`, which collapses a
condition to the bare variable name, so `D >= 2` and `C = 1` were written
identically and the `.scp` described a different problem than the one solved.

Two related rules that fall out of the same principle — the `.scp` describes the
*constraint*, not how it was propagated:

- **Alternative propagators share a keyword.** `Regular`, `RegularLegacy` and
  `RegularBacchus` all write `regular`. (Note the encodings do not all match:
  RegularLegacy's OPB is byte-identical to Regular's and chains, whereas
  RegularBacchus's upfront encoding labels rows cake has no counterpart for, so
  a proof *it* emits still fails against cake's OPB.)
- **Anonymous variables come back anonymous.** A variable created without a name
  is written `_N`, which is exactly the spelling `Problem::check_name()`
  reserves — so the reader recreates it unnamed rather than passing the name
  through, mirroring what `post_autonumbered` does for `_N` constraint labels.

## What `cake_pb_cp` does not encode

Constraints whose keyword the verified encoder has no rule for, so they cannot
chain at all no matter what the solver does. The solver still writes and reads
them; the gap is upstream.

| Constraint | keyword | reachable from |
|---|---|---|
| `BinPacking` | `binpacking` | MiniZinc, XCSP |
| `MDD` | `mdd` | MiniZinc, XCSP |
| `Power` / `PowerTable` | `power` | MiniZinc, XCSP |
| `MinDistance` | `min_distance` | library only |
| `Nogoods` (posted) | `nogoods` | library only |

Also upstream: `notin` (no solver writer), views (affine operands), and `in`
over a member list with **two or more variables** — that last one parses on both
sides but fails at VeriPB, because the solver's `f[N][inlt/ingt/in]` flags are
not cake's `x[id][i][ge/le/eq]` selectors (#487; one variable chains fine, which
is why `in_var_sat` passes).

Two complementary mechanisms:

## Part B — curated `.scp` chain harness (built)

`verified_encodings/scp_cases/`: a MiniZinc-style table of small, curated `.scp`
files, one+ per cake-encodable constraint/form, driven by
`verified_encodings/run_scp_chain.bash`:

```
glasgow_scp_solver --all --prove <scp>          # re-emits scp (+ prob_type) + opb + pbp
cake_pb_cp <scp>                  -> verifiedopb # re-derive OPB (verified)
veripb verifiedopb pbp --elaborate corepb        # elaborate (VeriPB = untrusted translator)
cake_pb_cp <scp> corepb           -> "s VERIFIED" # verified checker re-checks the core
opbdiff opb verifiedopb --match-labels [mode]
```

The **verified checker has the last word** (step 4) — VeriPB is only an untrusted
elaborator, so this is the real workflow-2 trust story, not a VeriPB check.

One ctest per case. **Where `cake_pb_cp` is absent** (e.g. GitHub CI, where
building CakeML is awkward) the runner degrades to a workflow-1 self-verify
(`veripb` on the solver's *own* OPB/pbp) rather than skipping, so the case is
still exercised; it skips (`SKIP_RETURN_CODE 77`) only when `veripb` itself is
absent. To run the full chain locally rather than the fallback, put `cake_pb_cp`
on `PATH` (alongside `veripb`/`opbdiff`, e.g. symlinked into `~/.cargo/bin`) or
point `CAKE_PB_CP` at the built binary. The `(prob_type enumerate)` `.scp`
section (so cake emits `preserved:`, which `decide` would not) means
**SAT cases verify by complete enumeration** — not just UNSAT — so the table can
exercise the naturally-satisfiable forms too.

Per-case `opbdiff` mode (3rd runner arg):
- `strict` — exact label match (abs, comparisons, lin_less_equal, …).
- `aux` — match modulo a same-polarity selector flag *name* (not_equals,
  lin_not_equals: cake names it `b[name][ne]`, the solver `f[N][gt]`).
- `none` — chain-only: all_different, whose selector has the *opposite* polarity
  to cake's and whose multiple identical-looking selectors defeat label matching
  (the deferred conform-the-solver item).

**Domains are bits-encoded on purpose**, to dodge the direct-only-vs-bits
divergence (a `[0,1]` variable is direct-encoded by the solver but bits-encoded
by cake, so the OPB constraint *counts* differ and veripb rejects the chain).
For the same reason the **reified forms are deferred** — their `(C = 1)`
condition variable is `[0,1]`.

Adding a constraint to the harness is: drop a `.scp` in `scp_cases/` and add one
`add_scp_chain_test(<case> <mode>)` line.

## Part A — three-way proof check in the data-driven tests (sketch)

**Superseded in part.** What actually landed instead of the three-way enum below
is `gcs/constraints/innards/cake_probe.hh`: `verify_proof_and_dispose` calls
`cake_probe_chain`, which runs the whole chain over the test's own `.scp` and
logs a `CAKECHAIN <name> <outcome>` line. It is a *probe*, not an assertion — it
never fails a test — and is off unless `GCS_TEST_CAKE` is set, so it is a way to
measure coverage over the random instances rather than to gate on it. The
reader-symmetry check above is the part of this idea that is on by default,
because it is cheap and needs no external tools.

The remainder of this section is the original design sketch, kept for the gating
analysis (which still describes what would be needed to make the chain an
assertion over random instances).

The random/edge-case instances live in the `*_test` binaries, which already
thread a `proofs` bool into `solve_for_tests*(p, proof_name, …)` and loop
`for (bool proofs : {false, true})`. `proof_name` being set makes `solve_with`
emit the proof (`ProofOptions`); workflow-1 verification then runs externally.

The sketch: widen that bool to a **three-way mode**, so the same random
instances can also drive the cake chain (where they're eligible):

```cpp
enum class ProofCheck { None, SelfVerify, CakeChain };
// for (auto check : {ProofCheck::None, ProofCheck::SelfVerify, ProofCheck::CakeChain})
```

- `None`        — `proof_name = nullopt` (today's `proofs == false`).
- `SelfVerify`  — emit + veripb the solver's own proof (today's `proofs == true`).
- `CakeChain`   — emit, then run `cake_pb_cp` + veripb (+ opbdiff) on the `.scp`,
  i.e. workflow 2 over the random instance.

`CakeChain` is **gated** per instance; if any gate fails it falls back to
`SelfVerify` (or skips the cake step):
1. **cake-encodable constraint** — abs, all_different, equals/not_equals,
   comparison, linear (the families cake knows). The other constraints opt out.
2. **bits-encoded domains** — every variable's domain needs ≥ 2 bits, else the
   direct-vs-bits divergence fails the chain on the constraint count. The random
   generator frequently picks small domains, so this gate trims most instances
   today.
3. **tools present** — `cake_pb_cp` + veripb on PATH, else skip.

### Why it's scaffolded-but-mostly-off until CakePB catches up

The whole point of Part A is the *edge cases* (small/awkward domains, views, dup
variables). But gate (2) excludes exactly the small-domain instances, because of
the **direct-only-vs-bits** divergence currently with the CakePB authors. So
until that's resolved, `CakeChain` would be green only on the large-domain
random instances. The plan:

- Land the three-way enum + the `CakeChain` plumbing (gated to bits-domains), so
  it's reviewed and ready and gives *some* coverage now.
- When direct-vs-bits is fixed upstream, drop gate (2) and the random edge-case
  coverage switches on broadly with one change.

### Hook points

- `gcs/constraints/innards/constraints_test_utils.hh` — `solve_for_tests*` /
  `solve_for_tests_with_callbacks`: where `proof_name` becomes `ProofOptions`.
  The `CakeChain` arm runs the chain after the solve writes `<name>.{scp,opb,pbp}`
  (via a helper mirroring `verified_encodings/run_scp_chain.bash`, or a `system()`
  call from a shared test utility).
- The per-test `for (bool proofs : {false, true})` loops become a three-way loop;
  cake-encodable tests opt their constraint into the `CakeChain` arm.
