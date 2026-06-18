# Workflow-2 (cake_pb_cp chain) test coverage

The solver's *own* proofs are checked by veripb in CI for essentially every
constraint (workflow 1: the data-driven `*_test` binaries). This doc is about
**workflow 2** — `cake_pb_cp` independently re-derives the OPB from the `.scp`,
veripb checks the solver's proof against *that*, and `opbdiff --match-labels`
confirms the two OPBs agree by `@label`. Workflow 2 is what protects all the
encoding/label reconciliation (names, orientations, `@c`/`@i`/`@b` labels) from
silent regression.

Two complementary mechanisms:

## Part B — curated `.scp` chain harness (built)

`verified_encodings/scp_cases/`: a MiniZinc-style table of small, curated `.scp`
files, one+ per cake-encodable constraint/form, driven by
`verified_encodings/run_scp_chain.bash`:

```
glasgow_scp_solver --all --prove <scp>          # re-emits scp (+ (enumerate)) + opb + pbp
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
point `CAKE_PB_CP` at the built binary. The `(enumerate)` `.scp` element (so cake
emits `preserved:`) means
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
