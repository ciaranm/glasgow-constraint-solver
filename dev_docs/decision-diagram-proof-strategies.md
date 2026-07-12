# Decision-diagram proof strategies: upfront vs per-call, and how to pick a default

Cross-cutting design note for the four "decision-diagram-shaped" propagators —
`Regular`, `MDD`, `Knapsack`, and `BinPacking`. All four prune a
layered/partial-sum diagram, and each has *two* proof-logging strategies for the
same propagation. This note records which strategy is the default for each, the
cost model that explains why, a predictive rule a propagator author can apply
*before* implementing, and the (both negative) results of probing scaffold
deletion and solver-side RUP hinting.

The measurements behind every number here were taken this session against the
rebased decision-diagram PR stack (VeriPB 3.0.2, veripb wall = median of 3). The
raw data and harness live in `~/claude/tmp/ddpr-analysis/` (the strategy
comparison) and `~/claude/tmp/ddpr-deletion-probe/` (the deletion / hinting
probe). The per-propagator PRs are #210 (Knapsack), #211 (MDD), #212
(BinPacking) and #213 (Regular); the hinting prototype is #497.

## The two strategies

Both strategies certify the *same* GAC pruning against the *same* natural OPB
encoding (per-`(state, val)` forward chains + per-layer exactly-one). They
differ only in **where** the proof-supporting intermediate lines are emitted.

- **Upfront** (`ProofLevel::Top` scaffolding). Once, before search, via
  `install_initialiser`, the constraint emits everything that does not depend on
  the runtime domain: forward/backward chains, per-state implications, per-layer
  at-least-one (ALO) clauses, phantom-node closures, and the statically-dead
  node lines. Each per-`propagate()` inference is then a *slim* sweep: at most
  one cache-gated `~state[i][q]` line, and the final `vars[i] != val` closes by
  RUP against the standing scaffold. Little or nothing is re-emitted per call.

- **Per-call** (`ProofLevel::Current`/`Temporary`, leaning on RUP). The OPB
  encoding and reified flags carry the definitional content; each
  `propagate()` emits whatever proof-supporting intermediates that call's
  inferences need (e.g. a re-derived DP/partial-sum aggregation, or per-`(parent
  state, val)` chains) and lets VeriPB RUP close the pruning. Intermediates are
  `Temporary`/`Current`, so they are deleted after the call or on backtrack.

## The cost model (the WHY)

The two strategies are *not* uniformly ordered, and — crucially — **proof size
and verification time can diverge**. The governing identity is:

> **veripb_time = #lines × cost-per-line = displacement × DB-tax**

- A **hinted** RUP (`JustifyUsingRUP{hints::Foo{...}}`) is checked in
  `O(#cited)`. A **hint-free** RUP — a bare `emit_rup_proof_line*`, *and*
  VeriPB's own solution-enumeration / backtrack RUPs — unit-propagates over the
  **entire live constraint database**, `O(#standing constraints)`.
- `ProofLevel::Top` lines **never leave the live DB**; `Temporary`/`Current`
  lines are deleted after the call / on backtrack. So an upfront scaffold of *S*
  lines adds an `O(S)` **DB-tax** to *every hint-free RUP in the whole proof* —
  even the ones that never cite it.

Decomposing the time ratio into two a-priori-knowable factors:

- **Displacement** (the line-count ratio) = how much per-`propagate()` volume
  the scaffold removes. Predict it from *what the per-call baseline emits per
  call*.
- **DB-tax** (the per-line cost ratio) = how much more expensive each line is to
  verify under the permanent Top scaffold. Predict it from *the size of that
  scaffold* (≈ its `red`/Top line count).

From which:

> Upfront wins **proof size** iff **displacement > 1** (the per-call baseline
> emits more per-call intermediate proof than the slim upfront sweep).
> Upfront wins **verification time** iff **displacement > DB-tax** — the per-call
> baseline must be *more than (DB-tax)× more verbose*, and the DB-tax grows with
> the size of the permanent Top scaffold.

Because the two winning conditions differ, a constraint can have a *smaller*
upfront proof that is *slower* to verify (Knapsack, below).

## Per-propagator results and defaults

Representative largest instance for each; search shape verified identical to the
digit between the two strategies (only the propagator is toggled — the tree does
not change). All proofs verified (`s VERIFIED`, zero failures).

| Propagator | Proof size (upfront vs per-call) | Verify time (upfront vs per-call) | Default | Opt-in |
|---|---|---|---|---|
| **Regular** (#213) | upfront **13–55× smaller** (9 MB vs 496 MB @7660 sol) | upfront **2.3–7× faster** (1.66 s vs 11.69 s) | **upfront `Regular`** | per-call `RegularLegacy` via `--legacy` |
| **MDD** (#211) | upfront **7–9× smaller** (1.8 MB vs 15.8 MB) | upfront **4–5× faster** (0.04 s vs 0.21 s) | **upfront (default)** | per-call **deferred** (see below) |
| **Knapsack** (#210) | upfront **3–6× smaller** (20.7 MB vs 121 MB) | upfront **3.6–18× SLOWER** (6.68 s vs 1.85 s) | **per-call `Knapsack`** | upfront `KnapsackUpfront` |
| **BinPacking** (#212) | upfront **6–10× BIGGER** (8 MB vs 1.3 MB) | upfront **8–16× SLOWER** (4.45 s vs 0.55 s) | **per-call (Stage 3)** | upfront via `upfront_proof=true` |

The per-line cost (`us/line`) is the DB-tax signature: Regular upfront 6.8–16 vs
legacy 3.2–5; MDD upfront 2.5–2.8 vs 2.6–3.5; Knapsack upfront **38–68** vs
3.7–4.4; BinPacking upfront **60–79** vs 24–30. The decomposition matched
measurement at every point:

| instance | displacement (line ratio) | DB-tax (us/line ratio) | predicted | measured |
|---|---|---|---|---|
| Knapsack i1 | 2.8× | 10.1× | 3.6× slower | **3.6×** |
| Knapsack i2 | 1.7× | 15.4× | 9.1× slower | **9.1×** |
| Knapsack i4 | 0.9× | 15.5× | 18× slower | **18×** |
| Regular 771 | 13.2× | 2.1× | 6.2× faster | **6.2×** |
| Regular 7660 | 26.9× | 3.9× | 7.0× faster | **7.0×** |
| MDD n12 | 4.2× | 0.8× | 5.2× faster | **5.2×** |
| BinPacking bp_l | 3.2× | 2.5× | 8.1× slower | **8.1×** |
| BinPacking bp_xl | 3.6× | 2.6× | 9.4× slower | **9.4×** |

Why each lands where it does:

- **Regular / MDD — upfront wins both, and the advantage *grows* with search.**
  The per-call baseline re-runs a forward+backward DP sweep on *every*
  `propagate()` and emits `O(states² · |Σ|)` hint-free lines to kill each state
  — enormous repeated volume (displacement 4–27×). The automaton/MDD is
  *narrow*, so the permanent Top scaffold is tiny (`red` ≈ 28–48 flags) → DB-tax
  ≈ 1–2×. Displacement ≫ tax → wins size and time.
- **Knapsack — split: wins size, loses time.** `KnapsackLegacy` rebuilds the
  partial-sum DP proof at `Temporary` each call — verbose, but only ~2–3× more
  lines than upfront (modest displacement). The upfront scaffold is a
  *k-dimensional* partial-sum DAG with phantom nodes — huge and permanent (`red`
  ≈ 11k–33k at root; ≈ 60% of upfront's lines). DB-tax ≈ 10–15× ≫ displacement
  (2–3×) → the proof shrinks in bytes but verifies 3.6–18× slower. So the
  default is **per-call**; `KnapsackUpfront` remains as the opt-in when byte size
  is the priority.
- **BinPacking — per-call wins both.** Stage 3 is *already* an upfront-flag
  design (`bpup/bpdn/bpat` reifications emitted once at Top, all pruning via
  *hinted* `JustifyUsingRUP` — **zero** manual `emit_rup_proof_line`). There is
  nothing per-call left to displace (displacement < 1). The upfront twin only
  *adds* 27 more Top lines (forward/backward chains, layer ALOs, per-state
  implications, phantoms) → a bigger permanent DB (`red` 2k–8k, DB-tax ≈ 2.5×)
  taxing every enumeration RUP. Both factors align against it → bigger *and*
  slower. Default **per-call**, `upfront_proof=true` the opt-in.

### Note on the MDD per-call opt-in

MDD defaults to upfront but does *not* currently ship a per-call twin, unlike
the other three. The per-call MDD strategy lives in the `#205` `mdd-propagator`
branch; resurrecting it as a runtime opt-in would cost ~150 LOC re-instating the
per-`(parent, val)` machinery for a strategy that is *strictly worse* on both
axes for MDD (7–9× larger, 4–5× slower). It was therefore deferred rather than
carried. If MDD ever needs the per-call path back, take it from `#205`.

## The predictive rule (apply before implementing)

> **Upfront pays off when the per-call baseline emits heavy per-`(state, val)`
> DP/chain intermediates on every call AND the diagram is narrow (small
> scaffold).** It **backfires** when either (a) the per-call path is already
> near-empty — it relies on hinted RUP + natural OPB + reified flags with no
> manual per-call emission (BinPacking Stage 3), so there is nothing to displace;
> or (b) the scaffold is wide/dense (Knapsack's k-dimensional partial-sum DAG),
> so the permanent DB-tax swamps the modest displacement.

Concretely: estimate *displacement* from the per-call baseline's per-call line
count, estimate *DB-tax* from the Top scaffold's line count, and compare. Narrow
diagram + verbose per-call baseline (Regular, MDD) → upfront. Lean per-call
baseline (BinPacking) or wide scaffold (Knapsack) → per-call.

A caveat visible in the data: there is a **crossover at tiny search**. At only
tens of solutions the fixed root scaffold is not yet amortised, so upfront can be
marginally bigger/slower even for Regular; its advantage (or deficit) *grows*
with instance size. The verdicts above are for real-instance scale.

## Deletion and solver-side hinting (both probed, both negative for the tax)

Two ways to attack the DB-tax directly were probed; neither is a safe default,
and the reports (`~/claude/tmp/ddpr-deletion-probe/`) quantify why.

**(1) Deleting spent scaffolding is not a safe default.** After deriving the
scaffold, one could `delete_range` the parts no longer needed, shrinking the
standing DB. Probing a deletion ladder (delete forward chains F / F+implications
/ F+I+backward chains / …) showed that **only the forward chains are ever a
deletion candidate** — deleting per-state implications, layer ALOs or backward
chains makes a search-time dead-state `~S ≥ 1` RUP fail to close (they are cited
at search time, not mere mid-ladder intermediates). And even forward-chain
deletion is **not unconditionally safe**: it verified for BinPacking k=1
(−16% verify) and Knapsack k=2 (−2–3%), but **deterministically breaks a
Knapsack k≥3 case** (`[[4,1,2,3],[4,6,3,8],[5,3,1,6]]`) — VeriPB RUP is
unit-propagation-only, and forward chains, though logically redundant, provide UP
*shortcuts* that some dead-state RUPs depend on. Whether deletion changes
*whether the proof verifies* (not just how fast) is instance/structure-dependent
and **not statically decidable**. At most this is an opt-in
`delete-forward-chains` flag, mandatorily gated on re-running that propagator's
proof-test suite — not a default, and worth ~0 for the narrow MDD/Regular case
which has no F layer at all.

**(2) Solver-side RUP hinting is feasible and sound, but flat hints do not reach
the ceiling.** The DB-tax is paid almost entirely by the propagator's *own*
hint-free `~S` RUPs: a line-count split shows propagator hint-free RUPs pay
**96–99.5%** of the standing-diagram tax, with VeriPB enumeration `solx`
collateral only **0.5–4%**. Hinting those `~S` RUPs is the high-value,
universally-safe lever (zero soundness risk, no VeriPB feature needed — the
known 2–18× RUP-hint speedup). But the #497 prototype found that **flat hints
reach only ~14% of the elaboration ceiling**: a minimal flat hint set is too
sparse, while a complete superset is *fat* — it hits the veripb parse bound and
inflates the proof ~5.7×, and neither flips any verdict here. Reaching the
ceiling without that I/O overhead is exactly what a **VeriPB "constraint-groups"
feature** (a group tag on scaffold lines + a per-group index the checker can
restrict RUP to) would buy. Note, though, that a groups feature would *only*
target the 0.5–4% enumeration slice on this DD family — it is **not** justified
by these constraints alone; the case for it is the general one, and the
dominant cost here is better attacked by hinting the propagator's own RUPs
(#497).

## Summary

- Narrow diagram + verbose per-call baseline → **upfront default** (Regular #213,
  MDD #211).
- Lean per-call baseline (already hint-driven) or wide/dense scaffold →
  **per-call default** (BinPacking #212, Knapsack #210), with the upfront twin
  kept as an opt-in for the size-critical case.
- Proof *size* and verification *time* are different questions; decide on time
  unless bytes are the constraint.
- Scaffold deletion is not a safe default; hinting the propagator's own
  per-call `~S` RUPs (#497) is the safe, high-value lever on the DB-tax.
