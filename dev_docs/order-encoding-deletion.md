# Order-encoding deletion via consolidate-then-delete branching

**Status: implemented behind a flag (`GCS_DELETE_ORDER_ENCODING=literals`),
measured on synthetic AND real instances; suite-safe; committed on this branch;
not default.** This note records the design for shrinking the integer
order-encoding that VeriPB carries, plus the measured outcome and what is and
isn't yet done. The full Brancher-API refactor (step 2, below) is a **decided design,
recorded in [brancher-design.md](brancher-design.md), now partly implemented**: its
stages A, B, B', B'' and C have landed, D/E have not. That note, not this one, is the
authority on the refactor's staging and status. The shipped deletion path still wires
into the existing branch/backtrack flow via hoisting, and the four-step sketch further
down this note is superseded by the decided design (see the note at "Design overview"
and at "Implementation staging").

## Results (measured)

All numbers below were measured on the development VM (KVM guest, AMD Ryzen 9
9950X3D, 32 vCPUs, 30 GB RAM, `veripb` 3.0.2): each timed run pinned to one core
with `taskset` and ASLR off via `setarch -R`, all timed proof I/O on the `/tmp`
tmpfs, every verify run **solo** on an otherwise idle machine, and each figure the
**minimum of three runs** (two above a minute, one for the multi-minute depth-point
rows). The guest exposes no `cpufreq` interface, so turbo cannot be pinned off;
taking a minimum rather than a mean is the compensation. Peak RSS via
`/usr/bin/time -v`. **The whole synthetic sweep was taken in one contiguous
sitting**, because this machine drifts by up to ~18 % between sittings on the
longest runs — see [benchmarking.md](benchmarking.md).

Every measured row cleared the gate: search statistics **IDENTICAL** OFF vs ON and
both proofs VeriPB-**VERIFIED**.

> **Superseded, twice.** The oldest hand-written table here (domain 100…4000,
> "~+89 % larger", ~60× at d4000) came from a *pre-commit* iteration of the
> `order_deletion_bench` driver and is not reproducible with the committed driver,
> whose `--problem linear` defaults root-refute in ≤3 recursions and produce no
> search signal. It was replaced by a campaign run on different hardware, which has
> in turn been replaced by the figures below, re-measured from scratch on the
> current machine. Only one set of numbers is kept, because absolute verify times do
> not transfer between machines and two sets invite comparing across them.

### Synthetic win curve (committed driver)

Exact invocation, `--domain` and `--window` swept together:

    order_deletion_bench --problem pairwise --size 8 --domain D --window D \
        --tightness 90 --unsat

(`pairwise` is the only mode that searches deeply on this build; `--window D`
disables the per-variable windows, `--tightness 90` sits just inside UNSAT so the
tree must be searched.) ON rows are `GCS_DELETE_ORDER_ENCODING=literals` at
`MIN_CHAIN=0` — the gate-off ceiling.

| D    | recursions | verify OFF | verify ON | speedup    | pbp OFF | pbp ON  | pbp growth |
|-----:|-----------:|-----------:|----------:|-----------:|--------:|--------:|-----------:|
| 250  |        393 | 0.335 s    | 0.067 s   | **5.04×**  | 1.13 MB | 2.32 MB | +105 %     |
| 500  |        919 | 1.669 s    | 0.171 s   | **9.79×**  | 2.59 MB | 5.74 MB | +121 %     |
| 1000 |      2 397 | 10.576 s   | 0.507 s   | **20.87×** | 6.34 MB | 15.3 MB | +141 %     |
| 2000 |      6 979 | 101.81 s   | 1.852 s   | **54.98×** | 17.1 MB | 44.9 MB | +163 %     |

The speedup **grows monotonically with domain**, at least doubling per domain
doubling. A depth point isolates search depth from domain: same domain 1000 but
`--tightness 95`, **72 341 recursions** (~30× deeper than the 2 397 at tightness 90),
gives **26.41×** (443.78 s → 16.81 s) — above the tightness-90 d1000 point, so deeper
search at the same domain also wins; the effect is not merely a domain artefact.

**The d2000 row is superlinear, and it is the least portable number here.** The
smaller rows double per domain doubling; d1000→d2000 gains 2.6×. The asymmetry is
entirely on the OFF side: relative to the older campaign hardware this machine runs
the ON verifies about 3× faster but the d2000 OFF verify under 2× faster, which is
what to expect when a large L3 keeps the ON run's working set resident while the OFF
run's much larger resident database misses to DRAM either way. That row is also the
one with real measurement noise — the same solo d2000 OFF verify came out at 128.5 s
in one sitting and 101.8-116.6 s in others, so its speedup moves between roughly 55×
and 68× depending on when it is taken, while every other row reproduces to a couple
of percent. Read it as "the curve keeps climbing", not as a constant, and see the
timing caveat in [benchmarking.md](benchmarking.md) before comparing any large-proof
verify across machines or across sittings.

ON proofs are **+105 %…+224 % larger** (the +224 % is the tightness-95 depth point)
yet verify far faster — the design's central claim confirmed: **resident chain
length, not proof line count, dominates VeriPB's cost.** The honest cost on the win
rows: solver-side proof-*writing* overhead is **+101 % at d1000 and +123 % at d2000**
(and +200 % on the depth point) — largest exactly where the verify win is largest, a
genuine trade rather than a free one. It stays a good trade in absolute terms: at
d2000 the solver pays 0.087 s → 0.194 s to save 100 s of verification.

**Peak `veripb` RSS falls, and the saving grows with domain** — the "resident
database is smaller" prediction confirmed directly, and more strongly than the
earlier campaign found:

| D | RSS OFF | RSS ON | change |
|--:|--:|--:|--:|
| 250  | 14.6 MB | 10.2 MB | −30 % |
| 500  | 21.6 MB | 12.3 MB | −43 % |
| 1000 | 39.6 MB | 20.7 MB | −48 % |
| 2000 | 73.4 MB | 31.9 MB | −57 % |
| 1000 @ t95 | 74.8 MB | 50.7 MB | −32 % |

The earlier campaign reported a smaller saving that **inverted** at d2000, on the
model that peak RSS = (the proof `veripb` must hold) + (the resident order database),
so a several-fold-larger ON proof would swamp the database saving. That model does
not hold here: at d2000 the ON proof is 44.9 MB but ON peak RSS is 31.9 MB, and at
the depth point the ON proof is 373 MB against 50.7 MB of RSS. `veripb` **streams**
the proof rather than holding it, so RSS tracks the resident constraint database
alone — which is exactly the quantity this mode shrinks, and why the saving grows
with domain instead of inverting.

The likely cause of the change is upstream, not in this feature: VeriPB dropped
mmapped proof input in favour of streaming (`59d948fb "Remove mmap"`, merged
2026-05-28). Under mmap the proof file counts toward RSS, which is exactly the term
the old model assumed; streaming removes it. Both campaigns report version 3.0.2 —
the string did not change across that commit — so **the version number is not enough
to tell the two behaviours apart**. If an RSS figure ever has to be compared against
an older one, check the `veripb` build date against 2026-05-28 first.

### Real instances — the win did NOT generalise

On **no reachable real instance** did the synthetic win materialise. The rows below
were re-measured on the current machine; each was checked search-identical (node and
propagation counts equal OFF vs ON) and VeriPB-VERIFIED in every mode.

- **seat-moving 2018** (`2018/seat-moving/sm-10-12-00.dzn`, flattened and run under
  `fzn-glasgow -n 1`) — the one deep-yet-verifiable real split case: 15 610-node
  find-first, `indomain_split`, maxdom 901. **Neutral.**

  | mode | verify | vs OFF | pbp | `del` lines |
  |---|--:|--:|--:|--:|
  | OFF          | 126.17 s | —          | 629.4 MB | 931 708 |
  | gate 0       | 119.52 s | **1.06×**  | 643.8 MB (+2.3 %) | 938 632 |
  | gate 16      | 121.24 s | **1.04×**  | 639.3 MB (+1.6 %) | 935 062 |
  | gate 64      | 120.55 s | **1.05×**  | 636.2 MB (+1.1 %) | 935 295 |

  A few percent either way is inside what an unpinnable-turbo VM can resolve, so read
  this as neutral rather than as a small win. The del-count proxy says why: ON emits
  only **+0.7 %** more `del` lines even at the aggressive gate — deletion barely
  fires. Not because the model lacks long chains (it has maxdom-901 split variables)
  but because it is reif/element/view-heavy and its order encoding is **pinned
  resident by design** (viewed variables held by the always-at-Top view bridges,
  product/aux magnitudes by the product-justification caches — the "delete only when
  unreferenced" rule).

- **Expected-bad, confirmed and bounded.** The two eq-enumeration examples:

  | instance | OFF verify | gate 0 | pbp growth, gate 0 / 16 / 32 / 64 |
  |---|--:|--:|---|
  | `crystal_maze` | 0.0306 s | 0.0322 s (**0.95×**) | +48.5 % / **0 %** / 0 % / 0 % |
  | `talent`       | 1.2649 s | 1.3197 s (**0.96×**) | +35.8 % / +5.8 % / +1.6 % / **0 %** |

  The `0 %` entries are not rounding: the proof is **byte-identical to `None`**
  (checked by digest), which is the strongest strictly-no-harm form. crystal_maze
  reaches it already at the shipped gate of 16 because its longest chain is 16;
  talent needs 64. So the downside on eq/small-domain models is a low-single-digit
  verify slowdown and +35–50 % proof size **at gate 0 only**, and the shipped gate
  removes most of it.

- **Not re-measured on this machine**, and carried over as qualitative findings only:
  mrcpsp 2023 and the `tour` circuit example (both recorded as exact no-ops — eq
  branching has no split frontier to advance, so nothing is deletable), sudoku_fixed
  (split but maxdom 16, del delta 0), and the scp `divide_sat` control (no win, no
  harm — the divide/modulus in-proof aux magnitudes stay resident by design). A
  find-first mrcpsp run under `--prove` here wrote **over 12 GB of proof** without
  finishing, so whatever bounded configuration produced the original 1 540-`del` row
  was not recorded and could not be reconstructed; treat mrcpsp as outside the
  verifiable set until someone pins down an instance and budget that lands.

- **Hunt for a tractable real win — none exists in the reachable set.** Screened
  radiation (2012/2013), on-call-rostering (2013/2018) and mspsp on top of the scoping
  set. Real challenge instances are either **shallow find-first**
  (static-encoding-dominated → neutral) or **intractably deep**: radiation *does*
  search deeply on proven optimality, but the smallest case (m06) blew past **3.98 GB
  of proof before completion**, far outside any verify budget. seat-moving stands as
  the lone deep-yet-verifiable real case, and it is neutral.

**Correctness gate (the whole point of a proof-only change):** every measured row was
search-**identical** OFF vs ON, both modes **VERIFIED** with identical
bounds/solution counts. No ON-only failure, no divergence anywhere.

### Pin apportionment (step 1b, measured) — the real reason the win does not generalise

The campaign's provisional read — that the view/product resident-by-design classes
block the real-instance win, motivating the bridge-lifetime redesign (step 3) — is
**overturned by measurement**. The `GCS_ORDER_ENCODING_STATS` diagnostic (below)
attributes every resident `ge` to the site that pinned it, first-cause-wins;
attribution is exact (recorded at the deciding call site, never inferred). Campaign
dumps in `real-instance-bench/apportionment/` (see Provenance).

On **seat-moving** (the lone deep-yet-verifiable real case), of 4 697 proof-time ge
atoms, 4 442 end Top-resident at gate 0:

- **view_pin + aux_pin (what step 3 would free): 0 — 0.0 %.** No view-underlying or
  aux-magnitude variable has *any* tracked ge. The same was true on mrcpsp and talent
  when those were measured. (The attribution mechanism itself is validated: a
  view-wrapped comparison test shows view_pin up to 84.6 %, and scp divide_sat shows
  aux_pin > 0.)
- eq_hoist: 1 962 (44.2 %); structural (model_time 1 858 + boundary 622): 55.8 %.
- Churn: **37 644 deletions but 37 616 reintroductions — net 28**. Split branching
  constantly re-touches deleted thresholds; deletion does enormous work for zero net
  shrinkage. This churn *is* the +2.3 % proof and the solver-side overhead. At the
  shipped gate of 16 the churn drops to **20 784 deletions** and 45.5 % of the
  Top-resident encoding is held by the gate itself — still churning, still for
  nothing, which is what stage C (#609) exists to fix.

And the deeper cause, measured directly from the proof (distinct `ge` thresholds
ever named, per variable): seat-moving's chains are **tiny** — median 12, p99 13,
max 98 (the objective), across 497 variables — despite maxdom 901. Strong
propagation means search never names more than ~a dozen thresholds per variable, so
**the long resident chains that dominate synthetic VeriPB cost never form on
propagation-strong real models at all**. Domain size is not chain length. No
deletion scheme of any kind — step 3, eq-unpinning, anything — can win where there
is nothing long to shorten; the win regime is characterised as *weak-propagation,
large-domain, bound-split search* (the synthetic driver's regime).

Consequences: **step 3 is deprioritised** (it frees 0 % on every real instance
measured; its win-recovery motivation is gone). A cheap, attractive follow-up
instead: a **chain-length gate** on deletion — only track/delete a variable's order
literals once its live chain exceeds some threshold (~tens) — which would eliminate
the real-model churn/overhead entirely (making the feature strictly-no-harm) while
preserving the full large-domain win, and might eventually justify default-on.

The diagnostic: set `GCS_ORDER_ENCODING_STATS` (any non-empty value) under
`GCS_DELETE_ORDER_ENCODING=literals`; a `%% oed-stats:` summary is printed to
stderr at proof end. Collection is gated on the mode + env var and emits no proof
bytes (verified byte-identical in all mode × env combinations).

### Baseline (non-feature) finding recorded in passing

mzn-challenge `2023/unit-commitment` is **REJECTED by veripb at `pbp:882`** ("not
implied by reverse unit propagation") — but in **both** OFF and ON modes
identically. It is a **pre-existing frontend/model proof-logging bug, out of this
feature's scope**, not a deletion regression, and was excluded from the campaign.
Flatten `mzn-challenge/2023/unit-commitment` to reproduce it (a repro `.fzn` is also
kept under `real-instance-bench/fzn/`), and flag it to whoever owns the MiniZinc
frontend proofs.

## Implementation status

- **Done, suite-safe:** the full caps-off test suite passes with the flag on (0
  flag-induced VeriPB rejections; mode-off byte-identical; flag-off 537/537). The
  hoist primitive, guess/eq/partition-atom hoisting, and the aux/view dispositions
  below are all in `gcs/innards/proofs/{names_and_ids_tracker,proof_logger,proof_model}.*`.
- **A line must never name a literal whose definition has been deleted — and that is now
  structural, not a discipline.** Deletion makes a `ge` atom's *definition* transient, so
  "the atom exists" does not imply "a line may name it". Rather than requiring every
  naming path to remember to consult a liveness check, deletion **retires the atom**: the
  sweep in `forget_order_literals_at_level` moves the `XLiteral` out of `VariableAtoms::ge`
  into `VariableAtoms::retired_ge`, so `find_condition` stops answering for it. The only
  route back to the literal is `need_gevar`, which re-introduces the definition and takes
  the retired `XLiteral` back — so the atom keeps its identity and its PB name across
  delete/re-introduce cycles. Anything that tries to render it without going through
  `need_gevar` now hits the const `xliteral_for`, which **throws** rather than silently
  emitting a stale name: a bypass fails loudly at emission instead of becoming a VeriPB
  rejection hundreds of lines downstream.

  Why it is written this way. The `proof-writing-perf` stack fused name introduction into
  line rendering (`834b7029`), and its `xliteral_for_ensuring` introduces a name **only
  when the atom is missing** — correct for every other mode. When the atom stayed put and
  only its definition was deleted, that check passed and re-introduction never fired:
  rebasing onto the stack turned 0 flag-induced rejections into **37** across the caps-off
  suite, every one a line naming a `ge` whose definition had gone, with the re-introduction
  appearing a few lines *later*, triggered by whatever next needed the atom. Retiring the
  atom makes "missing" true exactly when it should be, so the renderer's own check is the
  enforcement and no mode-specific special case is needed.

  Two traps worth carrying forward:

  - `ge_defs` keeps its entry when a threshold is retired, and the re-introduction must
    **`insert_or_assign`, not `try_emplace`**. The stale entry holds the deleted
    definition's line numbers, and every chain `pol` resolves its operands through them
    (`need_pol_item_defining_literal`), so `try_emplace` leaves the links pointing at
    deleted lines. That entry is deliberately never erased: it keeps `ge_defs` monotone,
    which is what makes it a sound basis for the chain gate's "thresholds ever named"
    count.
  - There is no longer an aliased-`ge` exception. Issue #554's fix deliberately stopped
    aliasing a DirectOnly `{0,1}` variable's `>= 1` atom to its bit, so every `ge` owns its
    own reification and `order_literal_aliased_to_bit` — which existed only to keep such a
    literal out of the re-introduction path — became dead and has been removed.
- **Eviction: taking a definition out on demand, rather than waiting for a backtrack.**
  Stage B' of the Brancher work ([brancher-design.md](brancher-design.md)) adds the mirror
  of the hoist primitive — `NamesAndIDsTracker::evict_order_literal` — together with the
  bookkeeping it needs, all **always-on under Literals** and all inert until something
  calls it (nothing in the solver does yet; its consumers are the eq-atom window and the
  objective-improvement `delc`). Three parts are worth knowing about even outside that
  work:

  - **`ge_top_pins`**, a per-threshold per-cause refcount of the *permanent* references
    holding a `ge` at Top, which is what makes "may I delete this?" answerable. It is
    counted **at the reference sites** rather than inside the hoist (which early-returns
    for a threshold already at Top, so the second of two permanent atoms naming one `ge`
    would be invisible — and `eq(v)` and `eq(v+1)` both name `ge(v+1)`), and **only for
    thresholds a hoist put at Top**, so "level 0 with no entry" reads as structurally
    resident and unevictable. `stats_ge_top_cause` remains the diagnostic's separate
    first-cause-wins map.
  - **`chain_clauses_by_level`**, the chain clauses currently present in the proof,
    bucketed by proof level and then by variable. Nothing recorded these before, because
    forgetting a level deleted them wholesale; eviction has to delete just the ones naming
    one threshold. Recording is on the hot path of every chain emission, which is why the
    shape is level-first and flat — see the stage-B' notes for the +12 % that keying it by
    threshold pair cost, and the +4.1 % this one costs.
  - **The eq analogue of atom retirement** (`VariableAtoms::retired_eq`,
    `forget_eq_literals_at_level`), so a *deletable* eq definition — which only a windowed
    variable has — retires its atom on backtrack and is re-introduced through
    `need_direct_encoding_for` with its identity intact. Both ge traps recur verbatim:
    `eq_defs` keeps its entry and re-introduction must `insert_or_assign`, and the
    `XLiteral` must be reused rather than re-minted.

  **A finding worth carrying forward: VeriPB does not police a leaked chain clause.** A
  chain clause left naming an evicted threshold stays a valid derived constraint, and
  re-introducing that threshold's definition verifies with the stale clause still in the
  database (measured by mutation against veripb 3.0.2 — the negated half of the
  reification forces the neighbour's atom through its own definition, so the leftover
  clause is implied under the witness). A missed deletion is therefore silent and costs
  precisely the resident-database shrinkage this whole mode exists for, which is why
  `chain_clauses_naming` exists and why `gcs/innards/proofs/order_evict_test.cc` asserts
  it in C++ rather than trusting the checker. This is the same lesson as the two
  solver-side invariants the design already records: **VeriPB polices the order encoding
  only at a point of use.**
- **Gate — randomized-test seed sweeps are part of the flag-ON gate.** A single caps-off
  suite run exercises only *one* random seed per data-driven test, and the fixed corpus
  missed a ~10 %-of-seeds VeriPB-rejection hole in divide/modulus (seed 3072268882 was one
  such seed). So any change to the deletion machinery, and any new resident/hoist
  disposition, must additionally clear a **seed sweep** of the affected randomized tests:
  ~200 fixed seeds, flag-ON at `GCS_DELETE_ORDER_ENCODING_MIN_CHAIN=0` (the gate-off,
  aggressive-testing mode — a nonzero gate hides short-chain shapes), each run isolated in
  its own working directory, **zero** rejections required. Report the before/after failure
  counts. (Sweep harness + results under `divide-modulus-seed-bug/`.)
- **Kept resident (not deletable), per the "delete only when unreferenced" rule,
  because their `ge`s are named by *permanent* Top constraints:**
  - divide/modulus in-proof-bit **aux-magnitude** variables (`register_state_variable_bits_in_proof`)
    — pinned by the product-justification caches;
  - the **real operands** of the magnitude-product constraints — divide/modulus `x, y, out`
    and multiply/power `x, y, z` (marked in `install_divide_modulus` and in
    `signed_multiply::make_data`, which multiply and power both route through) — pinned by
    the permanent identity / remainder / magnitude-channel / **sign-clause** rows
    (`product_encoding.cc`) and the `pol`/`rup` product reasons derived over them, all of
    which name these operands' order/eq literals (e.g. an `emit_sign_clauses` row naming
    `v >= 0` / `v < 1`, or a `mult_bc` reason naming `31 i[out][ge1]`). Without this an
    interior operand `ge` is born deletable, a backtrack deletes it while a pinning row
    stays live, a later reference **re-introduces** it, and the re-introduction's
    falsify-witness `ge := 0` collides with the pin — VeriPB rejects the proofgoal. (This
    was the divide/modulus seed-3072268882 bug: a ~10 %-of-random-seeds hole the fixed test
    corpus missed. Multiply/power share the identical pin mechanism; the fix is applied to
    them as a latent-bug closure — see the seed-sweep note under Gates.);
  - **viewed** variables (underlying of a registered view) — pinned by the
    always-at-Top view-bridge `pol`s in `need_gevar`.
  These get no deletion win, but are correct. **This narrows the win scope: any variable
  appearing as an operand of a divide/modulus/multiply/power constraint is now wholly
  resident, so it contributes no chain-shrinkage win** (its long chains, if any, are
  recoverable only by the parked bridge-lifetime redesign — Future work). In the win regime
  (weak-propagation, large-domain, bound-split) such variables are typically not the
  split-branched ones anyway.
- **`soli` objective atom** is hoisted to Top when the objective-improvement
  constraint is emitted (latent optimisation-mode bug fixed defensively).
- **The eq-atom sliding window (stage B'', opt-in and OFF by default).** The four
  contiguous eq value orders — `smallest_first`, `largest_first`, `smallest_in`,
  `largest_in` — used to keep every eq atom they branched on, *and* both of the `ge`
  thresholds each names, resident at Top forever: O(domain width) per branched variable,
  and no deletion win at all. Under
  `ProofOptions::set_order_encoding_deletion_eq_window()` (or
  `GCS_DELETE_ORDER_ENCODING_EQ_WINDOW=1`) the branch layer instead mints each guess's eq
  definition **deletable, at the node's own level**, advances a monotone frontier past it
  once the sibling is refuted, and evicts the atom and the threshold it stepped over
  behind that frontier — O(1) resident.
  [brancher-design.md](brancher-design.md) ("The eq-atom window") is the authority; the
  three things worth knowing here are:

  - **The advance RUPs *through* the eq atom's reverse reification**, which fixes the
    order of the per-iteration tidy: the definition must not be deleted before the
    advance is emitted. This is not a guess — the artifacts driver's D2c control deletes
    it early and VeriPB rejects.
  - **The atom's definition is minted before the descent, not by the child's
    propagation**, so it lands at the level the child's backtrack clause and the
    frontier advance both live at. Left to the child it would land a level deeper and
    the child's own `forget` would delete it out from under both.
  - **Permanent references are detected at the reference site**
    (`note_permanent_eq_reference`) and retain the atom rather than evicting it. There is
    exactly one such site plus the interval guard — a learned nogood's Top clause. A
    `solx`/`soli` line names `var == val` too, but is **not** one: the constraint VeriPB
    keeps is built from the `preserved:` set alone (our variables' bits), so those atoms
    are consumed while the line is checked and referenced by nothing afterwards.
    The list of sites is enumerated rather than general, which is acceptable only because
    getting it wrong is loud: the atom keeps its `XLiteral` across eviction, so a
    surviving line naming it collides with the re-introduction's `red` witness and VeriPB
    rejects.

  **Measured** (figures and method in [brancher-design.md](brancher-design.md), "What it
  measures"): on ascending eq branching over a wide domain the window verifies **2.3× /
  3.5× / 4.7× faster at domain 250 / 500 / 1000**, a speedup that grows with width — and
  it does so while making the proof **31 % bigger**, which is this mode's SIZE≠TIME point
  in its purest form.

  On the eq-heavy *real* instances it does not engage: talent windows **0** eq atoms and
  crystal_maze **2**, against 3255 on the synthetic. The precondition the design did not
  name is that **the window can only act on an eq atom the branch layer names first**, and
  on a model whose constraints reason per value the propagators have defined those atoms
  permanently long before the search reaches them. Where it cannot engage it now costs
  nothing (talent's window-on proof is byte-identical to its window-off proof). The window
  therefore ships off, and stage E owns whether the default changes.
- **The frontier deletion exemption (stage C).** `ProofModel::minimise` marks the objective
  `note_deletion_exempt`, so under Literals its whole `ge` encoding stays resident however
  long its chain grows. Branch-and-bound re-tightens the objective at every improving
  solution and every backtrack relaxes it again, so without this its thresholds are deleted
  and re-introduced forever, verify-neutrally, for zero shrinkage — on seat-moving 2018
  essentially all of the residual churn at the default gate. The chain gate cannot suppress
  it: the gate measures *length*, and the objective's chain is long for a churn reason
  rather than a win reason. This is a **policy** hook, not a correctness one — nothing is
  stranded without it — and it deliberately applies to the objective only, because
  exempting a bound-branched variable would defeat the split win, which *is* deleting its
  stepped-over chain.
- **In progress:** the clean Brancher abstraction (step 2). Stages A, B, B', B'' and C have
  landed — the `BranchDecision` / `BacktrackAdvance` types, the split families' bound
  advances, the eviction primitives plus their always-on residency bookkeeping, and the
  eq-atom window — so the direct guess/eq/aux hoist wiring is on its way out but is still
  what the shipped path uses. Stages C/D/E remain;
  [brancher-design.md](brancher-design.md) is the authority on each. Also future:
  short-reason flag / deview-companion level-scoping (currently inert), and the bridge
  redesign (deprioritised — step 1b measured it as freeing 0 %).

## Next steps (prioritised)

**1. Real-instance benchmarking — DONE.** Completed as the phase-2 campaign, and
re-measured from scratch on the current machine (see Results above). Verdict:
- The **synthetic mechanism is validated**, **5.0×→55× across domain d250→d2000**
  (and 26× at the depth point), driven by resident-chain shrinkage — the design's
  central claim holds.
- The **real-instance win is unproven**: no reachable real instance triggered it. The
  one deep-yet-verifiable real case (seat-moving) is neutral because its chains are
  pinned resident by view/reif bridges, and the tractable-real-win hunt found nothing
  (real instances are either shallow-neutral or intractably deep).
- The **downside is bounded**: a few-percent verify slowdown and +20–50 % proof size
  on eq/small-domain models, and roughly a doubling of solver-side proof-writing on
  the win rows.
- **Correctness is clean** (every row search-identical OFF vs ON, both VERIFIED).
- **Conclusion: keep the feature flag-gated; default-on is NOT justified by these
  numbers** (real win unproven, measurable overhead on eq/value-heavy models) — but
  the mechanism is sound and correctness is solid.
- The verification-only drivers `order_jump_check.cc` / `order_hoist_check.cc` are
  still uncommitted, in the artifacts directory (see Provenance). Stage E owns
  promoting them to proper `gcs/` tests — they regression-check the two verified
  foundations this whole design rests on, and until they are in-tree they survive only
  by luck.

**1b. Pin-apportionment instrumentation — DONE.** Implemented as the
`GCS_ORDER_ENCODING_STATS` diagnostic and measured (see "Pin apportionment" above).
The answer: **step 3 would free 0 % of the resident encoding on every real instance
measured**; the win is absent on real models because propagation-strong search never
builds long chains (seat-moving: median chain 12, max 98, despite maxdom 901), and
the deletion machinery churns (37 644 deletes / 37 616 reintroductions, net 28) for
nothing there.

**2. Brancher-API refactor — IN PROGRESS: stages A, B, B', B'' and C landed; D is next.**
The concrete, decided step-2 design and its staging live in
[brancher-design.md](brancher-design.md), which is the authority on what is done and
what each remaining stage owes. In summary: **A** added the `BranchDecision` /
`BacktrackAdvance` types and ported every value order (byte-identical); **B** wired the
split families' bound advances and the advance-RUP-driven deletion; **B'** added the
always-on residency bookkeeping and the evict/hoist primitives the eq window and the
objective `delc` both need (behaviour-neutral); **B''** built the eq-atom window on
them, opt-in and off by default; **C** exempted the objective from deletion. Remaining:
**D** the objective-improvement `delc` + Top-eviction, **E** benchmark and cleanup —
including whether the window becomes the default for `smallest_first`. The design
generalises consolidate-then-delete,
tidies the current direct wiring, and is the natural home for the chain-gated
deletion policy, the objective-variable exemption (from 2b, below), and the
objective-improvement `delc` lifecycle. Five owner decisions are settled there:
the per-node object stays a `std::generator` (not a virtual class) until it shows
as a benchmark hotspot; the pre-0.1 public yield-type source break is accepted
(the implicit `IntegerVariableCondition → BranchDecision` conversion is the
bridge); the objective is handled by exemption for its ges *and* an unconditional
delete-all-but-the-most-recent improvement constraint; the value-order mapping is
final; and the eq-atom window ships default-off pending a stage-E measurement.

Crucially, the design adds an **eq-atom sliding window** (validated 8/8 in VeriPB
3.0.2) that moves the four contiguous in-order/eq value orders —
`smallest_first`, `largest_first`, `smallest_in`, `largest_in` — into the win
regime as *O(1)-resident* (evict each eq/ge once the frontier steps past it),
**superseding this note's earlier claim that only split wins**: split still wins
by the bound *jump*, but ascending/descending eq now wins too, by the window.

**2b. Chain-length-gated deletion — DONE (implemented + measured; default gate 16).**

Under `OrderEncodingDeletion::Literals`, a real variable's interior (non-boundary)
`ge` definition is only emitted deletable-at-`Current` once the variable has crossed
a chain-length gate: when the number of `ge` thresholds ever named for it (its
`ge_defs` count for it at decision time in `need_gevar`, taken before this threshold is
inserted — model-time atoms
included) exceeds `min_chain`. At or below the gate the def stays resident at `Top`,
exactly like the boundary / view-pin / aux-pin paths. The gate is monotone (the
count only grows; once crossed, stays crossed; below-gate residents are never
revisited) — no flapping.

Parameter: `ProofOptions::order_encoding_deletion_min_chain` (+ fluent setter), env
override `GCS_DELETE_ORDER_ENCODING_MIN_CHAIN` (explicit-in-code wins). **`0` = gate
off = byte-identical to the pre-gate Literals behaviour — the aggressive-testing
mode: regression runs exercising the deletion machinery MUST set `MIN_CHAIN=0`,
because tiny test domains never cross a nonzero gate.** A variable with a live eq
window is exempt from the gate entirely (the `WindowedFrontier` slot): it is a frontier
variable by construction, and holding its thresholds resident would collapse the window
back to the baseline. The suite passed caps-off
flag-ON at gate 0 and at 32 when this landed (525/525 each, 0 flag-induced failures; the
suite has grown since — the standing gate is "all of it, in each of the three modes",
not a fixed number). The stats dump
gains a `gate-held` cause and a per-variable chain-length distribution.

**Default 16, chosen from measurement** (the original full tables are in
`chain-gate/gate-measurement.md`; the figures below are re-measured):

Synthetic columns are verify speedup vs OFF; real columns are proof growth vs OFF and
the extra `del` lines the mode emits (0 = byte-identical to `None`). Dashes are
combinations not measured.

| min_chain | pairwise d250 | d1000 | crystal_maze | talent | seat-moving |
|--:|--:|--:|--|--|--|
| 0 | 5.04× | 20.87× | +48.5 % / 344 | +35.8 % | +2.3 % / 6 924 |
| **16** | **3.19×** | **13.24×** | **+0.0 % / 0 (byte-identical to None)** | +5.8 % | +1.6 % / 3 354 |
| 32 | 2.40× | 9.59× | +0.0 % / 0 | +1.6 % | — |
| 64 | 1.64× | 6.31× | +0.0 % / 0 | **+0.0 % / 0** | +1.1 % / 3 587 |
| 128 | 1.05× | 3.71× | — | — | — |

Search identical OFF vs ON at every gate; every proof VERIFIED. An infinite gate
reproduces the mode-None proof **byte-for-byte** (measured two anchors) — the
strongest strictly-no-harm form; crystal_maze reaches that already at gate 16 (its
longest chain is 16). The synthetic-win tables in Results above are the gate-off
(`MIN_CHAIN=0`) ceiling.

Two measured caveats, stated plainly:
- **Stitch explosion (proof-size only).** Under split branching the first ~L
  thresholds are named in binary-split order, so resident anchors are spread and
  fragment each deleted run into per-sub-run stitches. Proof size is therefore
  **non-monotone in L**: at d1000 the gate-16 proof (15.54 MB) and the gate-32 proof
  (15.38 MB) are both *larger* than the un-gated 15.27 MB, before falling to 13.75 MB
  at 64 and 12.73 MB at 128. **Verify time — the target — erodes cleanly** across the
  whole range, so the gate is chosen from the verify curve, not from size. See
  `chain-gate/stitch-explosion.md`.
- **A single long chain defeats the flat gate.** seat-moving's residual churn
  (20 784 delete/reintroduce at gate 16) is concentrated on its objective (chain
  98) and cost (76) variables, which any win-preserving gate leaves deletable. That
  churn is verify-neutral (OFF 126.2 s ≈ L16 121.2 s ≈ L64 120.6 s, all VERIFIED)
  and costs only +1.6 % proof. Follow-up recorded for step 2: a
  **targeted objective-variable exemption** (never delete, or gate separately, the
  bound-tightened objective) would remove most remaining real-model churn at zero
  win cost — it belongs where the backtrack-constraint owner knows the bound
  frontier, not in the flat gate.

**3. Bridge-lifetime redesign — DEPRIORITISED.** Making viewed and divide/modulus
aux magnitudes deletable frees 0 % on every real instance measured (step 1b); its
win-recovery motivation is gone. Revisit only if a view/product-heavy
*weak-propagation large-domain bound-split* workload appears — the only regime where
freed chains would be long enough to matter.

**Ordering decided (2026-07): 2b first (done, above), then step 2.** Step 2 is under
way — A, B and B' are in — and it inherits the objective-variable-exemption follow-up
from 2b as its stage C; 3 stays parked.

**Also:** decide productionisation (keep flag-gated vs default-on — current verdict:
flag-gated), and — cleanup — the superseded dormant `Links` mode can be removed.

## The problem

Every integer variable is proof-encoded with order literals `ge(v)` ("x >= v"),
each defined by a reification against the variable's bits, plus **chain-link**
constraints `ge(v+1) -> ge(v)` between adjacent thresholds (see
[variable-encodings.md](variable-encodings.md)). Under the current (pre-this-work)
scheme all of this is emitted at `ProofLevel::Top` and kept for the entire search —
nothing is ever removed — so a large-domain variable accumulates a chain of every
threshold any subtree ever touched. Changing exactly that is the point of this note;
the rest of the document is about *when and how* the encoding can instead be deleted.

The chain links are 2-literal clauses, which VeriPB propagates first (2WL,
clausal priority) on every RUP check. Touching one end of a 1000-long chain makes
VeriPB chase the whole thing, and the bit<->order reifications fire more long
sequences. So the cost is **chain length**, and the lever is to **stop keeping the
entire order encoding of a large-domain variable resident when the proof is only
operating over a narrow range locally.** The goal is reduced VeriPB verification
time; proof size is a secondary signal.

## Why the obvious approaches don't work

Recorded so future work doesn't re-walk these.

- **Delete only the chain links, keep the literals.** Fails. It *fragments* the
  chain, and VeriPB RUPs rely on the chain being contiguous over the existing
  literals, including for closure-only reasoning about variables not named in the
  step. A fragmented chain breaks those RUPs. (The Ch.3 property of McIlree's
  thesis: at any point every integer literal must unit-propagate all known facts
  about its variable. A hole in the chain violates it.)

- **Delete literals and re-introduce on demand.** Deleting a literal and stitching
  its two chain links into one skip-link *coarsens* the chain (complete, fewer
  thresholds) rather than fragmenting it, which is sound. But re-introducing a
  literal later — re-emitting its `red` reification — **fails VeriPB** once the
  surrounding context has moved on: a live constraint pins the atom, and the
  reification's falsify-witness (`ge(v) := 0`) contradicts the pin, so the
  redundancy sub-goal can't be auto-proven. The dominant pins are **backtrack
  clauses**, which name the search's guess (branch-threshold) literals, so this
  bites in *every* searching proof, eq-free or not. An experimental
  `OrderEncodingDeletion::Literals` mode on this branch demonstrates the failure
  (see Provenance); it should be reworked into the design below.

The lesson: never delete-then-reintroduce. Advance a **monotone** frontier and
delete behind it, and when a surviving constraint still needs a literal, **hoist**
it rather than deleting-and-recreating.

## The verified foundation: guess-reasoned bound jumps

*Verified against VeriPB.* When a variable X has a lower bound `X >= L` and the
values `L .. H-1` have been eliminated as holes (each elimination derivable from
the current guesses), the bound can be jumped over the holes with a single RUP
whose reason is **just the conjunction of guesses**:

    rup <guesses> (X >= H) >= 1

This checks because RUP does full unit propagation: it re-derives every hole
`X != v` from the guesses over the (permanent) base constraints, then climbs
`X>=L -> X>=L+1 -> ... -> X>=H` through the eq-atom reverse-reifications. You do
**not** need the per-value reasons, nor "all reasons over all other variables" —
the guesses entail them and RUP rediscovers them. This is the same monotonicity
the final backtrack clause already relies on.

Checked at wide gaps (L,H differing in up to all 6 bits, e.g. 3->60, 17->46, 5->26)
with two controls that must fail and do: dropping a needed guess is rejected, and
over-jumping by one value is rejected. Small gaps can RUP by bit-coincidence, so
the wide-gap controls are what make the positive result trustworthy. (See
`order_jump_check` in Provenance.)

Two consequences that shape the design:

1. The jump climbs through the intermediate eq/ge atoms, so they must be **live at
   emit time**; afterwards they are deletable. That pins the ordering: **emit the
   jump, then delete behind it.**
2. The jump is one `.pbp` line but VeriPB does O(H-L) propagation to check it. So a
   jump doesn't make *that* check cheaper — the win is that after deletion the
   *resident* database is smaller, so every *other* RUP's closure shrinks.

## Design overview: consolidate -> hoist -> delete

> **Historical sketch — superseded by [brancher-design.md](brancher-design.md).**
> The sections from here through "Implementation staging" are the original
> user-approved *conceptual* sketch; the concrete, decided step-2 design (grounded
> in the real code, with the five owner decisions and the eq-atom window folded in)
> is [brancher-design.md](brancher-design.md). In particular the "Mapping the
> existing heuristics" table below is **wrong** and superseded: its in-order/eq rows
> claimed `smallest_first`/`smallest_in`/`largest_first`/`largest_in` win by an
> "O(1) pin" bound-jump, but eq branching has no gap to jump and an eq atom pins
> both ges — those orders instead win via the **eq-atom window** (evict behind a
> one-step frontier), while the bound-*jump* win is the `split_*` family only. The
> foundation above this note ("The verified foundation: guess-reasoned bound jumps")
> stands. The prose below is kept for provenance; do not treat it as current.

A brancher maintains a compact **backtrack constraint** — the "what we'll use to
backtrack" fact, i.e. the weakest constraint it has proven must hold given every
sibling tried so far is refuted, under the current guesses. It tightens
monotonically as siblings fail. On each refutation the framework:

1. asks the brancher for the tightened backtrack constraint;
2. emits the guess-reasoned RUP that advances it (a bound jump, for the common
   case);
3. **hoists** the literals the new constraint names to the level where it lives;
4. **deletes** the encoding the advance stepped over that nothing else names.

Consolidate, hoist the frontier, delete the rest. Because the frontier is
monotone, we never delete-then-reintroduce.

## The backtrack constraint

Three kinds, declarative and extensible:

- **Bound** (`LowerBound(v)` / `UpperBound(v)`) — for split / ascending /
  descending value orders. Advanced by the bound-jump RUP; names **one** literal
  (the frontier). Maximally deletable.
- **ExcludedSet** — the generic fallback, accumulating `X != v`. This is exactly
  today's `~(all guesses)` behaviour. Correct, but names a growing set, so nothing
  is deleted for that variable. Used by genuinely unstructured orders.
- **Custom** — an escape hatch: the brancher supplies its own backtrack constraint
  plus a proof callback. For exotic branchers; not fleshed out until a use case
  appears.

## The Brancher abstraction

Replace the bare `BranchValueGenerator` (which yields a
`generator<IntegerVariableCondition>` and touches no proof state) with a small
stateful object that owns *both* the decision sequence and the backtrack
constraint:

    struct BranchDecision {
        IntegerVariableCondition guess;      // what to branch on
        BacktrackAdvance         on_refuted; // how the backtrack constraint tightens if this fails
    };
    // BacktrackAdvance = variant<LowerBound, UpperBound, Exclude, Custom>

    struct Brancher {
        virtual auto next(const CurrentState &, const Propagators &)
            -> std::optional<BranchDecision> = 0;
        virtual auto initial_backtrack_constraint(...) -> BacktrackConstraint = 0;
    };

`solve.cc` drives it: `next()` -> guess -> recurse -> on refutation apply
`on_refuted` (framework emits the advance RUP, hoists, deletes) -> repeat; when
`next()` returns `nullopt` the standing backtrack constraint is the node's
backtrack lemma, replacing the generic `~guesses`. A brancher that only ever emits
`Exclude` advances reproduces today's behaviour byte-for-byte.

Owning decisions and their proof consequence in one object is deliberate: it is
what lets a new brancher be written *correctly* without the caller having to keep a
separate "value order" and "consolidation strategy" mutually consistent.

## The hoist primitive

A general `ProofLogger` operation, foundational to the whole scheme:

    hoist_literal_to_level(lit, target_level)
    hoist_literal_to_top(lit)                 // = hoist to level 0, permanent

It is a **bookkeeping move**: it reassigns the literal's definition from its
current (deep) level bucket to a shallower one, so a later `forget` deletes it
later, or never. **It re-emits nothing.** That is precisely why it succeeds where
delete-then-reintroduce fails — there is no re-asserted reification and therefore
no witness to collide with a pin.

Caveat, load-bearing: hoisting a literal so it stays *referenceable* is not enough;
for it to keep unit-propagating (the Ch.3 invariant) at its new level it must be
chain-linked to its neighbours *at that level*. So hoisting is two steps — move the
definition **and** stitch the literal into the target level's chain (for
hoist-to-top, into the permanent boundary chain). This is the existing stitch
machinery run in the hoist direction. Doing only the first step reintroduces a
subtler version of the chain-fragmentation bug.

## The deletion rule

Stated once, cleanly:

> Delete a literal only when no surviving constraint names it. If a surviving
> constraint at level L names a literal currently at a deeper level, **hoist** the
> literal to L instead of deleting it.

The brancher's backtrack constraint and any live nogoods are the "surviving
constraints" that trigger hoists. A compact bound backtrack constraint names one
literal, so one is hoisted and the rest of the stepped-over range is deleted (the
win). An excluded-set constraint names many, so many are hoisted (no win, but
correct). Retention is therefore automatic and exactly as tight as the brancher's
backtrack constraint — there is no separate "retained set" to maintain.

## Mapping the existing heuristics

Helpers make each existing `value_order::` a one-liner:

| value_order                                   | backtrack constraint       | deletable        |
|-----------------------------------------------|----------------------------|------------------|
| `smallest_first`, `smallest_in`               | ascending `LowerBound`     | yes, O(1) pin    |
| `largest_first`, `largest_in`                 | descending `UpperBound`    | yes              |
| `split_smallest_first` / `split_largest_first`| `LowerBound`/`UpperBound`  | yes              |
| `median`, `random`, `random_out`, `reject_random_interval` | `ExcludedSet` | no (unchanged)   |

The orders people use for large domains (in-order, split) get the win; the
deliberately-random ones keep working unchanged.

## Restarts

Backtrack constraints and advance RUPs live at `Current` levels, so a restart's
`forget` wipes them and the next pass simply re-runs the brancher and re-emits
them — no special handling. The coupling is with learned nogoods: they are at
`Top` and name the decision (branch-threshold) literals, so those literals must
survive. They **hoist to Top**. Since nogoods are the reduced positive-decision
prefix, this hoists O(nogoods) literals, not O(domain).

## Last-value / phase saving

Falls out for free, and in fact motivates the hole-jumping. Trying a remembered
value `X==42` first: if it is refuted it becomes a hole `X != 42`; when the
ascending frontier later reaches 42 it jumps over it with the verified
guess-reasoned RUP. The backtrack constraint stays a clean bound; the saved value
is just a hole in its path. The d-way "last sibling is free" case is subsumed too:
the frontier reaching `ub+1` *is* the at-least-one closure, so there is no separate
last-value special case to carry.

(There is no in-tree phase-saving today; if one is added it slots in here as a
first decision that may become a hole.)

## Parallel search (future)

Planned parallel search runs independent search processes that sometimes share
restart-nogoods. A shared nogood is only usable by a receiving process if the
literals it names are stably, identically defined there — which is exactly what
**hoist-to-top** guarantees. So this design does not solve parallel *proof-logging*,
but the hoist-to-top hook is the thing that future work will want, and nothing here
precludes it. Restart nogoods hoisting to Top (above) is the same mechanism.

## Extensibility

A new brancher is: pick a variable, yield decisions, tag each with a backtrack
advance — or, for the common case, call `frontier_ascending()` / `bisect()` and get
the consolidation, hoisting and deletion for free. Unstructured branchers use
`excluded_set()` (correct, no win). `Custom` is the escape hatch, and even it never
writes raw VeriPB — it hands back a backtrack constraint and the framework emits the
RUP. Per the "don't design ourselves into a corner, but don't over-commit" steer, we
ship the internal helpers plus `Custom` and leave a polished power-user surface until
a real use case lands.

## Implementation staging

> **Superseded.** This was the original four-step sketch, written before the step-2
> design was decided. Steps 1 and 2 are done (the hoist primitive, and the Brancher
> abstraction through stage B'), and step 3's "replace the experimental Literals mode"
> is now stage E's cleanup. Use **[brancher-design.md](brancher-design.md), "Migration
> staging"** for what is actually left. Kept here for provenance.

1. **Hoist primitive first.** It is foundational, independently testable, and needed
   by everything downstream. Build `hoist_literal_to_level` / `hoist_literal_to_top`
   (definition move + stitch into the target chain) and verify with VeriPB that a
   deep literal hoisted to Top / to a level still checks and the chain stays intact.
2. **Brancher abstraction.** Introduce `Brancher` + `BacktrackConstraint` +
   `BacktrackAdvance`, port the existing `value_order::` heuristics onto it via
   helpers (default `Exclude` = today's behaviour, byte-identical), keep `branch_with`
   working.
3. **Wire deletion.** Drive deletion from backtrack-constraint advances (consolidate ->
   hoist -> delete), replacing the experimental `OrderEncodingDeletion::Literals`
   mode. Gate behind the existing flag until it verifies across the suite.
4. **Benchmark.** Re-run the eq-free large-domain sweep (split branching, UNSAT) that
   the earlier attempt could not measure because its proofs did not verify.

Each stage gates on: VeriPB accepts, and recursions/propagations/solutions are
unchanged mode-off vs mode-on (a proof-only change must not perturb search).

## Open questions

- Backtrack-constraint expressiveness beyond bound/excluded-set/custom — deferred;
  revisit if a disjunctive (interval) brancher wants a first-class kind.
- Exactly how much chain context a hoist must carry to preserve the Ch.3 invariant
  cheaply (splice a single skip-link vs. rebuild a span).
- Whether hoist-to-top of nogood literals wants the full definition or a lighter
  "nameable at Top" form, once parallel proof-logging is designed.

## Provenance and artifacts

- **The artifacts directory** — currently `~/claude/tmp/order-encoding-deletion-artifacts/`.
  Not version controlled and it does not travel with a clone, so check it is present
  before relying on it. It holds `order_jump_check.cc` / `order_hoist_check.cc` (the two
  verified foundations, still uncommitted — stage E promotes them), the phase-2 campaign
  (`real-instance-bench/`, with the gate study in `chain-gate/`), the seed-bug sweep
  (`divide-modulus-seed-bug/`), the per-stage gate logs (`stage-b/`, `stage-bprime/`,
  `rebase-to-main-20260729/`), and the two self-contained VeriPB drivers the unbuilt
  stages rest on: `eq-window/run.sh` (the eq-atom window, **8/8**) and
  `objective-delc/run.sh` (the `delc` mechanics, **11/11**). Both need only `veripb`
  3.0.2 on `PATH` — no GCS build — and both were re-run green on the current machine.
  [brancher-design.md](brancher-design.md), "Provenance", says what each contains.
- `benchmarks/order_deletion_bench/` — scalable eq-free linear/pairwise/cumulative
  driver (split branching, `--unsat`) for the benchmark.
- Background: McIlree PhD thesis, Chapter 3 (integer-literal propagation properties);
  [variable-encodings.md](variable-encodings.md); [reasons-improvement.md](reasons-improvement.md).
