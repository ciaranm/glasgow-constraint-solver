# Certified edge-finding for Cumulative (#733)

Working notes for the branch `cumulative-edge-finding`, off `main`. Delete
before the PR.

## Decisions taken at the start (Ciaran, 2026-08-13)

- **Cumulative first**, reversing #733's stated "Disjunctive first, then
  Cumulative". Everything the certificate needs is already in `main`; the
  disjunctive side would need a clipped variant of `energy_pol` plus the whole
  unmerged #737-#741 stack under it, and no local benchmark posts a
  `Disjunctive` at all.
- **Extend the existing (OC') window sweep** rather than writing a Theta-Lambda
  tree. The certificate needs an explicit Theta and its window; the sweep
  already computes both, and a tree would have to reconstruct them.
- **Drop #733's gate on #732** (not-first / not-last). The composability
  question it was there to answer is answered below; #732 is the same
  certificate with the conclusion on `ub(s_j)`, so it becomes a follow-on.

## The rule

At window `[a, b)` with `Theta` the tasks contained in it (`est >= a`,
`lct <= b`), `width = slots_within(a, b)`, `energy = sum of p_i h_i over Theta`,
and a task `j` with `est_j >= a` and `lct_j > b`:

    detection    energy + h_j p_j  >  capacity * width
    rest         energy - (capacity - h_j) * width  >  0
    conclusion   s_j >= a + ceil(rest / h_j)

A `j` starting before `a` is not skipped, it is handled at the window
`[est_j, b)`, which the sweep visits in its own right because every candidate's
`est` is a window start.

## The certificate

One window, no chain. The conclusion is a bound push, so the framework's
wrapping RUP gets `s_j >= new_lb` and the explicit steps are emitted under the
reason with `[s_j >= new_lb]` riding every line as an extra disjunct --- the
`ExtLits` / `plus_ext` idiom at `cumulative.cc:729`, already used by both
time-table push chains.

1. Each `i` in `Theta`: `derive_window_energy` at its real bounds over
   `[a, b)`. Contained form, bound `p_i`. Identical to what the overload check
   emits today.
2. Task `j`: `derive_window_energy` over the same window at start bounds
   `(est_j, new_lb - 1)`. This is the **clipped** case --- the one the lemma was
   written for and which nothing currently calls. It returns
   `min(p_j, b - new_lb + 1)`.
3. Sum with the `C_t` capacity lines, scaling each energy line by `h_i`. Under
   the negated conclusion the window is overloaded, so the pol is contradictory
   and the wrapping RUP closes it.

Cost is `O((|Theta| + 1) * w)` lines per firing, the same order as the overload
check that ships.

### Why detection is needed as well as `rest > 0`

The pol closes in two branches, and the second is exactly the detection test:

- `min` is `b - new_lb + 1`: total is at least
  `rest + (C - h_j) width + h_j (b - a) - h_j ceil(rest / h_j) + h_j`, and
  `h_j ceil(rest / h_j) <= rest + h_j - 1`, so the total is at least
  `(C - h_j) width + h_j (b - a) + 1`, which exceeds `C * width` whenever
  `b - a >= width`. Always true, since `slots_within(a, b) <= b - a`.
- `min` is `p_j`: the total is `energy + h_j p_j`, and needing that to exceed
  `capacity * width` *is* the detection condition.

So detection is not an optimisation, it is what makes the second branch close.
The propagator therefore tests `window_energy_bound()` --- the lemma's own
arithmetic --- rather than the textbook condition alone, and fires only where
the proof will close.

## Stages

1. **Propagator, no proof code, `CumulativeRules::edge_finding` default off,
   refusing to run against a logger.** DONE. `--cumulative-edge-finding` on
   `examples/rcpsp` drives it.
2. **Measure the firing rate and search shape with proofs off**, on the Pack and
   Pack_d collections, before writing any proof code. This is the #730 lesson:
   a rule whose propagation does not pay is not worth a certificate, and the
   per-firing proof cost has to be priced against the firing count, not admired
   on its own.
3. The certificate, its mutation lanes, and the enumeration tests.
4. #732 as a follow-on.

## Not done yet

- **The mirror direction.** Only `lb(s_j)` is pushed. A real edge-finder also
  drops `ub(s_j)` from `j << Theta`, which wants the sweep run mirrored. Both
  directions before any strength claim.
- **Maximising the push.** The closed form is the classical update. The clipped
  test would license a binary search for the largest `new_lb` that still
  overflows, which is energetic reasoning rather than edge-finding, and is
  #696's territory.
- **A height-ordered scan.** `rest` is monotone in `h_j`, so iterating
  candidates tallest-first lets the scan `break` instead of `continue`. The
  `tallest` guard is the one-multiplication version of the same idea.
