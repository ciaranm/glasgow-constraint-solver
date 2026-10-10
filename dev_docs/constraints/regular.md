# `Regular`: a sequence of variables spells a word that a finite automaton accepts

> **Maturity** production (`Regular` under `proof_strategy::Upfront`, the
> default, and `proof_strategy::PerCall`, and the regular-expression form);
> benchmarking only (`proof_strategy::Bacchus`) ·
> **Audited** 2026-10-10 at `86caad24` ·
> **Open issues** filed by this audit: #1328 (MiniZinc's `regular` with a
> start state other than 1 gets wrong answers), #1329 (`Bacchus` accepts an
> empty sequence whose start state is not final; shared with `MDD`), #1331
> (`Bacchus`'s proofs are rejected because its scaffold leaves out three kinds
> of unit clause from the published encoding), #1332 (above
> `AssertionLevel::Off`, `Upfront`'s solution lines are rejected for an
> unambiguous non-deterministic automaton), #1330 (the root scaffolding
> `Regular` writes at every level is rejected above `Links` for a sequence
> variable declared as a range whose bounds unit propagation cannot recover,
> or a view whose own range is such a range, because the tracker omits the
> boundary pins there), #1333 (an out-of-range state number crashes; shared
> with `MDD`), #1335 (the `.scp` reader refuses the non-deterministic automata
> the writer emits), #1338 (the graph is copied whole at every search node, 49
> to 264 times Gecode's instructions; shared with `MDD`), #1339 (the support
> map keeps an entry per declared value, so every search node costs time
> linear in the declared width; shared with `MDD`). Commented on by this
> audit: #1227 (the regex form also builds its alphabet one value at a time),
> #364 (`regular` is not the incrementality gold standard; #1338, #1339) and
> #1120 (`PerCall`'s per-call short-reason flag, the same pattern).
> Already open and touching this family: #841 (the OPB alphabet includes every
> domain value), #1227 (the regex parser expands class ranges and quantifiers
> value by value), #489 (cake chain fails when a domain is narrower than the
> alphabet), #833 and #846 (large domains), #364 (the incrementality survey,
> which lists `regular` as already incremental), #200 (a unified layered-DAG
> framework), #1210 (`Links`-level solution lines, generic), #868
> (cross-solver comparisons; this document gives one, by hand). Tracked under
> #871.

`Regular(vars, num_states, transitions, final_states)` requires that the
values of `vars`, read left to right from state 0, drive the automaton into a
final state. The automaton may be non-deterministic, or given as a regular
expression in MiniZinc's syntax, which is compiled to one. There is one
public class and three proof strategies, chosen with `with_proof_strategy()`:
`Upfront` (the default) derives a scaffold at the root and kills states
lazily during search, `PerCall` re-derives McIlree's per-edge justifications
on every call, and `Bacchus` derives Bacchus's transition-variable encoding at
the root and writes nothing per call. All three run the same algorithm,
Pesant's layered graph, in three copies of the code (one per strategy's
class), so they draw the same inferences; only the proof differs. For an ambiguous automaton (#1203) the proof first pins the state
flags to one canonical run.

Four things to know before touching it.

- **It is generalised arc consistent on distinct variables, under every
  strategy, and the default's proofs check.** A brute-force check at the root
  over 12,000 random automata, deterministic and not, with holey domains,
  found no unsupported value and no lost solution, and a per-node check over
  the seed-1 half (about 6,000 automata) found none either. A repeated variable loses generalised arc consistency (163 of
  3,000 instances), but never a solution.
- **Two wrong answers: one through MiniZinc, one under an opt-in strategy.**
  Through MiniZinc, a `regular` whose start state is not state 1 is translated
  into a different automaton, so `fzn-glasgow` loses solutions or reports
  non-solutions (#1328); no Challenge model reaches it, but an
  enum-typed start state does, and so does a reified `regular` on MiniZinc
  2.10.1, which rewrites it into a plain one with the same start state. And `Bacchus` over an empty sequence reports the empty word as
  accepted even when state 0 is not final (#1329).
- **Three shapes of rejected proof.** `Bacchus` writes no proof per pruning
  and relies on unit propagation over its root encoding, which is not complete
  without three kinds of unit clause the published encoding has and this one
  leaves out (a state with no outgoing transition, one with no incoming
  transition, a non-final last-layer state): 7 of 1,300 random proofs here and
  63 of 10,000 in the fact-check's sweep are rejected at `Off`, some with a
  single final state (#1331). `Upfront` omits the statically dead
  state lines above `Off`, which an unambiguous non-deterministic automaton's
  solution lines need, so the default strategy's proofs fail at the assertion
  levels on 6 of 100 random NFAs (#1332). And the root scaffolding
  written as real steps at every level (the canonical run, `PerCall`'s static
  dead lines, `Bacchus`'s encoding) is rejected at `Inferences` and
  `Backtracking` for a sequence variable declared as a range whose bounds unit propagation cannot recover from its bits (such as `1..2`, `-1..2` or `-5..9`), or a view whose own range is such a range (such as `x' + 1` over `x' ∈ 0..1`); a variable declared from a value list is not affected: its domain collapses need the variable's
  declared bounds, and above `Links` the tracker emits no boundary pins
  (#1330).
- **It is very slow per node, and the reason is the state restore, not the
  algorithm.** The layered graph is a nest of hash maps and sets held as
  backtrackable constraint state, so it is deep-copied at every search node.
  On random nonograms with the same node counts as Gecode it executes 49, 124
  and 264 times Gecode's instructions, and a profile puts about half of the
  samples in copying and freeing those graphs (#1338). The support
  map also keeps an empty entry for every declared value of every domain, so
  that cost, and the per-call scan, grow with the declared width at every node
  of the search: ten variables of `0..9999` under a two-symbol automaton take
  540 times the instructions of `0..1` (#1339).

## What it is

### Semantics

`Regular(vars, num_states, transitions, final_states)`: states are
`0..num_states-1`, state 0 is the start, `final_states` lists the accepting
states, and `transitions[q]` maps a value to the next state (three
constructors: a sparse `unordered_map<Integer, long>` per state, where `-1`
means "no transition"; a dense `vector<vector<long>>` indexed by value
`0..`, again with `-1`; and a sparse `unordered_map<Integer, set<long>>` per
state for a non-deterministic automaton). A missing transition rejects. The
sequence is accepted when some run from state 0 on `vars[0], vars[1], …` ends
in a final state. `Regular(vars, regex)` compiles a MiniZinc-syntax regular
expression (`regex.hh`) to an epsilon-free NFA in `prepare()`, with `.` and
`[^…]` ranging over the contiguous `min..max` of the union of the variables'
initial domains, as MiniZinc does.

The symbols are the values themselves, any integers in the bounded range: the
two sparse constructors and the regex tokenizer check each value with
`innards::require_bounded` (`regular.cc:480`, `:503`, `regex.cc:80`; #1215,
and #1268 for the non-deterministic constructor). There is no requirement that the alphabet start at 0 or 1, or be
contiguous.

- **Empty sequence:** accepted exactly when state 0 is final (#254), under
  `Upfront` and `PerCall`. `Bacchus` accepts it whatever the final states are
  (#1329).
- **No final states, or none reachable:** unsatisfiable, detected at the root.
- **A repeated variable** is allowed and means the same value at every
  position it occupies; see [Robustness and limits](#robustness-and-limits).
- **State numbers are not validated.** A target or final state outside
  `0..num_states-1`, `num_states = 0`, a sparse table shorter than
  `num_states` or a dense one longer is undefined behaviour: segmentation
  faults, a crash in the constructor, a `ProofError` with proofs on, or, for
  a bad final state with proofs off, a silently accepted constraint (#1333).

### Concrete constraints and frontend coverage

| C++ class | MiniZinc / FlatZinc | XCSP3 | CPMpy | SCP `s_expr` | Notes |
|---|---|---|---|---|---|
| `Regular`, deterministic | ✓ `fzn_regular` → `glasgow_regular`[^mznreg] | ✓ `regular` | ?[^gcspy] | ✓ `regular` | wrong answers when `q0 ≠ 1`[^q0] |
| `Regular`, non-deterministic | `decompose`[^mznnfa] | ✓ `regular` (#1204) | ?[^gcspy] | written ✓, read `frontend gap` (#1335) | |
| `Regular`, regex | ✓, as a deterministic `fzn_regular`[^mznrx] | n/a | ?[^gcspy] | written as the compiled automaton | gcs's own regex compiler is C++ only |
| alphabet not starting at 1 | `decompose`[^mznset] | ✓ | ?[^gcspy] | ✓ | |
| reified | `unsupported` (2.9.7); ✓ via `glasgow_regular` (2.10.1)[^mznreif] | n/a | ? | n/a | no reified class; 2.10.1 reaches #1328 |
| `cost_regular` | `decompose` (standard library) | n/a | ? | n/a | no cost variant; #653 |

[^mznreg]: `minizinc/mznlib/fzn_regular.mzn` hands `x`, `Q`, `S`, the
    flattened `d`, `q0` and `F` to `glasgow_regular` unshifted (#803), and
    `fzn_glasgow.cc:1195-1235` keys the table by the symbols `1..S`, maps state
    `k` to `k − 1`, drops FlatZinc's failing state 0, and swaps `q0` with state
    1 so that the start is state 0.

[^q0]: The swap is applied to the transition targets only, not to the row
    index or to `F`, so for `q0 ≠ 1` the automaton gcs builds is a different
    one (#1328). Measured against Gecode on MiniZinc 2.9.7 and
    2.10.1 (`tmp/fd-dd/regular/mzn/diff.sh`): five shapes disagree, among them
    `q0 = 2` of 3 (5 solutions against gcs's 2, one of them wrong), the
    four-argument enum form with the start state `B` of `{A, B, C}`, and an
    empty sequence with `q0 = 2 ∈ F` (gcs says unsatisfiable); and on 2.10.1
    a reified `regular` with `q0 = 2` (footnote below). Nine shapes agree on
    both versions, including a non-1-based index set, empty sequences with
    `q0 = 1`, and the two decomposed rows below; the harness classifies the
    status markers and counts only `COMPLETE` or `UNSAT` on both sides as
    agreement. The fact-check's random sweep (120 models, both versions) found
    every `q0 = 1` model agreeing and 46 of 53 `q0 ≠ 1` models disagreeing. All
    20 Challenge models in the 285-model flattened corpus that post
    `glasgow_regular` pass `q0 = 1`. The half-swap dates from the handler's
    first version (`1dfe6366`, 2024-04-10).

[^mznnfa]: `regular_nfa` has no gcs override; the standard library's
    `fzn_regular_nfa` decomposes it into one state variable per position and
    element constraints. Gecode and gcs agree on `nfa.mzn`.

[^mznrx]: `regular(x, "…")` (`regular_regexp.mzn`) is compiled by MiniZinc
    into a deterministic `regular` with `q0 = 1`, which then reaches
    `glasgow_regular`. So gcs's own regex compiler is reached only from the C++
    API. Fifteen expressions (`tmp/fd-dd/regular/rx/exprs.txt`, among them
    `.`, `(.)*`, negated classes over holey domains, class ranges, counted
    quantifiers, multi-digit symbols, negative values and one unsatisfiable
    case) give the same status and the same solutions through gcs's regex form
    as through MiniZinc and Gecode, on both versions, 30 of 30 comparisons
    (`rxdiff2.sh`, which classifies MiniZinc's status markers on the Gecode
    side and, on gcs's side, the probe's exit status and solution count:
    `ERROR` on a failed run, `COMPLETE` with any solution, `UNSAT` without;
    `rxdiff2.txt`). The audit's first harness compared
    solution sets only, and the fact-check found it would call two failures an
    agreement.

[^mznset]: `regular` with an alphabet set whose minimum is not 1 calls
    `fzn_regular_set`, which gcs does not override; the standard library
    decomposes it. Agrees with Gecode (`set0.mzn`).

[^mznreif]: MiniZinc 2.9.7's `fzn_regular_reif` aborts ("Reified regular
    constraint is not supported") for every solver. 2.10.1's decomposes only
    when `fzn_regular_is_decomposed` is set, which gcs's `mznlib` does not
    set; otherwise it rewrites `b <-> regular(x, Q, S, d, q0, F)` into a plain
    `fzn_regular` over `Q + 2` states and `S + 2` symbols with one more
    variable, passing `q0` unchanged, which reaches `glasgow_regular`
    (`reif.mzn` flattens to `glasgow_regular` with 4 states and `q0 = 1`).
    With `q0 = 1` Gecode and gcs agree (`reif.mzn`); with `q0 = 2`
    (`reif_q0.mzn`) both find 8 solutions, but different ones: #1328's bug
    on a second route.

[^gcspy]: `gcspy` binds nothing in this family, so CPMpy cannot post it
    natively. Whether CPMpy decomposes `Regular` before it reaches `gcspy` was
    not investigated.

The XCSP3 reader (`xcsp_glasgow_constraint_solver.cc:422-461`) numbers states
by first appearance, with the start state forced to 0, and keeps every target
of a non-deterministic transition (#1204). Four instances (a non-deterministic
automaton whose start is not listed first, with negative symbols and two final
states; a one-variable instance; a final state that never appears in a
transition; a holey domain) give the same solutions as a brute-force
enumeration (`tmp/fd-dd/regular/xcsp/`). ACE 2.6 refuses the
non-deterministic one ("unimplemented case for non deterministic automaton")
and the one-variable one, so ACE could check only two. The fact-check added
two more (an NFA whose start is reached only as a target, and a permuted
`<list>`), which also match a brute force.

### Options

**`with_proof_strategy(RegularProofStrategy)`**, where `RegularProofStrategy`
is `std::variant<proof_strategy::Upfront, proof_strategy::PerCall,
proof_strategy::Bacchus>`; the default is `Upfront`. It is proof-only: the
three install the same algorithm (three copies of the propagator and its
graph type, `regular.cc:94`/`:280`, `regular_legacy.cc:81`/`:285`,
`regular_bacchus.cc:72`/`:173`) and draw the same inferences, and on every benchmark here their search statistics are identical.
`Upfront` is the class's own path; for the other two, `prepare()` builds the
sibling class (`RegularLegacy`, `RegularBacchus`), installs it in full and
returns `false` (`regular.cc:547-570`). `Bacchus` throws
`UnimplementedException` for a regex, and for any transition set that is not a
singleton, which includes an empty set from the set-valued constructor. Why
`Upfront` is the default is [`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md)'s
argument: a narrow diagram, so a small permanent scaffold, displacing a verbose
per-call baseline. This audit's figures agree with the conclusion, on proof
size and checking time (see [Proof performance](#proof-performance)), but not
with the premise: on the 25×25 nonogram (`nono 25 1 50`), 66,680 of `Upfront`'s 85,553 lines
(78%) are root scaffold, which is not small. `Upfront` wins there because it
writes a quarter of `PerCall`'s lines at about the same cost per line (3.08 s
over 85,553 lines and 12.93 s over 363,327 lines are both about 36 µs a line),
not because its scaffold adds no tax.

**Does the option change the OPB model?** `Upfront` and `PerCall`: no, the
rows and the flag names are identical. `Bacchus`: the same rows, but its state
flags are named `state<i>is<q>` (rendered `f[k][state<i>is<q>]`) rather than
`x[id][<i>_<q>][st]`, and its forward rows are labelled
`@c[id][fwd<i>q<q>v<v>]` so that its root `pol` steps can cite them
(`regular_bacchus.cc:287`, `:313`). So `Bacchus`'s OPB says the same thing
under different names, and does not match `cake_pb_cp`'s; see [Cake
conformity](#cake-conformity).

**`with_short_reasons(std::optional<bool>)`**, default `true`. Read only by
`PerCall`, where it defines one proof flag per call reifying the call's whole
reason, and states every line under that flag. `Upfront` and `Bacchus` ignore
it: it is kept as a no-op dummy so that `regular_random` and `nonogram` can
benchmark all three strategies from one call site.

There is no `with_consistency()`: every strategy is generalised arc
consistent, and there is no weaker arm.

### Variable kinds and views

Plain variables, constants and views, at any position. The propagator reads
domains value by value and removes values, and the proof writes `x_i ≠ v`
over each position's own proof variable, so a view is handled by the literal
layer. **Above `Links` there is a gap**, and it is not about views as such:
the root scaffolding written as real steps at every level (the canonical run,
`PerCall`'s static dead lines for an NFA, `Bacchus`'s encoding) collapses
domains, which needs each variable's declared bounds, and above `Links` the
tracker emits no boundary pins (`ensure_boundary_pin`). A variable declared as
a range (`create_integer_variable(lo, hi)`) has its bounds recovered from its
bit rows for some ranges (`0..1`, `0..9`, `-2..3`, `-8..7`) and not for
others (`1..2`, `-1..2`, `-5..9`, `-3..4`, `-1..4`, `-100..1`). A view behaves
like a range over **its own** range: `x' + 1` over `x' ∈ 0..1` or `-2..3` is
rejected, over `x' ∈ -1..2` or `-9..6` accepted. A variable declared from a
value list is not affected, because its at-least-one row over its values
(`@c[…][al1]`, posted through `In`) closes the collapse; a view of one is
affected by the view's range (#1330; see [Proof-time
state](#proof-time-state)). By default two view lanes run,
`regular_constraint_view_mixed` and `_view_mixed_late`; the per-wrap and
per-position lanes `add_view_tests(regular_constraint regular_test 4)` defines
exist only with `GCS_ENABLE_VIEW_WRAP_SWEEP=ON`, off by default. Either way the
view lanes run only the deterministic data: the regex, NFA and duplicate
shapes are skipped under a wrap (`regular_test.cc:355-359`), and every lane is
at `Off`. The regex form's `s_expr()` recomputes the alphabet from
each position's tracked bounds, views and constants included
(`regular.cc:730-749`).

### Reification

`None.` There is no reified class. MiniZinc 2.10.1 rewrites `regular_reif`
into a plain `regular` over a larger automaton, which reaches
`glasgow_regular` (and #1328 when `q0 ≠ 1`); 2.9.7 refuses it. A native reified form would want its own
encoding (the state flags half-reified on the condition) and is not obviously
worth it: no Challenge model posts one.

### Relation to other families

- **Decomposes into it:** nothing in the solver. MiniZinc's regex form arrives
  as a deterministic `regular`.
- **Child constraints:** none.
- **Shares code:** `canonical_run.{cc,hh}` is this family's own. It calls
  `recover_am1_from_pairs` (`innards/proofs/am1_from_pairs.hh`, whose header
  documents it; no family document owns it, and `all_different.md`,
  `min_distance.md`, `disjunctive.md`, `counting.md` and `sort.md` describe it
  among their callers' steps),
  and `ProofScaffoldingScope`. `MDD` (`gcs/constraints/mdd/`) carries its own
  copy of the same graph-maintenance code (`RegularGraph`'s fields,
  `decrement_outdeg` / `decrement_indeg`, the cache-gated dead-state line);
  nothing is shared, so a fix to one does not reach the other; #1338 and
  #1339 each cover both copies. `MDD` has no canonical run, since its layers are deterministic. `RegularLegacy` and
  `RegularBacchus` are this family's own internal classes.
- **Presolvers:** none reads or writes it.
- **Front-end-only reachability:** no. The C++ API and the `.scp` reader post
  it directly; `regular_random` and `nonogram` exercise all three strategies.
- **The shared design note.** [`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md)
  is shared with [`mdd.md`](mdd.md) and [`knapsack.md`](knapsack.md), and also
  covers `BinPacking`, which [`bin-packing.md`](../bin-packing.md) documents;
  it stays as a long note. This document describes `Regular`'s own strategies in its
  own fields and cites it for the cost model.

## The proof model

### OPB encoding

The same block for every strategy, McIlree's Encoding Procedure 5.1, extended
to a non-deterministic automaton. With `n = |vars|`, states `Q = 0..S−1`, and
the OPB alphabet `A` = the union of the transition keys **and every value of
every variable's initial domain** (`regular.cc:602-605`):

```
s[i][q]                proof flag, i ∈ 0..n, q ∈ Q            x[id][<i>_<q>][st]
∑_q s[i][q] = 1        for every layer i                       (two rows each)
s[0][0] ≥ 1
∑_{f ∈ F} s[n][f] ≥ 1
for i ∈ 0..n−1, q ∈ Q, v ∈ A:
  δ(q, v) = ∅:   ¬s[i][q] ∨ x_i ≠ v
  δ(q, v) ≠ ∅:   ¬s[i][q] ∨ x_i ≠ v ∨ ⋁_{q' ∈ δ(q, v)} s[i+1][q']
```

`s[i][q]` means "the accepting run the flags record is in state `q` after `i`
symbols". **It is definitional for a deterministic automaton**, whose flags are
then the run. For a non-deterministic one the rows say "there is an accepting
run" and the flags pick one, which the OPB leaves free; when a word has two,
nothing determines the flags, which is #1203, fixed by the canonical run in the
proof rather than in the model (see [Proof-time state](#proof-time-state)).

**Size**, from the emission code and checked against the OPB of a counter
automaton (`tmp/fd-dd/regular/size/`). The constraint's own block is
`2(n+1) + 2 + n·S·|A|` rows. Terms: `2S(n+1)` in the exactly-ones, `1` and
`|F|`, then `2 + |δ(q, v)|` per transition row and `2` per no-transition row.
Measured: `n = 10`, `S = 2`, a two-symbol automaton over `0..1` gives 64 rows
and 166 terms, exactly the formula; `S = 8`, 184 rows. Then the declared width
enters through `A`: over `0..W−1` with the same two symbols, the block is
`24 + 20W` rows (224, 2,024, 20,024 rows at `W = 10, 100, 1000`), and the
literal layer adds `4(W+1)` rows per variable: `4W + 2` definitions of the `=`
and `≥` atoms the rows name, and the variable's two bound rows (440, 4,040,
40,040 rows; 1,780, 22,300, 280,420 terms, the `≥` rows carrying one term per
bit; at `W = 10` the bound rows are 20 rows and 80 terms of those). So **both the constraint's rows and the literal
layer grow linearly with the declared width**, for an automaton whose alphabet
is two symbols; that is #841, and [`large-domains.md`](../large-domains.md)
measured the same split. A degenerate point: `n = 0` gives 4 rows (layer 0's
exactly-one, the start and the accept rows).

### Labels

`None` load-bearing under `Upfront` and `PerCall`: the rows carry no labels,
and every justification is a RUP that finds the rows itself. The state flags
are found by name, `x[id][<i>_<q>][st]`, cake's spelling.

`Bacchus` labels each transition row `@c[id][fwd<i>q<q>v<v>]`
(`regular_bacchus.cc:313`), and its root scaffold cites them in one `pol` per
transition (see [Proof-time state](#proof-time-state)).

### Cake conformity

Three chain cases, all `none`: `regular_sat` (a parity automaton),
`regular_unsat` (an unreachable accepting state) and `regular_ternary_sat` (a
sum-mod-3 automaton over `0..2`)
(`verified_encodings/scp_cases/CMakeLists.txt:372-386`). They chain-verify
because the state flags carry cake's names; they stay `none` because the
transition literals are spelt over the lazy bit encoding where cake uses eager
`=` literals (the case comment's #358). All three cases are deterministic.

Checked by hand at `86caad24` (`cake_pb_cp x.scp`, `veripb
--force-checked-deletion --elaborate`, `cake_pb_cp x.scp x.core`;
`tmp/fd-dd/regular/deg/chain1.txt`), under `Upfront` and `PerCall`: the
ambiguous regex `"(0|1)* 1 (0|1)*"` over four variables, with its canonical
run; the unambiguous NFA `"(0|1)* 1 (0|1)"`; `regular_test`'s
`nonfinal_sibling` NFA; a parity automaton; and both empty sequences, all
chain-verify. So the canonical run's `red` steps are accepted against cake's
OPB. These cannot be chain-test cases yet, because the harness re-solves the
`.scp` and the reader refuses a non-deterministic automaton (#1335).

Divergences:

- **A domain narrower than the alphabet** fails the chain: a `{0}` variable
  under a three-symbol automaton is rejected when VeriPB parses the proof
  against cake's OPB, which defines no `≥` atom past the domain's `ub + 1`
  (#489).
- **`Bacchus` does not chain** whenever there is a transition row to cite: its
  proofs cite the `@c[id][fwd…]` labels, which cake's OPB lacks
  (`regular_bacchus.cc:448-460` says so of the labels), and its flags are
  named `f[k][state…]` where cake has `x[id][…][st]`. An empty sequence
  chain-verifies, since nothing is cited (`chain1.txt`, `empty_acc_b`). The
  `.scp` it writes is the same `regular` term, and re-solving it picks
  `Upfront`.
- **`PerCall` and `Bacchus` write `regular`** as their `constraint_type()`,
  since the `.scp` names the constraint, not the strategy (`9d6b6173`).

### Proof-time state

Everything here is in the proof, not the OPB, apart from the state flags.

**`Upfront`, at the root** (one initialiser, `regular.cc:672-689`):

1. *If the automaton is ambiguous* (`regular_is_ambiguous`), the canonical
   run, written as real steps at every assertion level, before any other line
   mentions the state flags. See below. It is rejected at `Inferences` and
   `Backtracking` for a sequence variable declared as a range whose bounds unit propagation cannot recover from its bits (such as `1..2`, `-1..2` or `-5..9`), or a view whose own range is such a range (such as `x' + 1` over `x' ∈ 0..1`); a variable declared from a value list is not affected (#1330).
2. *At `AssertionLevel::Off` only*: per-value backward chains
   `¬s[i+1][q'] ∨ x_i ≠ v ∨ ⋁_{q : q' ∈ δ(q, v)} s[i][q]` for every
   `(i, q', v)` with `v` in the initial domain of `x_i`, at `ProofLevel::Top`,
   then the statically dead state flags `¬s[i][q]` at `Top` (forward-unreachable
   in ascending layer order, then the rest in descending order), unless the
   canonical run has written them. The `DeadCache` is pre-populated with the
   static set.

**`Upfront`, during search:** one `¬s[i][q] ∨ ¬R` per newly dead state at
`ProofLevel::Current`, where `R` is the call's whole-scope reason, cache-gated
per search path (`emit_dead_state`, `regular.cc:131-140`), and only at `Off`.
Then each pruning's own line. Nothing is deleted explicitly; `Current` lines
go on backtrack, together with their cache entries, since the cache is
backtrackable.

**Above `Off`, `Upfront` writes no scaffold** unless the automaton is
ambiguous. For a deterministic automaton that is harmless. For a
non-deterministic but unambiguous one it is not, because its solution lines
need the static dead lines (#1203's analysis, `canonical_run.hh`), and
`PerCall` writes them at every level while `Upfront` does not (#1332).

**`PerCall`, at the root:** the canonical run if ambiguous, else, if the
automaton is non-deterministic, `emit_regular_static_dead_states` (static dead
flags at `Top`, its per-value chains at `Temporary`), written as real steps at
every level (`regular_legacy.cc:543-551`). It verifies at every level when
unit propagation can recover the sequence variables' bounds, and is rejected
at `Inferences` and `Backtracking` otherwise (#1330).

**`PerCall`, during search** (every call, `regular_legacy.cc:285-384`): with
`short_reasons` on, a fresh flag `f ⇔ R` defined by two `red` lines at
**`ProofLevel::Top`, on every call, whether or not anything is inferred, at
every assertion level, and never deleted** (the deletion is commented out,
`regular_legacy.cc:378-383`); then McIlree's per-edge lemmas, each stated
under `f` at `Current`. So `PerCall` grows the permanent database by two lines
per call. [`smart_table.md`](smart_table.md) (#1120) and #1317 (`Circuit`)
record the same pattern; this audit commented on #1120 with `Regular`'s case.

**`Bacchus`, at the root, written as real steps at every assertion level**
(`regular_bacchus.cc:337-436`), so rejected at `Inferences` and
`Backtracking` for a sequence variable declared as a range whose bounds unit propagation cannot recover from its bits (such as `1..2`, `-1..2` or `-5..9`), or a view whose own range is such a range (such as `x' + 1` over `x' ∈ 0..1`); a variable declared from a value list is not affected (#1330):
for every transition `(i, q, v)`, a flag `t[i][q][v] ⇔ x_i = v ∧ s[i][q] ∧
s[i+1][δ(q, v)]` by redundance (`f[k][t<i>q<q>v<v>]`), then one `pol` adding
the labelled transition row to the flag's reverse half, then three families of
at-least-ones by RUP: out of each `(i, q)`, into each `(i+1, q')` that has an
incoming transition, and supporting each `(i, v)`. All at `Top`, never
deleted. Nothing during search. **Three kinds of line the published encoding
has are missing** (EP 5.2; #215): the outgoing at-least-one of a state with no
outgoing transition, which would be the unit `¬s[i][q]` (skipped,
`regular_bacchus.cc:390-391`); the incoming one of a state with no incoming
transition (skipped, `:414`); and the last layer's `¬s[n][q]` for non-final
`q`. Without them unit propagation does not reach GAC, and the prunings
`Bacchus` leaves to the next backtrack are not always re-derived (#1331).

**The canonical run** (`emit_regular_canonical_run`, `canonical_run.cc:176-370`;
derivation in [`regular.md`](../regular.md), "Ambiguous automata"), over the
*live* `(layer, state)` pairs under the root domains:

| Step | Lines | Level | Names |
|---|---|---|---|
| static dead flags | `¬s[i][q]`, with per-value chains for the forward-unreachable | `Top`; chains `Temporary` | the state flags |
| co-reachability `b[i][q]` | per live pair, via `t ⇔ x_i = v ∧ ⋁ b[i+1][·]` | `Top` | `f[k][regb]`, `f[k][regt]` |
| canonical run `c[i][q]` | edge choices `d`, then `c ⇔ ⋁ d` | `Top` | `f[k][regd]`, `f[k][regc]` |
| the rows hold for `c` | `s ⇒ b`, `c ⇒ b`, forward clauses over `c`, per-layer at-least-one and pairwise at-most-one, folded by `recover_am1_from_pairs` | `Temporary`, deleted | none |
| pinning | one guard `e ⇒ (c ⇒ s)` per live non-constant flag, each by its own `red … : e → 0`, then one `red ∑ e ≥ N` whose witness sends each live state flag to its `c`, and each dead one, and each live one whose `c` is constantly false, to 0 | `Top` | `f[k][rege]` |

**Auxiliaries in the OPB and in the proof.** The state flags are in the OPB
(per [`variable-encodings.md`](../variable-encodings.md), an OPB flag); every
other flag here is introduced in the proof. Each is fixed by unit propagation
on a solution: `b` backwards from the variables, `c` and `d` forwards, the
guards through the final `red`, `Bacchus`'s `t` from the variables and the
state flags, and `PerCall`'s reason flag from the reason's literals. The state
flags themselves are fixed by the forward rows from a deterministic
automaton's start; by the canonical run's pinning for an ambiguous one; and
for an unambiguous non-deterministic one, by the forward rows *plus* the
static dead lines, which is why those lines matter at every level. The
boundary pins these root steps lean on are the tracker's, not this family's
(#927, #928); above `Links` the tracker leaves them out on the assumption that
nothing checked there needs them, which is what #1330 runs into.

**Naming, for an external tool.** The state flags `x[id][<i>_<q>][st]` under
the hint's `constraint_id`; everything else is located by its defining `red`
lines. No proof-only vector is indexed by anything that dangles with proofs
off: the bridge's flag table is filled by `define_proof_model`, and the
propagator reads it only when a logger exists.

## The implementation

### Initialisation and global data

`prepare()` compiles a regex (building the `min..max` alphabet value by value,
commented on #1227), builds the OPB alphabet by walking every variable's initial
domain value by value (#841), and allocates the backtrackable `RegularGraph`
and, for `Upfront`, the `DeadCache` (`regular.cc:572-605`).

The graph itself is built on the first propagator call, not in an initialiser
(`initialise_graph`, `regular.cc:153-232`): a forward pass over every value of
every domain and every reachable state, then a backward pass. That is
`O(Σ_i |D_i| · S · t)` set operations, `t` the largest target set.

`Upfront`'s initialiser (default priority) then costs, with proofs on:
`compute_static_dead`, `O(Σ_i |D_i| · S · t)`; the backward chains,
`Σ_i S · |D_i|` lines built by an `O(S)` scan each, so `O(n · S² · |D|)` work;
and for a non-deterministic automaton `regular_is_ambiguous`, a product of the
automaton with itself over the live states, `O(n · P · |D| · t²)` for `P ≤ S²`
live pairs, which returns at once for a deterministic automaton. The canonical
run, when it fires, is linear in `n` times the live edges per layer: for
`"(0|1)* 1 (0|1)*"` at `n = 8, 16, 32, 64`, the non-comment lines
`emit_regular_canonical_run` writes are 988, 2,156, 4,492 and 9,164, of which
941, 2,077, 4,349 and 8,893 are the canonical run proper and the rest its
static dead section (`tmp/fd-dd/regular/canon/recount.txt`, re-counted after the
fact-check; the audit's first figures counted comment lines and left out the
static dead section).

**Root cost that dominates:** a wide declared domain, in every one of these
passes, and on the regex form before the constraint exists. A domain
`0..10⁹` makes the OPB alone billions of rows (#841, the audit lane's
`KnownTrip`).

### Propagator inventory

| Propagator | Triggers | Holes affect | Rule(s) | Enabled by | Idempotent? | Self-disables? |
|---|---|---|---|---|---|---|
| `Upfront` initialiser | — | — | scaffolding, canonical run | `Upfront`, proofs on | — | — |
| `Regular` (`propagate_regular`, `regular.cc:280-351`) | `on_change`, every position | derived: **every sequence variable** | 1, 2 | `Upfront` (default) | never claims | never |
| `PerCall` initialiser | — | — | canonical run, or static dead flags for an NFA | `PerCall`, proofs on | — | — |
| `RegularLegacy` (`regular_legacy.cc:285-384`) | `on_change`, every position | derived: every sequence variable | 1, 2 | `PerCall` | never claims | never |
| `Bacchus` initialiser | — | — | Bacchus scaffold | `Bacchus`, proofs on | — | — |
| `RegularBacchus` (`regular_bacchus.cc:173-212`) | `on_change`, every position | derived: every sequence variable | 2 only (rule 1 missing) | `Bacchus` | never claims | never |

**`on_change` is exact.** The propagator removes edges labelled with a value
that has left a domain, so a hole inside a variable's bounds can kill an edge,
then a state, then a value elsewhere: holes genuinely affect it, and the
derived declaration tells the truth.

**Idempotence.** Not claimed (every propagator returns
`PropagatorState::Enable`). **On distinct variables** it holds in effect, by
reading: the cascade of `decrement_outdeg` / `decrement_indeg` runs to
completion before the pruning loop, and the values the loop removes label no
live edge at their own position, so removing them kills nothing. **With a
repeated variable it does not**: a value removed at one position is a missing
value at the other on the next call, and that call can infer more.
`Regular{y, y}` over `y ∈ 0..2` (states 0: 1 → 1, 2 → 2; 1: 0 → 3; 2: 1 → 3,
2 → 3; finals `{3}`) asserts `y ≠ 0` under `y ∈ 0..2` on one call and `y ≠ 1`
under `y ∈ 1..2` on the next, under `Upfront` and `PerCall` alike (the
cross-document check's `regidem.cc`, re-run at `tmp/fd-dd/regular/fc/`). A
claim would still be safe, because `Propagators` ignores
`EnableButIdempotent` from a propagator whose trigger positions alias one
variable (`propagators.cc:111-129`, `:777-780`); see [Next
steps](#next-steps) item 10.

**Self-disabling.** Never, even with every variable fixed.

### Mutable state and incrementality

**`RegularGraph`, backtrackable** (`add_constraint_state`): per layer and
value, the set of states with a live edge on that value
(`unordered_map<Integer, set<long>>`); per layer and state, out-edges and
in-edges (`unordered_map<long, unordered_set<Integer>>`) and their degree
counts; the live node sets. The per-value map also holds an **empty entry for
every value of every root domain** (strictly, of each domain at the
propagator's first call, which another propagator may already have narrowed),
because the first call's backward pass and
every call's pruning loop look values up with `operator[]` (`regular.cc:203`,
`:347`; `regular_legacy.cc:177`, `:373`; `regular_bacchus.cc:117`, `:208`),
and those entries are never removed (#1339). `Upfront` adds the
`DeadCache`, a `vector<set<long>>`
of states whose dead line this search path has written. `RegularLegacy` and
`RegularBacchus` each carry a copy of the graph type.

The graph's **content** is maintained incrementally, as Pesant's algorithm
intends: a call removes only the edges whose value has gone and cascades from
there. But its **restoration** is not: `State::new_epoch` copies every
constraint state whole at every search node and pops the copy on backtrack
(`state.cc:798`, `:808`), so every node deep-copies every `Regular`'s graph,
touched or not, at a cost proportional to the graph, in allocator calls,
stale entries included. And each call **rescans** every layer's
supporting-value map to find values that have gone, which with the stale
entries is `O(Σ_i |D_i⁰|)` for the **root** domains `D_i⁰`, then every value of
every current domain to find values to prune (`O(Σ_i |D_i|)`), instead of the
variables the trigger says changed; and it materialises the whole-scope reason first, unguarded by
`want_reasons()` (`regular.cc:306`). #364 lists `regular` under "already
incremental (no work needed)" as "the gold standard"; that is true of the
content and not of the restore, as this audit's comment on #364 says. What it costs is under [CPU
performance](#cpu-performance); what to do is [Next steps](#next-steps) item 3.

### Interior values and optional pruning

**Offers.** `None.` There is one arm, generalised arc consistent, and no
pruning that some other propagator could be relied on not to need.

**Observes.** Every sequence variable, through `on_change`, and genuinely:
removing an interior value removes the edges it labels. So a `Regular` over a
variable keeps every other family's optional interior pruning on that variable
alive, which is correct. The state flags are OPB flags with no solver domain,
so nothing observes their holes.

### Robustness and limits

**Unbounded domains.** Every pass is per value of the initial domain, the OPB
included (#841), so a declared domain of `0..10⁹` does not install; the audit
lane pins all three classes as `KnownTrip`. See [Interval
efficiency](#interval-efficiency).

**Negative values and zero.** Symbols are arbitrary integers. The random
strength checks run over domains in `-1..3` with negative and zero symbols,
and the XCSP3 check has negative symbols. FlatZinc numbers symbols `1..S`, and
`fzn_regular.mzn` passes the model's own variables unshifted (#803).

**Degenerate shapes.**

- *Empty sequence:* correct under `Upfront` and `PerCall` (#254's special case,
  `regular.cc:290-300`, which `contradiction()`s when 0 is not final); wrong
  under `Bacchus`, which has no such case (#1329): a
  root-strength sweep finds a solution-count mismatch on 319 and 325 of 3,000
  instances at seeds 1 and 2, every one with `n = 0`.
- *One variable, all fixed, no final state, unreachable finals:* covered by
  `regular_test` (#254), under every strategy for most of them.
- *A repeated variable* is sound and loses generalised arc consistency: each
  position is treated as independent. `Regular{x, x}` over an automaton that
  accepts only `01` and `10` keeps both values of `x` at the root and fails
  only after branching (`deg.cc rep_xx`, 3 recursions, 0 solutions). Root GAC
  failures over 3,000 random instances with repeats (`regcheck … alias`, seed
  3): 163 deterministic under `Upfront` and under `PerCall`, 146
  non-deterministic under `Upfront` (and 488 under `Bacchus`, of which 325 are
  #1329's empty sequences). The per-node check fails too: 208 of 1,267
  checked nodes deterministic, 201 of 1,491 non-deterministic. Never a lost
  solution. `regular_test`'s duplicate runs check enumeration only.
- *Out-of-range state numbers and `num_states = 0`:* undefined behaviour
  (#1333): a target of 7 with two states segfaults `Upfront` and
  `PerCall` with proofs off, and throws `ProofError` ("can't find literals for
  flag") under every strategy with proofs on, uncaught by
  `glasgow_scp_solver --prove` (exit 134); `num_states = 0` segfaults all
  three; a dense table with more rows than `num_states` crashes in the
  constructor (`SIGFPE` or `SIGSEGV`, depending on the heap); a final state of
  5 with two states is silently accepted with proofs off and throws
  `ProofError` with them on; a negative target other than `-1` segfaults all
  three (the fact-check's case).
- *An empty regex* throws `InvalidProblemDefinitionException`; so does any
  unparsable one.

**Overflow.** There is no arithmetic on values: symbols are hashed and
compared. Transition values and regex integers are range-checked (#1215,
and #1268 for the non-deterministic constructor), and a declared domain or view outside `±(2⁶⁰ − 1)` is refused by
#1214. The regex compiler's `lo..hi` loop and class-range loop step a bounded
`Integer` and cannot overflow; they can only be very long (#1227, and this audit's comment
on it). State numbers are `long` and are not checked (#1333).

### Interval efficiency

**Not fine at any width, and the walks are per value of the declared domain,
at the root and at every node.** After the root every domain is a subset of
the automaton's transition keys, but the support map keeps an empty entry for
every value of every root domain, and every call scans those entries while
every node copies them (#1339). Ten variables declared `0..W−1`
under a two-symbol parity automaton, enumerating the same 512 solutions in
1,023 recursions, proofs off: 93.3·10⁶ instructions at `W = 2`, 5.14·10⁹ at
`W = 1,000`, 50.6·10⁹ at `W = 10,000`; one variable at `W = 10,000`, root
only, 23.5·10⁶ (`tmp/fd-dd/regular/fc/w.cc`, after the fact-check's
`width/w.cc`, which also has 507·10⁹ at `W = 10⁵`). The width also bites in
the OPB, in the root's proof and in the regex front end.

1. **The propagation side.** No interval primitive is used anywhere.
   - `initialise_graph`: `each_value_immutable` / `each_value_mutable` over
     every domain, once, at the first call: per value of the root domain.
   - Per call: the scan over `states_supporting[i]`, one entry per value of
     the **root** domain (the live ones and the stale empty ones, #1339);
     then `each_value_mutable` over every domain to prune, per value of the
     current domain. At the root that removes every out-of-alphabet value
     **one `infer_not_equal` at a time**, `n · (W − |Σ|)` inferences for a
     width-`W` domain; afterwards the pruning loop is bounded by the alphabet,
     and the scan is not.
   - `prepare()`: the OPB alphabet walks every initial domain (#841), with
     proofs off too, since it is not gated on a proof model; a regex
     builds `min..max` of the union of the domains as a vector before parsing
     (commented on #1227), and its class ranges and counted quantifiers expand
     value by value (#1227).
   - The initialisers: `compute_static_dead`, the backward chains, and
     `regular_is_ambiguous` and the canonical run's `compute_layers`, each per
     value of the root domain.
   None of these exits early, and none has a weaker arm behind it.
2. **The reason side.** The reason is `generic_reason` over the whole scope:
   two bound literals per unfixed position plus one range literal per run of
   holes, never per value, and the runs are found by interval (#935). It is
   materialised on every call before anything is known to need it
   (`eager_reason`, `regular.cc:306`; `regular_legacy.cc:291`), unguarded by
   `want_reasons()`, proofs off too. `RegularBacchus` uses `NoReason`.
3. **The proof side.** One line per pruned value, never a range: at the root a
   width-`W` domain gets `W − |Σ|` lines per variable for its out-of-alphabet
   values, where one `x_i ∉ …` range line per gap would do. `Upfront`'s backward
   chains are one line per value of the initial domain per `(i, q')`. Neither
   is width-gated. The dead-state lines and the value lines carry the per-run
   reason.
4. **The audit lane.** Three rows, all `KnownTrip`: `Regular`, `RegularLegacy`
   and `RegularBacchus`, each over three variables of `0..10⁹` and a
   two-state, one-symbol automaton (`large_domain_audit_test.cc:743-754`).
   The last two post the internal classes directly rather than through
   `with_proof_strategy()`. No row in the `"Large domain proof sizes"` case.
   **What the rows do not vary:** holes; a non-deterministic automaton (so not
   the ambiguity check or the canonical run); the regex form, whose alphabet
   expansion happens before any of them; proofs (the lane solves without
   them, so the per-value root proof lines and backward chains are unseen);
   views; and search, so the stale per-value entries that cost every node
   time linear in the declared width (#1339) are unseen too: the rows trip
   at the root.

## Inference catalogue

Two rules. Both belong to the one propagator, which every strategy runs; what
differs is the proof, so each entry's **Proof technique**, **Assertion**,
**Hint** and **Proof size** fields are given per strategy.

Facts that hold for both:

**The reason is the whole scope.** Every inference's reason is the generic
reason over every position: both bounds of each unfixed variable, one range
literal per run of holes, one equality per fixed variable. It is sufficient,
and not minimal: a pruning at position `i` depends only on what has gone from
the domains, and is often decided by a few positions. It is one literal per
run, never per value.

**One hint per strategy, no subhint.** `hints::Regular{originator}` (wire
`regular:((constraint_id <id>))`) for `Upfront`, and `hints::RegularLegacy`
(`regular_legacy:(…)`) for `PerCall`, both in `regular/hints.hh`. Nothing says
which rule fired; the clause's shape does. `Bacchus` asserts nothing.

**What licenses the derivations.** McIlree's thesis, Chapter 5, §5.1:
Encoding Procedure 5.1 is the OPB; Justification Procedure 5.1 (Regular
language membership propagation) is the closing RUP of rule 2, and 5.2
(infeasibility) its conflict form; Justification Subprocedures 5.3 and 5.4
remove a node's incoming edges once its outgoing ones are gone (one RUP) and
its outgoing edges once its incoming ones are gone (`|Q|` RUPs plus one);
Justification Procedure 5.5 removes the edges out of the first layer and into
the last. They are stated for a deterministic automaton with per-edge lemmas
`R ⇒ ¬s[i][k] ∨ x_i ≠ v`. `PerCall` is the thesis's implementation and follows
them, with whole-state lemmas added. `Upfront` replaces the per-edge lemmas by
**per-state** ones, `¬s[i][q]` under the reason, followed by each value's
removal by RUP. That shape is published: Demirović, McCreesh, McIlree,
Nordström, Oertel and Sidorov (*Pseudo-Boolean Reasoning About States and
Transitions to Certify Dynamic Programming and Decision Diagram Algorithms*,
CP 2024, LIPIcs 307, §3.3) describe it for GCS's knapsack diagram (RUP steps
showing each infeasible state false, then each value's removal by RUP) and say
it "closely resembles" McIlree and McCreesh's steps for `Regular` (CP 2023).
What is particular to `Upfront` is the engineering around it: the per-value
backward chains derived once at the root and kept at `Top`, and the
per-search-path cache of dead-state lines; see [Prior art](#prior-art). Both strategies also run over a non-deterministic automaton (a
forward row with several targets, so a state is dead only when *every* target
is); the same arguments carry over, and that is not claimed here as new
(Quimper and Walsh treat NFA-specified `Regular`, see [Prior art](#prior-art));
`Bacchus` refuses a non-deterministic automaton. Each step's licence is
Theorem 2.6 (a step under a reason reduces to its consequent), the rows being
clauses or a cardinality constraint, and Theorem 3.2 (an emptied domain is a
conflict) for every "every value of `x_i` is ruled out" collapse; see
[`justification-techniques.md`](../justification-techniques.md).

**Why a dead state is RUP, in the two directions** (used by rule 2 under
`Upfront`, and by an offline reconstruction under every strategy). Write `R`
for the reason. *Forward:* `q'` at layer `i+1` is dead because every edge into
it is gone. Under `R ∧ s[i+1][q']`, the backward chain for each value `v` still
in `D_i` has all its predecessor flags false (earlier lemmas, ascending layer
order), so it propagates `x_i ≠ v`; the values outside `D_i` are false by `R`;
so `x_i`'s domain empties (Theorem 3.2). Each backward chain is itself a RUP
against the OPB: under its negation the layer-`i+1` at-most-one falsifies every
other state flag there, the layer-`i` at-least-one needs some `s[i][p]` with `p`
not a predecessor on `v`, and that `p`'s forward row on `v` has no true target.
*Backward:* `q` at layer `i` is dead because every edge out of it is gone.
Under `R ∧ s[i][q]`, each value `v` still in `D_i` has a forward row whose
targets are all dead (later lemmas, descending order) or a no-transition row,
so `x_i ≠ v` propagates, and the domain empties again. *Last layer:* a
non-final `q` gives `¬s[n][q]` by RUP, since `s[n][q]` and the at-most-one
falsify the accept row. *Start layer:* `¬s[0][q]` for `q ≠ 0` from the start
row and the exactly-one.

### Rule: empty-sequence-rejected

(Rule 1.)

- **Infers** — a contradiction.
- **Fires when** — `vars` is empty and state 0 is not final, on the first call
  (`regular.cc:290-300`, `regular_legacy.cc:300-310`). `Upfront` and
  `PerCall`. **`Bacchus` has no such rule** and accepts the empty word
  (#1329).
- **Strength** — `GAC` (there is nothing else to prune): checked by
  `regular_test`'s `empty seq rejected` and `empty seq accepted`, and by the
  root sweep's `n = 0` instances.
- **Algorithm** — a scan of `final_states`. `O(|F|)`.
- **Why it is true** — the only run on the empty word stays in state 0, which
  does not accept.
- **Proof technique** — `RUP`, against the start row, the accept row and layer
  0's exactly-one: with `s[0][0]` forced and the at-most-one falsifying every
  other layer-0 flag, the accept row over `s[0][f]`, `f ≠ 0`, has no true term.
- **Reason** — the generic reason over no variables: empty.
- **Assertion** — `¬R` from `contradiction()`, with `R` empty: the empty
  clause. Measured at `Inferences`, `Upfront`
  (`tmp/fd-dd/regular/deg/out/empty_rej_u_inferences.pbp`):
  ```
  a >= 1::regular:((constraint_id _1));
  ```
  and `a >= 1::regular_legacy:((constraint_id _1));` under `PerCall`.
- **Hint** — `hints::Regular` / `hints::RegularLegacy`: `originator`, the
  `ConstraintID`.
- **Offline reconstructibility** — `offline`: the clause is RUP against three
  OPB rows.
- **Proof size** — one line.
- **Gaps** — `None` under `Upfront` and `PerCall`. Under `Bacchus` the rule is
  missing, which is a wrong answer, not a proof gap: VeriPB rejects the
  solution line that follows.
- **Tightness** — `Not shown.` No mutation lane.

### Rule: unsupported-value

(Rule 2.)

- **Infers** — `x_i ≠ v`, for each value `v` of each position that no live
  edge of layer `i` carries. When it removes a domain's last value it is the
  conflict; the code never calls `contradiction()` for it.
- **Fires when** — every call, after the edge removals for values that have
  left the domains have cascaded (`regular.cc:311-350`). At the root it removes
  every value outside the alphabet, every value whose edges lead nowhere, and,
  when no accepting path exists, every value. All three strategies.
- **Strength** — `GAC` on the sequence variables, when they are distinct;
  `partial` with a repeated variable: GAC on the decomposition in which each
  position is a distinct variable, which loses GAC at the root and at search
  nodes (see [Robustness](#robustness-and-limits)). Checked by brute force: at the root, 3,000 random automata per
  strategy and seed, deterministic (`Upfront`, `PerCall`, `Bacchus`) and
  non-deterministic (`Upfront`, `PerCall`), sequence lengths 0 to 4, 1 to 4
  states, domains with holes over `-1..3`, seeds 1 and 2: no unsupported value
  and no lost solution (`tmp/fd-dd/regular/gac/regcheck.cc`, `root2.txt`);
  and at every node of a full enumeration of the same instances at seed 1
  (3,722 and 5,023 nodes): none (`node1.txt`). `regular_test` checks GAC at
  every node too (`solve_for_tests_checking_gac`). Pesant proves the
  algorithm domain consistent for a deterministic automaton; the
  non-deterministic case is the same graph with several edges per value.
- **Algorithm** — Pesant's: the unrolled automaton as a layered multigraph,
  kept with degree counts; a removed value deletes its edges, and a node whose
  in- or out-degree reaches zero is deleted with its remaining edges,
  recursively, forwards or backwards; a value is supported while some edge
  carries it. Per call: `O(Σ_i |D_i⁰| + Σ_i |D_i|)` scanning, `D_i⁰` the root
  domain, because the support map keeps an entry for every root value
  (#1339), plus
  `O(edges removed)` for the cascade, amortised over a search path. The edges
  are `(i, q, v, q')` tuples, so the graph is `O(n · S · |Σ| · t)`.
- **Why it is true** — a value at position `i` is in some accepted word only if
  some run reads it on an edge from a state reachable from the start to a
  state that can still reach a final state, over the current domains; the
  graph keeps exactly those edges.
- **Proof technique** — per strategy:
  - *`Upfront`:* `chain scaffolding` (the per-value backward chains, at the
    root) and `RUP sequence`, the published state-elimination shape (CP 2024
    §3.3) closed by JP 5.1's RUP. The lemmas are the dead-state lines
    `¬s[i][q] ∨ ¬R` for every state this call killed and this path has not
    already killed, written in the order the cascade finds them, at
    `Current`, before any domain change (`emit_dead_state`); together with the
    root's static dead lines and backward chains they make the closing step
    JP 5.1's RUP: under `R ∧ x_i = v`, every `s[i][q]` with a transition on `v`
    is false outright or has every target false, so its forward row
    propagates `¬s[i][q]`; the no-transition rows falsify the rest; layer
    `i`'s at-least-one has no true term. Why each lemma is RUP is the preamble's
    two directions. The cascade order matters and is commented in the code:
    `decrement_outdeg` writes a node's line before recursing to its parents
    (`regular.cc:239-246`, `7abd37d5`).
  - *`PerCall`:* `RUP sequence`, the thesis's procedures. For a state
    unreachable at the first pass, per-predecessor lines
    `x_i ≠ v ∨ ¬s[i][q] ∨ ¬s[i+1][q']` for each value, then
    `¬s[i][q] ∨ ¬s[i+1][q']`, then `¬s[i+1][q']` (`regular_legacy.cc:143-161`);
    in the first call's backward pass, `x_i ≠ v ∨ ¬s[i][q]` per edge with no
    live target and `¬s[i][q]` per state left unsupported (`:191-195`,
    `:203-204`); per node killed by its out-degree, one `x_{i−1} ≠ v ∨
    ¬s[i−1][l]` per incoming edge whose source keeps no other edge on that
    value (JSP 5.3, "dec outdeg inner", `:235-240`), then `¬s[i][k]` ("dec
    outdeg", `:245-246`); per node killed by its in-degree the three-step
    pattern again (JSP 5.4, `regular_legacy.cc:250-270`). All under the
    short-reason flag `f`, at `Current`; then the closing RUP (JP 5.1). The
    edge removals the main loop makes for a value that has left a domain write
    nothing, as the thesis says: they are not "explicit". In the in-degree pattern the
    per-value lines name `x_i`, the variable *after* the dead node at layer
    `i`, where the forward rows into it read `x_{i−1}`; they verify because
    each pair line is RUP from the predecessor's own lines regardless, so the
    per-value lines carry nothing. Argued, not measured.
  - *`Bacchus`:* `not logged`, by design (`NoJustificationNeeded`): Bacchus
    (CP 2007) shows unit propagation on his encoding achieves GAC, so the
    next backtrack line's RUP re-derives every pruning. **This tree's encoding
    lacks three kinds of published unit clause** (a state with no outgoing
    transition, one with no incoming transition, a non-final last-layer state;
    see [Proof-time state](#proof-time-state)), so the re-derivation can fail
    and VeriPB rejects the backtrack line, with one final state as well as
    several (#1331).
- **Reason** — the generic reason over the scope, per run; at the root, the
  root domains. Not minimal. Assembled every call, unguarded. `PerCall` states
  every line under one flag reifying it; `Bacchus` uses `NoReason`.
- **Assertion** — `x_i ≠ v ∨ ¬R` per pruned value; in the conflict form, the
  attempted literal and the reason both appear, with no deduplication. Measured
  at `Inferences`, `Upfront`, on a "contains a 2" automaton with `x3 ∈ 0..2`
  (`deg.cc contains2`):
  ```
  a 1 ~i[_3][eq0] 1 ~i[_1][ge0] 1 i[_1][ge2] 1 ~i[_2][ge0] 1 i[_2][ge2] 1 ~i[_3][ge0] 1 i[_3][ge3] >= 1::regular:((constraint_id _1));
  ```
  and the conflict form, the second removal on a 0/1 variable whose domain is
  already `{1}` (`deg.cc c2unsat`), the reason's `x1 = 1` and the attempted
  `x1 ≠ 1` being the same literal twice:
  ```
  a 1 ~i[_1][b0] 1 ~i[_1][b0] 1 ~i[_2][ge0] 1 i[_2][ge2] >= 1::regular:((constraint_id _1));
  ```
  Under `PerCall` the clause names the short-reason flag instead of the
  reason, `a 1 ~i[_3][eq0] 1 ~f[8][] >= 1::regular_legacy:(…)`, with `f`
  defined by two `red` lines just before. Under `Bacchus`, nothing.
- **Hint** — `hints::Regular` (`Upfront`) or `hints::RegularLegacy`
  (`PerCall`): `originator`, the `ConstraintID`. On the wire the default
  identity form. `Bacchus` carries none.
- **Offline reconstructibility** — `offline`, for `Upfront`'s and `PerCall`'s
  assertions. The hint names the constraint, so the rows are known; the reason
  gives every position's domain; from those a reconstructor runs Pesant's two
  passes over the reason's domains, which fixes the set of dead
  `(layer, state)` pairs with nothing chosen, and derives one lemma per dead
  pair, forward-unreachable ones in ascending layer order (each after its
  per-value backward chains) and the rest in descending order, then the
  asserted clause. Each step is guaranteed RUP by the preamble's argument, from
  the rows and what the reason contains. For an NFA the same holds, since a
  state is dead only when every target is. Under `PerCall` the reason is the
  flag `f`, whose two defining `red` lines are in the proof at every level and
  expand it. `Bacchus` asserts nothing, so a hints-only proof contains no trace
  of its prunings and the backtrack assertions carry them.
- **Proof size** — per pruned value one line of `O(n + holes)` literals. The
  lemmas: under `Upfront` at most one dead-state line per `(layer, state)` per
  search path (the cache), each `O(n + holes)` literals; under `PerCall`
  `O(S · |D_i|)` lines per node found unreachable or killed by its
  in-degree, and one per incoming edge of a node killed by its out-degree, each
  of one to three literals plus `f` (on `nono 25 1 50`: 26,379 lines with two
  terms, 118,223 with three and 194,542 with four, `f` included), and two
  permanent `red` lines per call for `f`. Measured shares are under [Proof performance](#proof-performance).
- **Gaps** — `None` under `Upfront` and `PerCall` at `Off`. Under `Bacchus`,
  rejected re-derivations wherever the backtracks are real RUPs, which is up
  to `Links` (`proof_logger.cc:427` asserts them only from `Inferences`), and
  at one shape a rejected scaffold RUP at every level (#1331).
  Above `Off`, `Upfront`'s solution lines for an unambiguous NFA (#1332), and above `Links` the every-level root scaffolding for a variable
  whose bounds unit propagation cannot recover (#1330): the
  scaffold's gaps rather than this rule's. The propagator
  is the same with proofs on or off.
- **Tightness** — no mutation lane in the tree. By hand at `86caad24`
  (`tmp/fd-dd/regular/mut/`, each against an uncorrupted control that
  verifies): pruning a supported value instead (`x3 ≠ 2` for `x3 ≠ 0` on
  `contains2`) is refused at the corrupted line; deleting the forward-unreachable
  static dead line `¬s[1][1]` is refused at the next line, the next
  forward-unreachable line `¬s[2][1]`; on a 12-variable,
  six-state enumeration (`rdfa 12 6 3 1`) deleting every per-call dead-state
  line is refused at line 402, and deleting the backward chains is refused at
  line 133. Not load-bearing on their fixtures: the backward chains on
  `contains2` (two values; the forward rows alone close it), a single backward
  chain on the enumeration, and the backward-dead static line `¬s[3][0]` on
  `contains2`. So the slack instances are small alphabets; a fixture that makes
  each backward chain load-bearing wants more values than states.

## Evidence

### Tests

- **`regular_test`** (`regular_constraint`, plus the view lanes
  `regular_constraint_view_mixed` and `_view_mixed_late`; the per-wrap and
  per-position lanes are registered only with `GCS_ENABLE_VIEW_WRAP_SWEEP=ON`,
  off by default and in CI, and every view lane skips the regex, NFA and
  duplicate shapes): 15 deterministic-automaton
  shapes (parity over `0..1` and over a 1-based alphabet, a 1-based alphabet
  with a hole in the middle, "no two 0s", "contains a 2" with and without a
  forced last position, "all the same", no final states, unreachable finals,
  #254's empty and fixed shapes) under `solve_for_tests_checking_gac`, so GAC
  at every node; eleven regex shapes (concatenation, stars, fan-out, five
  ambiguous expressions, wildcard, counted quantifier, negated class) under the
  same check, against an independent reference matcher; five
  non-deterministic automata through the set-valued constructor, each under
  `Upfront` and `PerCall`, including the #1204 and #1203 shapes and
  `nonfinal_sibling`; four duplicate-variable shapes under plain
  `solve_for_tests`. With and without proofs; VeriPB runs when it is on the
  path. Seeded (`--seed`).
- **`regular_legacy_test`**: 13 of the deterministic shapes (not the two
  1-based alphabets) and eight regex shapes under `PerCall`, plus duplicates.
- **`regular_bacchus_test`**: seven deterministic shapes under `Bacchus`, with
  per-node GAC; no empty sequence, no regex (refused).
- **`regex_test`** (Catch2): the compiled NFA against the reference matcher on
  every word up to a length, for each syntax feature.
- **`canonical_run_test`** (Catch2): `regular_is_ambiguous` on deterministic,
  split-and-fail, split-and-meet, domain-dependent and length-dependent cases.
- **`scp_chain_regular_*`**: three deterministic cases; see [Cake
  conformity](#cake-conformity).
- **MiniZinc:** `regex.mzn` (a hand-built table, `q0 = 1`), `nurses.mzn`.
  **XCSP3:** `regular.xml`, `regular_nfa.xml`.
- **Audit lane:** the three rows above.

**Runtime caps.** No lane sets or clears one. The default caps (300 solutions,
1,500 recursions) **do not fire**: the largest expected count is 27 solutions
in `regular_test` and 19 in the other two, so the capped run checks the whole
tree (`GCS_TEST_MAX_SOLUTIONS=300 GCS_TEST_MAX_RECURSIONS=1500 <test>
--seed=1` at `86caad24`; `tmp/fd-dd/regular/tests/`). `regular_test` runs 80
solves there, 40 with proofs, in 0.75 s; `regular_legacy_test` 50 (25),
`regular_bacchus_test` 14 (7).

**Tightness:** no mutation lane; see rule 2 for the hand mutations.

**What the tests do not cover.**

- **Any assertion level.** Every proof in the suite is at `Off`, which is how
  #1332 went unnoticed: `nonfinal_sibling` is in `regular_test` and passes
  there, and fails under any non-`Off` `GCS_ASSERTION_LEVEL`. No lane sets
  that variable, and no CI job does.
- **The every-level scaffolding above `Links`** (#1330), over a range or a
  view whose bounds unit propagation cannot recover: no lane runs above
  `Off`, the view lanes run the deterministic data only, and the
  regex and NFA shapes' domains (`0..1`, `0..2`, `1..3`, `{1, 3}`) run only
  at `Off`.
- **`Bacchus` with an empty sequence**, or with an instance that needs one of
  the missing unit clauses (#1329 and #1331). Two of its seven shapes have two
  final states; neither needs one.
- **Search over a declared domain wider than the alphabet** (#1339).
- **A start state other than 1 through MiniZinc** (#1328): `regex.mzn` and
  `nurses.mzn` both use `q0 = 1`, and no test uses the enum form.
- **Out-of-range state numbers** (#1333).
- **Holey initial domains** for the per-node GAC check: none of the tests has
  one (the "1-based alphabet with a hole" shape has its hole in the transition
  table, over `1..3`); branching makes holes, and the sweeps here cover holey
  domains.
- **Wide domains**, the regex alphabet, and any domain narrower than the
  alphabet in a chain case (#489).
- **A non-deterministic automaton in a chain case or through the `.scp`
  reader** (#1335).
- **Real instances:** none ported. `examples/nonogram` reads Challenge data
  files but is not a test.

### Benchmarks and examples

- **In the repository:** `examples/regular_random` (random automata;
  `--legacy`, `--bacchus`, `--all`) and `examples/nonogram` (one `Regular` per
  line; `--random N`, `--dzn`, `--all`, and the same strategy flags).
  [`benchmarking.md`](../benchmarking.md) notes that `regular_random` does
  almost no search in its default first-solution mode and recommends `--all`;
  [`proof-benchmarks.md`](../proof-benchmarks.md) finds that `--all` has no
  usable size for proof checking (`-n 6` checks in under a second, `-n 7`
  takes over an hour), and that the nonogram size it tried does no search.
- **Corpus:** 20 of the 285 flattened MiniZinc Challenge models post
  `glasgow_regular`: `nonogram` (2011, 2012, 2013; 26 to 110 posts),
  `pentominoes` (2011, 2013, 2020, 2021; 10 each, automata of up to 400
  states), `elitserien` (2014, 2016, 2018, 2023), `traveling-tppv` (2014, 2017,
  2022), `rotating-workforce` (2018, 2019; one post over 182 positions),
  `rotating-workforce-scheduling` 2022 (101), `peacable_queens` (2021, 2024)
  and `work-task-variation` 2025, all with `q0 = 1`.
- **For CPU:** random nonograms with search, `reg_gcs nono 30 2 50` and
  `nono 35 1 50` (`tmp/fd-dd/regular/bench/`), against the Gecode twin
  `reg_gecode`; both explore the same number of nodes.
- **For proof verification:** `nono 25 1 50` (625 cells, 50 constraints, 25
  nodes; checks in about 3 s under `Upfront`) and `rdfa 12 6 3 1` (one
  constraint, 2,162 solutions; under half a second under `Upfront`, 12 s under
  `PerCall`). `nono 30 2 50` has 227 nodes and is the next size up.
- **Never uncapped:** the regex form over any wide domain (it does not
  install), and any Challenge nonogram with proofs at `--all` before measuring
  its size.

### CPU performance

*Release build of `86caad24` (GCC 15.2.0, `-O3 -march=native`); Gecode 6.3.0,
built locally; fataepyc-10, `taskset -c 12`, malloc thresholds fixed;
2026-10-10. The machine was shared with two other audits, so wall times are
inflated and noisy; decide on `instructions:u` (`perf stat`), which is
reproducible to six figures between runs. Median of three runs, proofs off.*

**Against Gecode, on the same nodes.** Random nonograms (`gen.hh`: a random
picture of the given density, one line automaton per row and column), all
solutions, input order, smallest value first; GCS's `Regular` against Gecode's
`extensional` with a `DFA`. Both are generalised arc consistent, and the
solution counts and node counts agree (GCS recursions = Gecode nodes; the
failure counters are defined differently and do not compare).

| instance | solutions | nodes | Gecode instr. | Gecode wall | GCS `Upfront` instr. | GCS wall | `PerCall` instr. | `Bacchus` instr. | ratio (instr.) |
|---|---|---|---|---|---|---|---|---|---|
| 25×25, seed 1 | 4 | 25 | 15.9·10⁶ | 0.010 s | 774·10⁶ | 0.40 s | 772·10⁶ | 764·10⁶ | 49 |
| 30×30, seed 2 | 8 | 227 | 92.9·10⁶ | 0.049 s | 11.54·10⁹ | 5.99 s | 11.53·10⁹ | 11.46·10⁹ | 124 |
| 35×35, seed 1 | 60 | 4,745 | 798·10⁶ | 0.345 s | 211·10⁹ | 99.2 s | — | — | 264 |

The ratio grows with the instance, as a per-node cost proportional to the
total graph size would. A `perf` profile of the 30×30 `Upfront` run
(`perf_nono30.data`) puts about 30% of the samples in copying a
`RegularGraph` and about 24% in destroying one, nearly all of it in the
allocator and hash-table assignment: the per-epoch constraint-state copy (see
[Mutable state](#mutable-state-and-incrementality)). That is a hotspot share,
not a saving; no fix was built. Filed as #1338. The stale per-value entries
of #1339 are part of what is copied when a declared domain is wider than
the alphabet; on these nonograms the domains are `0..1`, so they are not.

On a single random automaton with a three-value alphabet (`rdfa 14 6 3 1`,
13,574 solutions) GCS takes 0.60 s to Gecode's 0.013 s, one run each, but
GCS's search branches one child per value where Gecode's is binary, so the
node counts differ (24,087 against 27,147) and the pair is not a comparison.

**What the benchmark does not exercise.** Non-deterministic automata, the
regex form, holes in the initial domains, wide domains, repeated variables,
and proofs.

### Proof performance

*Same build and machine; VeriPB 3.0.2 with `--force-checked-deletion`; one run
each, wall time, on a shared machine (`tmp/fd-dd/regular/proof/`).*

| instance | strategy | lines, `Off` | bytes, `Off` | VeriPB, `Off` | lines, `Inferences` | bytes, `Inferences` | VeriPB, `Inferences` | `regular` assertions / all |
|---|---|---|---|---|---|---|---|---|
| `nono 25 1 50` | `Upfront` | 85,553 | 9.91 MB | 3.08 s | 1,079 | 0.66 MB | 0.09 s | 964 / 993 |
| | `PerCall` | 363,327 | 25.5 MB | 12.93 s | 3,442 | 1.39 MB | 0.15 s | 964 / 993 |
| | `Bacchus` | 148,700 | 12.4 MB | 4.27 s | 148,686 | 12.4 MB | 3.76 s | 0 / 29 |
| `rdfa 12 6 3 1` | `Upfront` | 30,939 | 2.74 MB | 0.42 s | 21,456 | 2.20 MB | 0.31 s | 1,974 / 7,977 |
| | `PerCall` | 134,272 | 10.2 MB | 12.06 s | 32,076 | 4.25 MB | 4.68 s | 1,974 / 7,977 |
| | `Bacchus` | 22,658 | 1.07 MB | 0.56 s | 18,697 | 1.72 MB | 0.43 s | 0 / 6,003 |

All verify (`s VERIFIED` at `Off`, `s UNDER ASSERTIONS` at `Inferences`).
`Upfront` is the smallest and fastest on the nonogram, as the design note
predicts; on the enumeration `Bacchus` is smaller and close in time. `PerCall`
is the slowest at **both** levels, and at `Inferences` its 4.68 s against
`Upfront`'s 0.31 s is not the justifications, which are asserted there: it is
the two permanent `red` lines per call for the short-reason flag, which every
later RUP pays for. The fact-check measured that: with
`with_short_reasons(false)`, `PerCall` on `rdfa 12 6 3 1` at `Inferences` is
21,456 lines and 0.31 s against 32,076 lines and 4.52 s with it on (the
difference is 10,620 `red` lines, two per call for 5,310 calls), and at `Off`
1.59 s against 11.95 s (`tmp/fd-dd/factcheck/regular/proof/q/`). `Bacchus`
writes its whole scaffold at every assertion level, so on the nonogram, a
shallow search, its `Inferences` proof is as big as its `Off` one; on the
enumeration it has fewer lines at `Inferences` (18,697 against 22,658) but
more bytes (1.72 MB against 1.07 MB). The backtracks are about the same size
either way (RUPs at `Off`, assertions at `Inferences`); the growth is in the
solution lines, `solx` spelt over the bits (305 KB to 580 KB) plus an asserted
`solx_block` line per solution (2,162 lines, 415 KB), and the fewer lines come
from the `core id` lines and the scaffold RUPs that `Off` writes. The 4.68 s
in the table and the fact-check's 4.52 s are separate runs of the same cell.

**Own contribution against the shared layers**, by line shape
(`classify.py`, approximate: lines are classed by their shape and the comment
before them):

- `nono 25 1 50`, `Upfront`, `Off`: root backward chains 48,450 lines (57%;
  2.76 MB, 28%), root static dead lines 18,230 (21%; 0.55 MB), per-call
  dead-state lemmas about 8,800 lines (10%) but 5.76 MB (58%), because each
  carries the whole-scope reason; value prunings and backtracks about 2,200
  lines; the literal layer and bookkeeping (`red`, `pol`, `core`, `del`) about
  7,600 lines. So on a shallow search the root scaffold is most of the lines,
  and the reasons most of the bytes.
- `PerCall`, same instance: per-call lemmas 338,180 lines (96.5%).
- `rdfa 12 6 3 1`, `Upfront`: the family's own lines are the 5,028 per-call
  lemmas and a few hundred root lines; the rest is the enumeration's
  solution, backtrack and bookkeeping lines (about 19,500), mostly the shared
  part, though 1,717 of them are `del range` lines deleting the family's own
  `Current` lemmas.

The OPB split against width is under [OPB encoding](#opb-encoding): for ten
variables of width `W` under a two-symbol automaton, the constraint's own
`24 + 20W` rows against the literal layer's `4(W+1)` rows per variable.

**Measured elsewhere, not to be mixed with the above.** The design note
[`regular.md`](../regular.md) and
[`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md)
give `Upfront` against `PerCall` as 13 to 55 times smaller and 2.3 to 7 times
faster to check (9 MB against 496 MB, 1.66 s against 11.69 s at 7,660
solutions), and `Bacchus` against `Upfront` on `regular_random`, measured on
the decision-diagram PR stack (#210 to #213) before #1266. The canonical
run's costs in the design note (12.3 s for `"(0|1)* 1 (0|1)*"` over 160
variables, against 11.5 s determinised; a blow-up case at 0.6 s against 26
minutes determinised) were measured on 2026-10-05 for #1266. None was re-run
here.

## Status, gaps, and next steps

### Proof-logging gaps

- **`Bacchus`: rejected re-derivations** when a pruning rests on a state that
  one of the three missing unit clauses would rule out: 7 of 1,300 random
  proofs here, 63 of 10,000 in the fact-check's sweep, some with a single final
  state; rejected wherever the backtracks are real RUPs (`Off`,
  `Definitions`, `Links`), and one of the fact-check's seeds (2833) at a
  scaffold RUP at every level (#1331). By design it logs no pruning; the published encoding's
  unit clauses would make that sound, and with all three patched in the
  fact-check's sweep has no rejection.
- **`Upfront` above `Off`: rejected solution lines** for a non-deterministic,
  unambiguous automaton, because the static dead lines are skipped (#1332).
  6 of 100 random NFAs at `Inferences`. `PerCall` had none at any level in the
  fact-check's sweep without views, because that sweep declared its variables
  from value lists, which #1330 does not affect.
- **At `Inferences` and `Backtracking`: rejected root scaffolding** under
  every strategy that writes some at every level: the canonical run
  (`Upfront`, `PerCall`), `PerCall`'s static dead lines and `Bacchus`'s
  encoding, whenever a sequence variable declared as a range has bounds unit
  propagation cannot recover (`1..2`, `-1..2`, `-5..9`), or a view's own range
  is such a range (#1330); a variable declared from a value list is not
  affected. The cause is the boundary pins the tracker omits above `Links`;
  inserting the two pins per variable makes every failing shape accepted. In
  the fact-check's sweep with views, 7 of 150 NFA `PerCall` proofs and 9 to 10
  of 150 NFA `Upfront` proofs are rejected at each of those levels. The ten
  other families the fact-check tried, with views, are accepted there, since
  they gate their scaffolding to `Off`; the closest relative is #1067.
- **No unchecked assertion** at `Off` under any strategy, and no bare unit
  clause at the assertion levels: every `Upfront` and `PerCall` assertion
  carries its reason (or its reason's flag).
- **The propagator is the same with proofs on or off**, under every strategy.

### Known limitations

- **Through MiniZinc, a `regular` whose start state is not the first state
  gives wrong answers,** including any enum-typed automaton whose start is not
  the first enum value, and on MiniZinc 2.10.1 a reified `regular` (#1328).
- **`Bacchus` accepts an empty sequence** whose start state is not final
  (#1329), and its proofs can be rejected (#1331). It is a benchmarking
  option; no front end selects it.
- **A malformed automaton crashes** rather than being refused (#1333).
- **A repeated variable propagates less than it could** (each position is
  independent); no solution is lost.
- **Wide declared domains do not install**: the OPB is per value (#841), and so
  are the root passes and the root's pruning lines. The regex form fails on any
  wide variable (#1227, and this audit's comment on it).
- **It is far slower per node than Gecode** (49 to 264 times the instructions
  on nonograms), because its graph is copied at every node (#1338), and
  every node costs time linear in the declared width of the domains, even
  after the root has cut them down to the alphabet (#1339).
- **Above `Links`, the proof can fail** under the canonical run, `PerCall`'s
  NFA scaffold or `Bacchus`, for a sequence variable declared as a range such
  as `-1..2`, or a view whose own range is one (#1330).
- **A `.scp` holding a non-deterministic automaton cannot be read back**
  (#1335).
- **`PerCall`'s proofs grow the permanent database by two lines per call**,
  which shows at every assertion level.

### Next steps

0. **Fix the MiniZinc start state** (#1328). Apply one permutation to rows,
   targets and `F`, or prepend a fresh start state copying `q0`'s row; add a
   `minizinc/tests` case with `q0 ≠ 1`, one with the enum form and one
   reified. Small, and the only wrong answer a front end reaches.
1. **Give `Upfront` the static dead lines at every level for an NFA**
   (#1332): call `emit_regular_static_dead_states` from `Upfront`'s
   initialiser for a non-deterministic, unambiguous automaton when the level
   is not `Off` (at `Off` `emit_top_scaffolding` writes those lines already).
   Small; the fact-check's patch of exactly that had no rejection in 3,800
   proofs, but over variables declared from value lists, which #1330 does not
   affect: the pass is a
   domain collapse, so above `Links` it needs #1330's pins (as `PerCall`'s
   copy of it already does). Add an `Inferences` run of the NFA cases to
   `regular_test`.
2. **Repair `Bacchus`** (#1329 and #1331): #254's empty-sequence check, and
   the three unit clauses of the published encoding (#215): `¬s[i][q]` for a
   state with no outgoing transition, the same for one with no incoming
   transition, and `¬s[n][q]` for a non-final state. Small, but above `Links`
   the first of them is a domain collapse that needs the boundary pins of
   #1330 (or `Bacchus`'s scaffold gated to `Off`). Or retire the strategy,
   which no front end selects; the design note
   [`regular.md`](../regular.md) keeps it for #200.
3. **Stop copying the graph at every node** (#1338). Flat arrays with degree
   counters first (a copy becomes a few `memcpy`s), then a trail of removed
   edges restored on backtrack (#364's survey has the pattern); separately,
   scan only the positions the trigger reports, and build the reason only when
   something will read it. With it, look values up with `find()` rather than
   `operator[]` (#1339, the same fix as `MDD`'s), which is a one-line change
   per site and removes the width from every node. Moderate. On the nonograms
   here the copy is about
   half the profile, and the gap to Gecode is two orders of magnitude, so this
   is the family's main performance item. Each step wants the solution
   sequence and node counts checked unchanged.
4. **Validate the automaton** (#1333) in each constructor and the `.scp`
   reader. Small.
5. **Read non-deterministic automata from `.scp`** (#1335) and add an NFA
   chain case. Small.
6. **Width** (#841, #1227 and this audit's comment on it): out-of-alphabet values as a range row per
   gap rather than a row per `(state, value)`, the root pruning of those values
   as range inferences, and the regex alphabet built as an interval and only
   when `.` or `[^…]` needs it. Moderate; #841 lists what VeriPB has to accept
   first. The regex alphabet was not filed separately: it is this audit's
   comment on #1227.
7. **`PerCall`'s short-reason flag on every call**: define it only when
   something is inferred, or delete it after the call. Small, and the same
   change `smart_table` (#1120, which this audit commented on) and `Circuit`
   (#1317) want; not filed separately. Separately, its in-degree
   lemmas' per-value lines name the wrong variable and are dead weight (rule
   2); worth a mutation check before dropping them. Not filed.
8. **A test lane at the assertion levels**, for every strategy, with views
   and ranges such as `-1..2` in the regex and NFA shapes, so that the next
   shape of #1331, #1332 and #1330 shows up. Small. #1330 itself wants a decision
   first, between two options: have the tracker emit the boundary pins at every
   level (two RUP lines per variable, for every family), or gate `Regular`'s
   every-level scaffolding to `Off` and say what replaces it above `Links`,
   where solution lines need it. The lane itself is not filed.
9. **Minimal reasons.** A pruning depends only on what has gone from the
   domains; the whole-scope reason is what makes `Upfront`'s per-call lemmas
   58% of the nonogram proof's bytes. The right subset is the edges' killing
   literals, which the cascade knows; per the arc's standing rule, which
   literals are needed is for the justifier to show. Moderate. Not filed;
   the always-true declared-bound literals in the same `generic_reason` are
   part of this audit's comment on #1070.
10. **Claim idempotence on distinct variables.** Return
    `PropagatorState::EnableButIdempotent` from all three copies of the
    propagator; `Propagators` already ignores the claim when two trigger
    positions alias one variable (`propagators.cc:111-129`, `:777-780`), which
    is the case where it would be false. Small. It removes the requeue after
    every call that infers anything; `mdd.md` measured the same change on
    `MDD`'s copy of this code (26% fewer calls, 0.9% fewer instructions), so
    the gain is probably small. It wants a check that the solution sequence
    and node counts are unchanged, and an idempotence-checker run. Not filed.

## Prior art

- **Propagation.** Pesant (*A Regular Language Membership Constraint for
  Finite Sequences of Variables*, CP 2004, LNCS 3258, 482–495) gives the
  layered-graph algorithm with forward and backward passes and incremental
  degree maintenance, domain consistent in `O(n · |Q| · |Σ|)`; this
  propagator is his, with the graph restored by copying. Whether Pesant's
  paper treats non-deterministic automata was not checked here. Quimper and
  Walsh's *Global Grammar Constraints*, in the 15-page version on Walsh's
  site (`cse.unsw.edu.au/~tw/comic-2006-005.pdf`, which by its file name is
  their technical report COMIC-2006-005; the PDF itself carries no report
  number), the long version of their CP 2006 short paper of the same title,
  751–755, whose text was not checked, does, in §4 ("NFA constraint"): it
  encodes an NFA-specified `Regular` as
  a Berge-acyclic chain of ternary constraints on which GAC gives GAC, in
  `O(nT)` for `T` transitions. Running Pesant's graph over several targets per
  value is that observation applied, not something claimed here as new;
  `Upfront` and `PerCall` support it, and `Bacchus` refuses a
  non-deterministic automaton.
- **Decompositions.** Bacchus (*GAC via Unit Propagation*, CP 2007, LNCS 4741,
  133–147) gives the clausal encoding with transition variables on which unit
  propagation achieves GAC; `proof_strategy::Bacchus` derives it in the proof
  from the natural encoding, as McIlree's Encoding Procedure 5.2 states it and
  #215 specified it, but without three of its kinds of unit clause (#1331).
- **Certification.** McIlree and McCreesh (*Proof Logging for Smart Extensional
  Constraints*, CP 2023, LIPIcs 280, 26:1–26:17) certified `Regular` for the
  first time, and McIlree's thesis (*Pseudo-Boolean Proof Logging for
  Constraint Propagation Algorithms*, Glasgow, 2026, Chapter 5, §5.1) gives the
  encoding (EP 5.1), the Bacchus alternative (EP 5.2) and the justification
  procedures (JP 5.1, 5.2, 5.5; JSP 5.3, 5.4) for a deterministic automaton,
  with the GCS implementation that is now `PerCall`. Gocht, McCreesh and
  Nordström's auditable solver (CP 2022) does not cover it, as far as its
  abstract shows.
- **The derivation's shape is published.** Dead states by RUP, then values by
  RUP, is CP 2024 §3.3's (Demirović, McCreesh, McIlree, Nordström, Oertel and
  Sidorov, LIPIcs 307), which itself says it closely resembles McIlree and
  McCreesh's CP 2023 steps for `Regular`.
- **What is this solver's.** Two things, each as far as this audit knows
  unpublished:
  - **The upfront strategy**: the per-value backward chains derived once at the
    root and kept at `Top`, with a per-search-path cache of the per-call
    dead-state lemmas. It is
    [`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md)'s
    "upfront" strategy, landed for `Regular`, `MDD`, `Knapsack` and `BinPacking`
    in one PR stack (#210, #211, #212, #213). It is claimed here once, for the
    solver; [`mdd.md`](mdd.md) and [`knapsack.md`](knapsack.md) describe their
    instances and point here.
  - **The canonical run** (#1266), which pins an ambiguous automaton's state
    flags to one accepting run by a single redundance step over guard flags,
    so that a solution line is unit-propagation complete without determinising
    the automaton. The thesis's encoding and proofs assume a deterministic
    automaton, for which the flags are the run.

## Further reading

- [`regular.md`](../regular.md): the design note. The three strategies and why
  `Upfront` is the default, the encoding, the ambiguity analysis and the
  canonical run's derivation step by step, `Upfront`'s and `Bacchus`'s root
  scaffolds, benchmark tables for all three on `regular_random`, and a usage
  note (command lines, no figures) for `nonogram`. Against the code at
  `86caad24` it is wrong in these places, for an out-of-stack fix:
  - it says the OPB is identical across all three strategies (`Bacchus` names
    its flags and labels its rows differently);
  - it says the choice "never changes the inferences drawn or the solutions
    found" (`Bacchus` accepts an empty sequence whose start is not final,
    #1329);
  - it says `Bacchus`'s backtrack RUPs close by unit propagation (not without
    three kinds of unit clause, #1331);
  - it says `Upfront`'s scaffold is emitted "only if proof logging is enabled",
    leaving out that it is also only at `Off` (#1332);
  - it says `Bacchus`'s per-call propagator "is passed `logger = nullptr`"
    (it is passed the logger, `regular_bacchus.cc:209`);
  - it says the graph is built "once in `prepare()`" and that each call
    "builds the per-call support graph" (it is built at the first call and
    then maintained, `regular.cc:308-309`);
  - it counts `Bacchus`'s incoming at-least-ones as one per `(i+1, q')` and
    its variable-support ones as one per `(i, v)` with `v` in the initial
    domain (each is skipped when no transition exists, `regular_bacchus.cc:414`,
    `:432`, and the second runs over the OPB alphabet);
  - it calls the sibling classes internal, while their headers are installed
    and the audit lane posts them.

  And `regular.hh:103-104` says `Bacchus` "requires every such set to have at
  most one member", where an empty set is refused too (`regular.cc:563`).
- [`decision-diagram-proof-strategies.md`](../decision-diagram-proof-strategies.md):
  the cost model shared with `MDD`, `Knapsack` and `BinPacking` (and with
  [`mdd.md`](mdd.md) and [`knapsack.md`](knapsack.md)): displacement against
  the permanent scaffold's tax, the per-family defaults, and the negative
  results on deleting scaffolding and on flat RUP hints. One correction for
  its out-of-stack list, with the others `mdd.md` and `knapsack.md` record:
  its reason for `Regular`'s default, a narrow automaton and so a tiny
  permanent scaffold (`red ≈ 28–48` flags), does not hold on nonograms, where
  `Upfront`'s scaffold has no `red` lines and is 66,680 of 85,553 lines (see
  [Options](#options)); the conclusion survives, on line count.
- [`justification-techniques.md`](../justification-techniques.md): Theorems
  2.6 and 3.2, which every step here leans on.
- [`large-domains.md`](../large-domains.md): the `Regular` rows of the
  encoding survey and #841's proposed re-encoding.
- [`all_different.md`](all_different.md): `recover_am1_from_pairs`, which the
  canonical run calls.
