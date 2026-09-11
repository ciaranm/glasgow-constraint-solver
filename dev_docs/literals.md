# What a literal is: the unified account

The theory of the literal layer — what an order, equality or range atom *is*,
what clauses hold the layer together, and why unit propagation can be relied on
to re-derive a solver fact during a backtrack-clause replay — lives in one
document:

- **[literal-encodings.tex](literal-encodings.tex)**, 34 pages when typeset.

It is a revised and extended version of §3.2 and §3.3 of Matthew McIlree's
thesis, covering the two things the thesis does not: **range ("in") literals**,
and **several views of one variable**. It keeps the thesis's
numbering, so Theorem 3.3 is still "complete propagation of implied atomic
literals" and Inv1/Inv2/Inv3 are still the invariants they were there.

Build it with `latexmk -pdf dev_docs/literal-encodings.tex`; the .pdf is not
checked in.

## What is in it

| | |
|---|---|
| §3.2 | The encoding procedure, extended with *view variables* (a registered view is an encoded variable with a definitional link `V − sX = c`) and a third kind of atomic variable (`[X ∈ a..b]`, reified against two order cuts, width-1 being the eq atom). |
| §3.3.1 | The nine invariants of the literal layer, the definition of a *defined domain* over a whole view family, and the reproved Theorems 3.2 and 3.3 with their family versions 3.2′ and 3.3′. |
| "How facts move" | A table of every crossing and the clause family that carries it. Start here if you only read one page. |
| §3.3.2–4 | Backtracking, optimality and enumeration, with the preserved set pinned down (base bits only). |
| Interlude | The P1/P2 distinction, the W1–W9 witness suite and its ablation matrix, the coincidence trap, and the cost model. |
| Appendices | A worked example; residues and open questions; the design rationale (why a binary encoding, why equality and interval atoms rather than conjunctions of inequality atoms, why a view gets its own variable); the refuted designs, each with the witness that catches it. |

## Where each invariant lives in the code

All in `gcs/innards/proofs/names_and_ids_tracker.cc` unless noted.

| Invariant | Maintained by |
|---|---|
| `Inv-Chain`, `Inv-Bound` | `need_gevar` (the chain `pol`s, and `fix_bound`) |
| `Inv-Thresholds` | `define_plain_invar`'s two `need_gevar` calls; `need_all_proof_names_in` on an eq atom's reification |
| `Inv-Part` | `init_interval_partition`, `ensure_partition_cut`, and `need_direct_encoding_for`'s singleton splits |
| `Inv-Cover` | the three `emit_rup_proof_line` covering emissions in `ensure_partition_cut`, `init_interval_partition`, `define_invar_with_covering` |
| `Inv-Cont` | `link_immediate_containment` |
| `Inv-View` | `need_view`'s backfill; the view hooks in `need_gevar` and `need_direct_encoding_for`; `mirror_invar_across_view_link` |
| `Inv-Name` | `need_invar` (outside the definition guard) and `xliteral_for_ensuring` |
| `Inv-Conflict`, `Inv-Domain` | the solver: every inference is logged eagerly, every backtrack writes its clause |

## The companion documents

These cover the *implementation*, and defer to the document above for the
theory:

- [range_literals_spec.md](range_literals_spec.md) — what was built, in what
  order, which witness test guards what, and the edge-case inventory. Its
  section numbers are cited from the code; don't renumber them.
- [view-range-literals.md](view-range-literals.md) — issue #882's record: where
  the naming trigger lives in the code, the measured role divergence between the
  two sides, and the residue.
- [view-proof-logging.md](view-proof-logging.md) — working with views as a
  propagator author: `pol` cancellation, big-M sizing, the test harness. Its
  three numbered invariants are cited by number from `difference-logic.md` and
  from `difference_constraints.cc`.

Between them and the document above the rule is: **statements, arguments and
measured numbers live in `literal-encodings.tex`; function names, test names,
dates and decisions live in the Markdown.** A number in two places is a number
that will disagree with itself.

## Further reading

Matthew McIlree, *Pseudo-Boolean Proof Logging for Constraint Propagation
Algorithms*, PhD thesis, University of Glasgow, 2026.
<https://theses.gla.ac.uk/86049/> — that is the exact title; it is not "Proof
Logging for Constraint Programming", which is the title of its chapter 3.
