# `s_exprify` → `s_expr` (structured `.scp` terms) — complete

## What this was

A constraint's `.scp` entry used to be produced by `Constraint::s_exprify()`, a
hand-built string (the body of the `(name op args...)` list, without the
enclosing parentheses; `write_scp` added them). Every constraint did its own
string formatting, which gave inconsistent spacing and nothing for a `.scp`
*reader* to share.

It now comes from `Constraint::s_expr()`, which returns the term as a structured
`innards::SExpr` (the full `(name op args...)` list). Stringification happens
once, centrally, in `innards::write_scp` (`gcs/innards/proofs/scp_writer.cc`),
the sole `.scp` serialiser. The structured term is also what the `.scp` reader
produces, so writer and reader share one representation and compare directly
(`parse_s_expr(line) == c.s_expr()`). Output is canonical (single line,
single-space) regardless of how a term is built.

## Status: complete

`Constraint::s_expr()` is now **pure virtual** — every constraint overrides it —
and the legacy `s_exprify()` method plus the transitional bridge (which derived
each form from the other) have been removed (`gcs/constraint.hh`,
`gcs/constraint.cc`). `write_scp` was already off `s_exprify()`, so nothing
changed there.

To build a term, use `innards::SExpr::list({...})` and `SExpr::atom(...)`, with
`NamesAndIDsTracker::s_expr_term_of(...)` for operands — it has overloads for an
`IntegerVariableID`, a `Literal` (the and/or/parity inputs), and a
`ReificationCondition` (returns `nullopt` when unconditional). Integer atoms are
`SExpr::atom(value.to_string())`. See `abs.cc` (simple) and `in.cc` (sub-lists)
for the canonical shape.

### Suspect forms resolved (not enshrined)

- **`GACArithmetic` double parentheses** — the old `s_exprify()` returned
  `(name op ...)` *with* its own outer parens, so `write_scp` double-wrapped it to
  `((name op ...))`. `s_expr()` returns the single proper list, fixing it.
- **`element`** — keeps the corrected form `s_exprify()` had reached: a bare varc
  list `(X0 ... Xn-1)` (and `((row) (row) ...)` for `element_2d`) plus a
  space-separated `(var offset)` index, then the result.
- **Multi-line tabular constraints** (`table`, `negative_table`, `smart_table`,
  `regular`, `knapsack`, `sort`, `arg_sort`) — built as nested `SExpr` lists;
  `write_scp` renders them on one canonical line (as the bridge already did).

## Bugs surfaced by routing the writer through the parser

- **`inverse`, `arg_sort`** emitted a stray trailing `)` (they hand-wrote the
  closing paren that `write_scp` also adds), leaving the `.scp` unbalanced —
  harmless only because nothing parsed it. Fixed during the bridge work; the
  structured form is balanced by construction.
