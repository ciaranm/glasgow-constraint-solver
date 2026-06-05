# Migrating `s_exprify` → `s_expr` (structured `.scp` terms)

## Where we are

A constraint's `.scp` entry used to be produced by `Constraint::s_exprify()`,
which returned a hand-built string (the body of the `(name op args...)` list,
without the enclosing parentheses; `solve()` added those). Every constraint did
its own string formatting, which gave inconsistent spacing and nothing for a
`.scp` *reader* to share.

We are moving to `Constraint::s_expr()`, which returns the term as a structured
`innards::SExpr` (the full `(name op args...)` list). The stringification then
happens once, centrally, in `innards::write_scp` (`gcs/innards/proofs/scp_writer.cc`),
which is the sole `.scp` serialiser — `solve()` just calls it. The structured
term is also what a future `.scp` reader will produce, so writer and reader share
one representation and can be compared directly (`parse_s_expr(line) == c.s_expr()`).

### Transitional bridge (current state)

`Constraint` declares both methods, each with a default that derives it from the
other (`gcs/constraint.cc`):

- `s_expr()` default: `parse_s_expr("(" + s_exprify() + ")")`
- `s_exprify()` default: `to_string(s_expr().as_list())` (body, no outer parens)

So a constraint overrides **exactly one**. Un-migrated constraints keep their
`s_exprify()` string override and get `s_expr()` via the bridge; migrated ones
override `s_expr()` and get `s_exprify()` for free. Overriding *neither* recurses
— don't (a constraint must define its `.scp` form somehow).

Because `write_scp` goes through `s_expr()`, **every** constraint's output now
passes through the parser, so it must be balanced, parseable s-expression text.
Output is also canonicalised (single line, single-space) regardless of how the
legacy string was formatted.

Migrated so far: `abs`, the reified comparisons, GAC/VC `all_different`, `in`.

## What's left

Migrate the remaining 37 `s_exprify` overrides to `s_expr()` (build an `SExpr`
instead of a string), then finish the cutover:

1. Migrate each remaining constraint (list below) to override `s_expr()`.
2. Resolve the **suspect forms** as they are migrated (don't enshrine them):
   - **`GACArithmetic` double parentheses** — its `s_exprify()` already returns
     `(name op ...)` *with* outer parens, so the writer double-wraps it to
     `((name op ...))`. The bridge preserves this faithfully today; fix it when
     migrating arithmetic (return the body, or a single list).
   - **`element` index form `_4,0`** — the comma-joined `elem,idx` atom is
     suspect and likely to change; decide its structured form when migrating
     `element`.
   - **Multi-line tabular constraints** (`table`, `smart_table`, `regular`,
     `knapsack`, …) currently emit pretty multi-line strings; via the bridge
     these are already canonicalised to one line. Confirm that's acceptable when
     migrating them.
3. Once **all** constraints override `s_expr()`:
   - Make `s_expr()` pure virtual.
   - Delete the bridge defaults and the `s_exprify()` method entirely (or keep a
     single non-virtual `to_string(s_expr())` convenience if any caller wants the
     string body).
   - `write_scp` is already off `s_exprify()`, so no change there.

## Bugs surfaced by routing the writer through the parser

- **`inverse`, `arg_sort`** emitted a stray trailing `)` (they hand-wrote the
  closing paren that `solve()` also adds), leaving the `.scp` unbalanced —
  harmless only because nothing parsed it. Fixed in this change.

## Remaining constraints (override still on `s_exprify`)

all_different_except, symmetric_all_different, all_equal, among, arithmetic
(Plus/Minus/Times/Div/Mod/Power — note double-paren above), at_most_one, circuit,
count, cumulative, disjunctive, disjunctive_2d, element (comma form), equals,
bounds/gac global_cardinality, increasing, inverse, knapsack, lex,
lex_smart_table, linear_equality, linear_inequality, logical, min_max, minus,
mult_bc, n_value, parity, plus, regular, seq_precede_chain, smart_table,
arg_sort, sort, negative_table, table, value_precede.
