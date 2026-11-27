gcs_minizinc_test(minizinc-tablebool bool.mzn true true)

gcs_minizinc_test(minizinc-tableint int.mzn true true)

# Duplicate rows, which MiniZinc keeps: every solution is matched by two rows,
# and the proof's solution lines used to fail (issue #1115). One enumerates
# (solx), the other optimises (soli).
gcs_minizinc_test(minizinc-tableintduplicates int_duplicates.mzn true true
    OPTIONS --fzn-pattern glasgow_table_int)

gcs_minizinc_test(minizinc-tableintduplicatesopt int_duplicates_opt.mzn false true
    OPTIONS --fzn-pattern glasgow_table_int)

# The shapes a front end can misread (#1006). glasgow_table_int and
# glasgow_table_bool receive the scope and the table flattened row by row,
# and fzn-glasgow cuts the table back into rows of the scope's length, so each
# model packs shapes where reading a row wrongly changes the answer: a single
# row, a scope and table indexed from somewhere other than 1, negative values
# and values outside the scope's domains, a variable repeated in the scope,
# constants in the scope, and an enum-indexed scope. --fzn-count insists that
# every call reached the builtin. MiniZinc's default solver has its own table,
# so --reference-std adds the standard library's decomposition as well.
gcs_minizinc_test(minizinc-table-shapes shapes.mzn true true
    OPTIONS --fzn-count 5 glasgow_table_int --reference-std)

gcs_minizinc_test(minizinc-table-boolshapes bool_shapes.mzn true true
    OPTIONS --fzn-count 3 glasgow_table_bool --reference-std)

# Reified, half-reified and negated tables. The standard library's
# fzn_table_int_reif builds a bigger table with the control variable as an
# extra column, and hands it to fzn_table_int, so three of the four calls
# reach glasgow_table_int (the single-variable one becomes set_in_reif). A
# reified Boolean table is an abort in the standard library for every solver,
# so there is nothing to test there.
gcs_minizinc_test(minizinc-table-reif reif.mzn true true
    OPTIONS --fzn-count 3 glasgow_table_int --reference-std)

# A table with no rows is unsatisfiable, and flattens to an empty table array
# that fzn-glasgow must still post, not skip. One model per type, since each
# type has its own redefinition.
gcs_minizinc_test(minizinc-table-empty empty.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern glasgow_table_int --reference-std)

gcs_minizinc_test(minizinc-table-emptybool empty_bool.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern glasgow_table_bool --reference-std)
