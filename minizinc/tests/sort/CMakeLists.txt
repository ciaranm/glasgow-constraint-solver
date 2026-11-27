gcs_minizinc_test(minizinc-sort basic.mzn true true)

# The shapes a front end can misread for sort (#1006): different index sets on
# the two sides, empty and single-element arrays, integer literals and repeated
# variables, enums and the function form. The count insists that each reached
# the builtin; --reference-std adds the standard library's decomposition, since
# MiniZinc's default solver has its own sort.
gcs_minizinc_test(minizinc-sort-shapes shapes.mzn true true
    OPTIONS --fzn-count 6 glasgow_sort --reference-std)

# Reified, half-reified and negated sort. The stdlib's reified decomposition
# posts sort through its function form, at the root, so all three reach the
# builtin and the count says so.
gcs_minizinc_test(minizinc-sort-reif reif.mzn true true
    OPTIONS --fzn-count 3 glasgow_sort --reference-std)
