gcs_minizinc_test(minizinc-argsort basic.mzn true true)

# As minizinc-inverses-offset.
gcs_minizinc_test(minizinc-argsort-offset offset.mzn true true OPTIONS --fzn-pattern glasgow_arg_sort_int)

# As minizinc-inverses-shapes. There is no --reference-std: MiniZinc's default
# solver has no arg_sort of its own, so it already runs the stdlib decomposition.
gcs_minizinc_test(minizinc-argsort-shapes shapes.mzn true true OPTIONS --fzn-count 5 glasgow_arg_sort_int)

# A reified and a half-reified arg_sort, which failed to flatten at all until
# the redefinition included the stdlib's reified decomposition: nothing else
# reaches that include, since every other lane posts arg_sort at the root.
gcs_minizinc_test(minizinc-argsort-reif reif.mzn true true)
