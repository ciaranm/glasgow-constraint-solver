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

# More shapes beyond minizinc-argsort-shapes (#1006): a negated call, integer
# literals in p, a par x with a tie, and an enum-valued x. As there, MiniZinc's
# default solver already runs the stdlib decomposition, so there is no
# --reference-std.
gcs_minizinc_test(minizinc-argsort-moreshapes more_shapes.mzn true true
    OPTIONS --fzn-count 3 glasgow_arg_sort_int)

# The same variable twice in p, which can be no permutation. The pattern checks
# that p reached the builtin with the repeat.
gcs_minizinc_test(minizinc-argsort-aliased aliased.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern glasgow_arg_sort_int
        --fzn-pattern "\\[\"q\", \"q\"\\]")
