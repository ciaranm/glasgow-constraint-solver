gcs_minizinc_test(minizinc-knapsack basic.mzn false true)

# The shapes a front end hands knapsack (#1006), several to a model, so
# --fzn-count insists that each reached the builtin, and enumerated, where the
# lane above only compares an optimum. Native Gecode has no knapsack of its
# own, so the default solver already is the standard library's decomposition.
gcs_minizinc_test(minizinc-knapsack-shapes shapes.mzn true true
    OPTIONS --fzn-count 4 glasgow_knapsack)
