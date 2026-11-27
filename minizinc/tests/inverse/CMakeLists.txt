gcs_minizinc_test(minizinc-inverses basic.mzn true true)

# The index sets the three index-valued alldifferent-family globals were given
# in the model (#987): the flattened arrays are 1-based whatever the model's
# were, so the redefinitions pass them explicitly. --fzn-pattern is load-bearing,
# as for circuit: the stdlib decomposition agrees with the reference solver and
# verifies its proof whatever the builtin would have done.
gcs_minizinc_test(minizinc-inverses-offset offset.mzn true true OPTIONS --fzn-pattern glasgow_inverse)

# More of the shapes a front end can misread for the index-valued globals
# (#1006), several to a model, so --fzn-count guards each. The -negative lanes
# are the shapes MiniZinc's default solver gets wrong itself: its own inverse,
# which symmetric_all_different reaches through the stdlib, reports
# `Int::channel: Number out of limits` on a negative index set and calls an
# empty pair of arrays unsatisfiable. So those compare against the standard
# library's decompositions alone, and the others against both.
gcs_minizinc_test(minizinc-inverses-shapes shapes.mzn true true
    OPTIONS --fzn-count 4 glasgow_inverse --reference-std)

gcs_minizinc_test(minizinc-inverses-negative negative.mzn true true
    OPTIONS --fzn-count 2 glasgow_inverse --reference-std --skip-default-reference)

# Arrays of different lengths, which the redefinition turns into `false` before
# any builtin is posted. The default solver errors on the mismatch instead of
# reporting it, and the flattener never runs a solver on a model it has already
# found inconsistent, so there is no proof to check.
gcs_minizinc_test(minizinc-inverses-unequal unequal.mzn true false
    OPTIONS --unsatisfiable --reference-std --skip-default-reference)

# Two entries of one array equated, which MiniZinc flattens into the same
# variable twice. Each is unsatisfiable and used to be an error (#1047); the
# pattern checks that the array really did reach the builtin with a repeat.
gcs_minizinc_test(minizinc-inverses-aliased aliased.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern glasgow_inverse --fzn-pattern "\"(X_INTRODUCED_[0-9]+_)\", \"\\1\"")

# The reified and negated contexts, which go through the stdlib's
# fzn_inverse_reif and reach no builtin, but have to flatten for us at all.
gcs_minizinc_test(minizinc-inverses-reif reif.mzn true true OPTIONS --reference-std)

# Two arrays indexed from far apart and far from 1 (#1006).
gcs_minizinc_test(minizinc-inverses-large large.mzn true true
    OPTIONS --fzn-pattern glasgow_inverse --reference-std)
