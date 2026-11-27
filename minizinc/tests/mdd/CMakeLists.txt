gcs_minizinc_test(minizinc-mdd basic.mzn true true)

# The shapes a front end can misread (#1006): fzn-glasgow regroups MiniZinc's
# nodes by level, so nodes numbered out of level order, an unreachable node, a
# dead end, an empty label, labels with holes and negative values, a single
# variable, and a repeated variable with a constant. --fzn-count insists all
# three reached the builtin; MiniZinc's default solver has its own mdd, so
# --reference-std adds the standard library's decomposition.
gcs_minizinc_test(minizinc-mdd-shapes shapes.mzn true true
    OPTIONS --fzn-count 3 glasgow_mdd --reference-std)

# Reified, half-reified and negated calls, which reach the standard library's
# decomposition and only need to flatten and agree; the one plain call is
# counted.
gcs_minizinc_test(minizinc-mdd-reif reif.mzn true true
    OPTIONS --fzn-count 1 glasgow_mdd --reference-std)
