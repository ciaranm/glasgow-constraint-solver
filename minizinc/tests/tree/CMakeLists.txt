# tree and dtree ride one reachability encoding plus counting rules rather than the
# stdlib's distance labelling, and steiner rides those in turn through the
# stdlib's own wrapper. Each guard names the builtin that must appear in the
# flattened model, because without one the test would pass vacuously against
# the decomposition.
gcs_minizinc_test(minizinc-tree basic.mzn true true OPTIONS --fzn-pattern glasgow_tree)

gcs_minizinc_test(minizinc-dtree dtree.mzn true true OPTIONS --fzn-pattern glasgow_dtree)

gcs_minizinc_test(minizinc-steiner steiner_tree.mzn false true OPTIONS --fzn-pattern glasgow_tree)
