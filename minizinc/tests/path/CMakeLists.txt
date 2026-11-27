# path and dpath ride one reachability encoding plus counting rules rather than the
# stdlib's distance labelling, and bounded_dpath rides those in turn through the
# stdlib's own wrapper. Each guard names the builtin that must appear in the
# flattened model, because without one the test would pass vacuously against
# the decomposition.
gcs_minizinc_test(minizinc-path basic.mzn true true OPTIONS --fzn-pattern glasgow_path)

gcs_minizinc_test(minizinc-dpath dpath.mzn true true OPTIONS --fzn-pattern glasgow_dpath)

gcs_minizinc_test(minizinc-bounded-dpath bounded_dpath.mzn false true OPTIONS --fzn-pattern glasgow_dpath)
