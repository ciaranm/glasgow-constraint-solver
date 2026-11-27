# path and dpath ride one reachability encoding plus counting rules rather than the
# stdlib's distance labelling, and bounded_dpath rides those in turn through the
# stdlib's own wrapper. Each guard names the builtin that must appear in the
# flattened model, because without one the test would pass vacuously against
# the decomposition.
gcs_minizinc_test(minizinc-path basic.mzn true true OPTIONS --fzn-pattern glasgow_path)

gcs_minizinc_test(minizinc-dpath dpath.mzn true true OPTIONS --fzn-pattern glasgow_dpath)

gcs_minizinc_test(minizinc-bounded-dpath bounded_dpath.mzn false true OPTIONS --fzn-pattern glasgow_dpath)

# More of the shapes a front end can misread (#1006): the redefinitions shift
# the endpoints, the source and the target by min(index_set(ns)), or by 1 for
# the N-and-E spelling. Several shapes to a model, so --fzn-count guards each,
# and --fzn-pattern checks that a variable the model equates really does reach
# the builtin twice. --reference-std adds the standard library's
# decomposition.
gcs_minizinc_test(minizinc-path-shapes shapes.mzn true true
    OPTIONS --fzn-count 4 glasgow_path --reference-std
        --fzn-pattern "glasgow_path\".*\"(X_INTRODUCED_[0-9]+_)\", \"\\1\"")

gcs_minizinc_test(minizinc-path-dpath-shapes dpath_shapes.mzn true true
    OPTIONS --fzn-count 4 glasgow_dpath --reference-std
        --fzn-pattern "glasgow_dpath\".*\"(X_INTRODUCED_[0-9]+_)\", \"\\1\"")

# No nodes, through the enum spelling: unsatisfiable, and the flattener says so
# before any solver runs, so there is no proof to check. These are the guard
# against a `then true` copied into the rooted redefinitions (#1305).
gcs_minizinc_test(minizinc-path-empty empty.mzn true false OPTIONS --unsatisfiable)

gcs_minizinc_test(minizinc-path-dpath-empty dpath_empty.mzn true false OPTIONS --unsatisfiable)
