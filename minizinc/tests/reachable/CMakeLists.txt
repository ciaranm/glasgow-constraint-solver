# The reachability family. --fzn-pattern is the reachability guard: MiniZinc's
# connected / dconnected wrappers go through reachable / dreachable, so without
# it a test would still agree with the reference solver via the stdlib distance
# labelling even if the override never fired.
gcs_minizinc_test(minizinc-reachable basic.mzn true true OPTIONS --fzn-pattern glasgow_reachable)

gcs_minizinc_test(minizinc-connected connected_undirected.mzn true true OPTIONS --fzn-pattern glasgow_reachable)

gcs_minizinc_test(minizinc-dreachable dreachable.mzn true true OPTIONS --fzn-pattern glasgow_dreachable)

gcs_minizinc_test(minizinc-dconnected dconnected.mzn true true OPTIONS --fzn-pattern glasgow_dreachable)

# More of the shapes a front end can misread (#1006): the redefinitions shift
# the endpoints and the root by min(index_set(ns)), or by 1 for the N-and-E
# spelling. Several shapes to a model, so --fzn-count guards each, and
# --fzn-pattern checks that a variable the model equates really does reach the
# builtin twice. --reference-std adds the standard library's decomposition.
gcs_minizinc_test(minizinc-reachable-shapes shapes.mzn true true
    OPTIONS --fzn-count 5 glasgow_reachable --reference-std
        --fzn-pattern "glasgow_reachable\".*\"(X_INTRODUCED_[0-9]+_)\", \"X_INTRODUCED_[0-9]+_\", \"\\1\"")

gcs_minizinc_test(minizinc-reachable-connected-shapes connected_shapes.mzn true true
    OPTIONS --fzn-count 2 glasgow_reachable --fzn-count 1 glasgow_dreachable --reference-std)

gcs_minizinc_test(minizinc-reachable-dreachable-shapes dreachable_shapes.mzn true true
    OPTIONS --fzn-count 3 glasgow_dreachable --reference-std)

# No nodes, through the enum spelling: unsatisfiable, and the flattener says so
# before any solver runs, so there is no proof to check. These are the guard
# against a `then true` copied into the rooted redefinitions (#1305).
gcs_minizinc_test(minizinc-reachable-empty empty.mzn true false OPTIONS --unsatisfiable)

gcs_minizinc_test(minizinc-reachable-dreachable-empty dreachable_empty.mzn true false OPTIONS --unsatisfiable)

# A fixed root that is not a node, which reaches Reachable as -1.
gcs_minizinc_test(minizinc-reachable-root-outside root_outside.mzn true true
    OPTIONS --unsatisfiable --fzn-count 1 glasgow_reachable)
