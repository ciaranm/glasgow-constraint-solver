gcs_minizinc_test(minizinc-dag basic.mzn true true OPTIONS --fzn-pattern glasgow_dag)

# dag and the four-argument subgraph over an empty node set are true, so these
# models keep the solutions of their free variable (#1303). Nothing reaches a
# builtin, so there is no --fzn-pattern; --reference-std is the standard
# library's reading of the empty case.
gcs_minizinc_test(minizinc-dag-empty empty.mzn true true OPTIONS --reference-std)

# More of the shapes a front end can misread (#1006): fzn_dag.mzn shifts the
# endpoints by min(index_set(ns)). The subgraph posted alongside is counted
# too, and --fzn-pattern checks that the arcs the model equates really do reach
# the builtin as one variable twice. --reference-std adds the standard
# library's decomposition, which agrees once subgraph is posted.
gcs_minizinc_test(minizinc-dag-shapes shapes.mzn true true
    OPTIONS --fzn-count 3 glasgow_dag --fzn-count 2 glasgow_subgraph --reference-std
        --fzn-pattern "glasgow_dag\".*\"(X_INTRODUCED_[0-9]+_)\", \"\\1\"")
