gcs_minizinc_test(minizinc-subgraph basic.mzn true true OPTIONS --fzn-pattern glasgow_subgraph)

gcs_minizinc_test(minizinc-subgraph-empty empty.mzn true true OPTIONS --reference-std)

# More of the shapes a front end can misread (#1006): fzn_subgraph_enum.mzn
# shifts the endpoints by min(index_set(ns)) and fzn_subgraph_int.mzn by 1.
# Several shapes to a model, so --fzn-count guards each, and --fzn-pattern
# checks that the node variables the model equates really do reach the builtin
# as one variable twice.
gcs_minizinc_test(minizinc-subgraph-shapes shapes.mzn true true
    OPTIONS --fzn-count 4 glasgow_subgraph --reference-std
        --fzn-pattern "glasgow_subgraph\".*\"(X_INTRODUCED_[0-9]+_)\", true, \"\\1\"")

# Reified, half-reified and negated subgraph, which must reach the standard
# library's fzn_subgraph_reif rather than the builtin, which has no reified
# form: so the count is zero.
gcs_minizinc_test(minizinc-subgraph-reified reified.mzn true true
    OPTIONS --fzn-count 0 glasgow_subgraph --reference-std)
