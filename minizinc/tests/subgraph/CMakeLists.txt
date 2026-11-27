gcs_minizinc_test(minizinc-subgraph basic.mzn true true OPTIONS --fzn-pattern glasgow_subgraph)

gcs_minizinc_test(minizinc-subgraph-empty empty.mzn true true OPTIONS --reference-std)
