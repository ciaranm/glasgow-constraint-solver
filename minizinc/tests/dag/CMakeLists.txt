gcs_minizinc_test(minizinc-dag basic.mzn true true OPTIONS --fzn-pattern glasgow_dag)

# dag and the four-argument subgraph over an empty node set are true, so these
# models keep the solutions of their free variable (#1303). Nothing reaches a
# builtin, so there is no --fzn-pattern; --reference-std is the standard
# library's reading of the empty case.
gcs_minizinc_test(minizinc-dag-empty empty.mzn true true OPTIONS --reference-std)
