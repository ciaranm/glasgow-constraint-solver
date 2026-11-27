gcs_minizinc_test(minizinc-symmetricalldifferent basic.mzn true true)

# As minizinc-inverses-offset.
gcs_minizinc_test(minizinc-symmetricalldifferent-offset offset.mzn true true
    OPTIONS --fzn-pattern glasgow_symmetric_all_different)

# As minizinc-inverses-shapes and minizinc-inverses-negative.
gcs_minizinc_test(minizinc-symmetricalldifferent-shapes shapes.mzn true true
    OPTIONS --fzn-count 4 glasgow_symmetric_all_different --reference-std)

gcs_minizinc_test(minizinc-symmetricalldifferent-negative negative.mzn true true
    OPTIONS --fzn-count 2 glasgow_symmetric_all_different --reference-std --skip-default-reference)
