gcs_minizinc_test(minizinc-binpacking basic.mzn true true)

# The bin offset the three bin_packing redefinitions pass, which fzn_glasgow
# applies as a view. --fzn-pattern is load-bearing on both: MiniZinc's
# bin_packing wrappers are free to rewrite into the library decomposition, which
# agrees with the reference solver and verifies its proof just as happily, and
# then the offset argument under test is never read. basic.mzn above is
# 1-based, where the offset is 1; these reach offsets of 5, 3 and 0, and
# load.mzn is the only test of the variable-load form at all.
gcs_minizinc_test(minizinc-binpacking-offset offset.mzn true true
    OPTIONS --fzn-pattern glasgow_bin_packing_capa)

gcs_minizinc_test(minizinc-binpacking-load load.mzn true true OPTIONS --fzn-pattern glasgow_bin_packing_load)
