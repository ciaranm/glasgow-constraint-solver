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

# The shapes a front end hands the three bin_packing forms (#1006), several to
# a model, so --fzn-count insists that each reached its builtin. These have
# negative offsets, beside offset.mzn's positive ones and load.mzn's zero; the
# load form's is the only non-zero one. --reference-std adds the standard
# library's decompositions, since native Gecode has its own bin_packing.
gcs_minizinc_test(minizinc-binpacking-shapes shapes.mzn true true
    OPTIONS --fzn-count 2 glasgow_bin_packing_capa --fzn-count 1 glasgow_bin_packing_load
    --reference-std)

# No items, with and without bins: each redefinition's length guard, and the
# builtins with no items. Native Gecode's redefinitions take the bounds of an
# empty array or the min of an empty index set and report an error, so these
# compare against the standard library's decompositions alone.
gcs_minizinc_test(minizinc-binpacking-empty empty.mzn true true
    OPTIONS --fzn-count 1 glasgow_bin_packing_capa --fzn-count 1 glasgow_bin_packing_load
    --reference-std --skip-default-reference)

# An item and no bins, one lane for each guard, since either guard saying
# false would make a shared model unsatisfiable on its own. The flattener
# decides both, so there is no solver run and no proof. Native Gecode errors
# on the capacity form, as above, and happens to agree on the load form.
gcs_minizinc_test(minizinc-binpacking-no-bins-capa no_bins_capa.mzn true false
    OPTIONS --unsatisfiable --reference-std --skip-default-reference)

gcs_minizinc_test(minizinc-binpacking-no-bins-load no_bins_load.mzn true false
    OPTIONS --unsatisfiable --reference-std)

# An item that fits in no bin, which the flattener does not see, so BinPacking
# has to refute it with a proof.
gcs_minizinc_test(minizinc-binpacking-no-fit no_fit.mzn true true
    OPTIONS --unsatisfiable --fzn-count 1 glasgow_bin_packing_capa --reference-std)
