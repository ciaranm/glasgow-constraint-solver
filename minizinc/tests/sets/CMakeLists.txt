gcs_minizinc_test(minizinc-setinreif set_in_reif.mzn true true)

gcs_minizinc_test(minizinc-sets basic.mzn true true)

# Empty-set set_in / set_in_reif: MiniZinc folds `x in {}` to false before it
# reaches the solver, so these feed hand-written JSON FlatZinc to fzn-glasgow
# directly to exercise the empty-set frontend guards.
gcs_fzn_json_test(minizinc-emptysetin empty_set_in.fzn)

gcs_fzn_json_test(minizinc-emptysetinreif empty_set_in_reif.fzn)
