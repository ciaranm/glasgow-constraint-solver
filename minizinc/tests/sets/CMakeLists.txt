gcs_minizinc_test(minizinc-setinreif set_in_reif.mzn true true)

gcs_minizinc_test(minizinc-sets basic.mzn true true)

# Empty-set set_in / set_in_reif: MiniZinc folds `x in {}` to false before it
# reaches the solver, so these feed hand-written JSON FlatZinc to fzn-glasgow
# directly to exercise the empty-set frontend guards.
gcs_fzn_json_test(minizinc-emptysetin empty_set_in.fzn)

gcs_fzn_json_test(minizinc-emptysetinreif empty_set_in_reif.fzn)

# Sets with holes, sets of a single value and sets reaching past the domain,
# in set_in and in reified, half-reified and negated set_in_reif (#1006).
# fzn-glasgow posts a set's bounds and one constraint per gap, so the holes are
# what it can get wrong. The counts insist that each call reached the builtin
# rather than becoming a domain or an equality.
gcs_minizinc_test(minizinc-sets-inshapes in_shapes.mzn true true
    OPTIONS --fzn-count 2 "\"set_in\"" --fzn-count 5 "\"set_in_reif\""
            --reference-std)
