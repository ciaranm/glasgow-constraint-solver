# The standard library has no plain int overload of decreasing or
# strictly_decreasing, so an int array used to take the optional overload and be
# decomposed into int_lin_le, and these lanes passed against the decomposition
# (#1146). The fzn counts are what notice that happening again: every shape in
# decreasing_shapes.mzn, and the one in each single-shape lane, must reach a
# builtin. decreasing_reif.mzn checks that the reified and half-reified forms,
# which have no builtin, still flatten. The standard library's reified
# increasing decomposition is wrong on an empty array, so the overloads decide
# arrays of length 0 or 1 themselves; decreasing_trivial.mzn, the two empty-not
# lanes and decreasing_empty_half_not.mzn check those lengths under reification,
# half-reification and negation. MiniZinc finds the empty-not models
# inconsistent while flattening, so the solver never runs and there is no proof
# to check; decreasing_empty_half_not.mzn is a negated empty array that does
# reach the solver.
gcs_minizinc_test(minizinc-decreasing decreasing_basic.mzn true true OPTIONS --fzn-count 1 glasgow_increasing_int)

gcs_minizinc_test(minizinc-decreasing-shapes decreasing_shapes.mzn true true
    OPTIONS --fzn-count 5 glasgow_increasing_int --fzn-count 2 glasgow_strictly_increasing_int --fzn-count 1 glasgow_increasing_bool --reference-std)

gcs_minizinc_test(minizinc-decreasing-reif decreasing_reif.mzn true true)

gcs_minizinc_test(minizinc-decreasing-trivial decreasing_trivial.mzn true true OPTIONS --reference-std)

gcs_minizinc_test(minizinc-decreasing-empty-not decreasing_empty_not.mzn true false
    OPTIONS --unsatisfiable --reference-std)

gcs_minizinc_test(minizinc-strictlydecreasing-empty-not strictly_decreasing_empty_not.mzn true false
    OPTIONS --unsatisfiable --reference-std)

gcs_minizinc_test(minizinc-decreasing-empty-halfnot decreasing_empty_half_not.mzn true true
    OPTIONS --reference-std)

gcs_minizinc_test(minizinc-increasing basic.mzn true true)

gcs_minizinc_test(minizinc-strictlydecreasing strictly_decreasing_basic.mzn true true
    OPTIONS --fzn-count 1 glasgow_strictly_increasing_int)

gcs_minizinc_test(minizinc-strictlyincreasing strictly_increasing_basic.mzn true true)
