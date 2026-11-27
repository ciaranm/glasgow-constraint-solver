# Maximising while a constraint uses the objective's negation as a view: the
# check after each solution has to spell the objective as `min:` did (issue
# #1206). One gets there by `solve maximize -x`, the other by `y = -x`.
gcs_minizinc_test(minizinc-maximizenegation maximize_negation.mzn false true OPTIONS --fzn-pattern int_lin_eq)

gcs_minizinc_test(minizinc-maximizenegatedview maximize_negated_view.mzn false true
    OPTIONS --fzn-pattern int_lin_eq)

# Objectives in the shapes a front end can misread (#1006). Each model has one
# objective, so each is its own lane. The --fzn-pattern on the solve item pins
# that the flattener left an optimisation problem, and so that the solver's
# minimise or maximise was reached; the constant objective is the one a future
# flattener might reasonably turn into satisfy.
gcs_minizinc_test(minizinc-objective-minimise-negative-sum minimise_negative_sum.mzn false true
    OPTIONS --fzn-pattern "\"method\" *: *\"minimize\"" --fzn-count 1 "\"int_times\"" --reference-std)

gcs_minizinc_test(minizinc-objective-maximise-negative maximise_negative.mzn false true
    OPTIONS --fzn-pattern "\"method\" *: *\"maximize\", \"objective\" *: *\"y\"" --reference-std)

gcs_minizinc_test(minizinc-objective-maximise-offset-view maximise_offset_view.mzn false true
    OPTIONS --fzn-pattern "\"method\" *: *\"maximize\"" --fzn-count 2 "\"int_lin_eq\"" --reference-std)

gcs_minizinc_test(minizinc-objective-constant constant_objective.mzn false true
    OPTIONS --fzn-pattern "\"method\" *: *\"minimize\"" --reference-std)

gcs_minizinc_test(minizinc-objective-bool bool_objective.mzn false true
    OPTIONS --fzn-pattern "\"method\" *: *\"maximize\"" --fzn-count 1 "\"bool2int\"" --reference-std)

gcs_minizinc_test(minizinc-objective-search-minimise search_minimise.mzn false true
    OPTIONS --fzn-pattern "\"method\" *: *\"minimize\"" --fzn-count 1 "\"int_search\"" --reference-std)

# Optimisation over a model with no solutions, which only search shows, so the
# solver itself has to say UNSATISFIABLE for an optimisation problem.
gcs_minizinc_test(minizinc-objective-unsat-maximise unsat_maximise.mzn false true
    OPTIONS --unsatisfiable --fzn-pattern "\"method\" *: *\"maximize\"" --fzn-count 1 "\"int_times\"" --reference-std)

gcs_minizinc_test(minizinc-objective-unsat-minimise unsat_minimise.mzn false true
    OPTIONS --unsatisfiable --fzn-pattern "\"method\" *: *\"minimize\"" --fzn-count 1 "\"int_times\"" --reference-std)
