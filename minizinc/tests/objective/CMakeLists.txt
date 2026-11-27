# Maximising while a constraint uses the objective's negation as a view: the
# check after each solution has to spell the objective as `min:` did (issue
# #1206). One gets there by `solve maximize -x`, the other by `y = -x`.
gcs_minizinc_test(minizinc-maximizenegation maximize_negation.mzn false true OPTIONS --fzn-pattern int_lin_eq)

gcs_minizinc_test(minizinc-maximizenegatedview maximize_negated_view.mzn false true
    OPTIONS --fzn-pattern int_lin_eq)
