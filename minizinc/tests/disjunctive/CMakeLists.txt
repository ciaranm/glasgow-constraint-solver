gcs_minizinc_test(minizinc-disjunctive-opt opt.mzn true true
    OPTIONS --fzn-pattern glasgow_disjunctive_opt --reference-solver chuffed)

# The strict optional form, which had no redefinition at all before #735: no
# route through cumulative can express "a present zero-duration task may not sit
# inside another", so this one used to keep the library decomposition and go
# uncertified.
gcs_minizinc_test(minizinc-disjunctive-strict-opt strict_opt.mzn true true
    OPTIONS --fzn-pattern glasgow_disjunctive_strict_opt --reference-solver chuffed)

gcs_minizinc_test(minizinc-disjunctive basic.mzn true true)

gcs_minizinc_test(minizinc-disjunctivestrict strict.mzn true true)

gcs_minizinc_test(minizinc-disjunctive-var var.mzn true true)

gcs_minizinc_test(minizinc-disjunctive-var-nonstrict var_nonstrict.mzn true true)
