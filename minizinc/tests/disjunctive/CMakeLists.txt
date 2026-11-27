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

# The shapes a front end hands disjunctive and disjunctive_strict (#1006),
# several to a model, with a count for each builtin (the closing quote keeps
# each count to its own name): MiniZinc's disjunctive wrapper hands a call
# with only positive durations to disjunctive_strict, and a count that lumped
# the two together would not notice. --reference-std adds the standard
# library's decompositions, since native Gecode has its own disjunctive_strict.
gcs_minizinc_test(minizinc-disjunctive-shapes shapes.mzn true true
    OPTIONS --fzn-count 3 "glasgow_disjunctive\"" --fzn-count 3 "glasgow_disjunctive_strict\""
    --reference-std)

# The same for optional tasks, against Chuffed and Gecode under -G std, which
# decompose, as well as native Gecode, which propagates the strict form itself
# where the durations are fixed.
gcs_minizinc_test(minizinc-disjunctive-opt-shapes opt_shapes.mzn true true
    OPTIONS --fzn-count 1 "glasgow_disjunctive_opt\"" --fzn-count 2 glasgow_disjunctive_strict_opt
    --reference-solver chuffed --reference-std)
