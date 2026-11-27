gcs_minizinc_test(minizinc-arraybooland array_bool_and.mzn true true)

gcs_minizinc_test(minizinc-arrayboolxor array_bool_xor.mzn true true)

gcs_minizinc_test(minizinc-boolxor bool_xor.mzn true true)

# The Boolean builtins on the shapes fzn-glasgow's branches can misread
# (#1006): literals mixed in with the variables, a variable repeated (in a
# clause both positively and negatively), empty arrays, reified forms with
# constant arguments, and bool_lin_eq / bool_lin_le with negative and zero
# coefficients, a variable right-hand side, and the two-term unit-coefficient
# forms that fzn-glasgow rewrites into a comparison of two variables. MiniZinc
# passes a direct call to a FlatZinc builtin through as written, so the models
# make direct calls, and the counts insist that each one arrived. The
# standard-library reference decomposes bool_clause_reif, where the default
# solver posts it natively.
gcs_minizinc_test(minizinc-logical-clauses clauses.mzn true true
    OPTIONS --fzn-count 3 "\"bool_clause\"" --fzn-count 3 bool_clause_reif
            --fzn-count 2 array_bool_and --fzn-count 1 array_bool_xor
            --fzn-count 1 "\"bool_and\"" --fzn-count 1 "\"bool_xor\""
            --reference-std)

gcs_minizinc_test(minizinc-logical-compare compare.mzn true true
    OPTIONS --fzn-count 2 "\"bool_le\"" --fzn-count 1 "\"bool_lt\""
            --fzn-count 3 bool_eq_reif --fzn-count 2 bool_le_reif
            --fzn-count 3 bool_lt_reif --fzn-count 2 "\"bool_or\""
            --fzn-count 1 "\"bool_and\"" --fzn-count 3 "\"bool_xor\""
            --fzn-count 1 "\"bool_not\"" --fzn-count 2 "\"bool2int\""
            --reference-std)

gcs_minizinc_test(minizinc-logical-lin lin.mzn true true
    OPTIONS --fzn-count 4 bool_lin_eq --fzn-count 3 bool_lin_le --reference-std)

# Unsatisfiable shapes, one to a model: the empty clause, an odd number of an
# empty array's members true, and a variable that is its own negation.
gcs_minizinc_test(minizinc-logical-emptyclause empty_clause.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern "\"bool_clause\"")

gcs_minizinc_test(minizinc-logical-emptyxor empty_xor.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern array_bool_xor)

gcs_minizinc_test(minizinc-logical-notself not_self.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern bool_not)
