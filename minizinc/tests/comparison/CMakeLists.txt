gcs_minizinc_test(minizinc-disjointdomain disjoint_domain.mzn true true)

gcs_minizinc_test(minizinc-equalsreif equals_reif.mzn true true)

gcs_minizinc_test(minizinc-lessthans less_thans.mzn true true)

gcs_minizinc_test(minizinc-notequalsreif not_equals_reif.mzn true true)

# Each comparison builtin called directly on one variable twice (#1006), which
# the flattener passes through, so the propagators meet aliased operands. The
# first count is every builtin the model calls bar int_eq(y, y), which the
# flattener drops; the second pins that the reified four really did arrive
# aliased. The unsatisfiable lane is int_lt(x, x) alone, since in a model with
# other shapes a second inconsistency would hide it.
gcs_minizinc_test(minizinc-comparison-self-reif self_reif.mzn true true
    OPTIONS --fzn-count 7 "\"int_(le|lt|eq|ne)_reif\"|\"int_le\"|\"int_lin_(le|eq)_reif\""
            --fzn-count 4 "\\[\"x\", \"x\", \"b[1-4]\"\\]" --reference-std)

gcs_minizinc_test(minizinc-comparison-self-lt-unsat self_lt_unsat.mzn true true
    OPTIONS --unsatisfiable --fzn-count 1 "\"int_lt\"" --reference-std)

# Comparisons with a constant on either side, reified, half-reified and in
# negated contexts (#1006): the reified ones reach int_le_reif and int_eq_reif
# with a literal argument, a negated implication forces an int_ne with a
# literal, and the comparisons between variables under negation reach two-term
# int_lin_*_reif rows, which the reader does not recover.
gcs_minizinc_test(minizinc-comparison-const-negated const_negated.mzn true true
    OPTIONS --fzn-count 3 "\"int_(le|eq)_reif\"" --fzn-count 1 "\"int_ne\""
            --fzn-count 2 "\"int_lin_(ne|le)_reif\"" --reference-std)
