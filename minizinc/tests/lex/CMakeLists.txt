gcs_minizinc_test(minizinc-lexbool bool.mzn true true)

gcs_minizinc_test(minizinc-lexgequnequal geq_unequal.mzn true true)

gcs_minizinc_test(minizinc-lexgtunequal gt_unequal.mzn true true)

gcs_minizinc_test(minizinc-lexlequnequal leq_unequal.mzn true true)

gcs_minizinc_test(minizinc-lexless less.mzn true true)

gcs_minizinc_test(minizinc-lexlesseq lesseq.mzn true true)

gcs_minizinc_test(minizinc-lexltunequal lt_unequal.mzn true true)

gcs_minizinc_test(minizinc-lexreif reif.mzn true true)

# The shapes a front end can misread for lex_less and lex_lesseq (#1006): index
# sets that differ between the two arrays and do not start at 1, unequal
# lengths, integer literals and variables shared between the sides, the same
# array on both sides, enums, and empty arrays, which the stdlib's wrapper
# decides before any builtin. Each model counts every builtin it should reach.
# --reference-std adds the standard library's decompositions, since MiniZinc's
# default solver has its own lex.
gcs_minizinc_test(minizinc-lex-shapes shapes.mzn true true
    OPTIONS --fzn-count 3 glasgow_lex_less_int --fzn-count 3 glasgow_lex_lesseq_int --reference-std)

# lex has real reified builtins, so a reified, half-reified or negated call
# reaches Glasgow rather than a decomposition, unlike most globals; minizinc-lexreif
# covers only the reified form over equal-length arrays from 1.
gcs_minizinc_test(minizinc-lex-reifshapes reif_shapes.mzn true true
    OPTIONS --fzn-count 2 glasgow_lex_less_int_reif --fzn-count 2 glasgow_lex_lesseq_int_reif --reference-std)

# The Boolean builtins, plain and reified. The `[^_]` keeps the plain patterns
# from also matching the reified builtins.
gcs_minizinc_test(minizinc-lex-boolshapes bool_shapes.mzn true true
    OPTIONS --fzn-count 1 "glasgow_lex_less_bool[^_]" --fzn-count 2 glasgow_lex_less_bool_reif
        --fzn-count 1 "glasgow_lex_lesseq_bool[^_]" --fzn-count 1 glasgow_lex_lesseq_bool_reif --reference-std)

# The same array on both sides of lex_less, which the solver has to prove has no
# solution.
gcs_minizinc_test(minizinc-lex-self self.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern glasgow_lex_less_int --reference-std)
