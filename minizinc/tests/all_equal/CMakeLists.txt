gcs_minizinc_test(minizinc-allequal basic.mzn true true)

# Issue #1153: holes made during search, under the model's own branching. The
# --fzn-count guards that the one all_equal reaches the builtin.
gcs_minizinc_test(minizinc-allequal-search-holes search_holes.mzn true true
    OPTIONS --fzn-count 1 glasgow_all_equal_int --reference-std)

# The shapes a front end hands all_equal (#1006), guarded by --fzn-count so that
# one rewritten away cannot hide behind the others. The empty and single-element
# arrays never reach the builtin, since the stdlib wrapper answers them itself,
# which is why the count is 5 for 7 calls. reif.mzn has the reified,
# half-reified and negated contexts, which go through the stdlib's
# fzn_all_equal_int_reif and reach no builtin. --reference-std adds the standard
# library's decompositions, since MiniZinc's default solver has its own
# all_equal.
gcs_minizinc_test(minizinc-allequal-shapes shapes.mzn true true
    OPTIONS --fzn-count 5 glasgow_all_equal_int --reference-std)

gcs_minizinc_test(minizinc-allequal-reif reif.mzn true true OPTIONS --reference-std)
