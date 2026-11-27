gcs_minizinc_test(minizinc-allequal basic.mzn true true)

# Issue #1153: holes made during search, under the model's own branching. The
# --fzn-count guards that the one all_equal reaches the builtin.
gcs_minizinc_test(minizinc-allequal-search-holes search_holes.mzn true true
    OPTIONS --fzn-count 1 glasgow_all_equal_int --reference-std)
