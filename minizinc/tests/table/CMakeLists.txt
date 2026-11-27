gcs_minizinc_test(minizinc-tablebool bool.mzn true true)

gcs_minizinc_test(minizinc-tableint int.mzn true true)

# Duplicate rows, which MiniZinc keeps: every solution is matched by two rows,
# and the proof's solution lines used to fail (issue #1115). One enumerates
# (solx), the other optimises (soli).
gcs_minizinc_test(minizinc-tableintduplicates int_duplicates.mzn true true
    OPTIONS --fzn-pattern glasgow_table_int)

gcs_minizinc_test(minizinc-tableintduplicatesopt int_duplicates_opt.mzn false true
    OPTIONS --fzn-pattern glasgow_table_int)
