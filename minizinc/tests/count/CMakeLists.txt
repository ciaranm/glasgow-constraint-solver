gcs_minizinc_test(minizinc-count basic.mzn true true)

# Count with how_many or the value of interest sharing a variable with the
# array, or with each other: the justifications used to read the state after
# their own push, and VeriPB rejected the proofs (issue #1201).
gcs_minizinc_test(minizinc-countaliased aliased.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern glasgow_count_eq)

gcs_minizinc_test(minizinc-countaliasedboth aliased_both.mzn true true OPTIONS --fzn-pattern glasgow_count_eq)

gcs_minizinc_test(minizinc-countaliasedvoi aliased_voi.mzn true true OPTIONS --fzn-pattern glasgow_count_eq)

# how_many is the value of interest, and the array pruning used to decide on
# bookkeeping from before the how_many bound that also pruned the value of
# interest: a wrong UNSATISFIABLE (issue #1304).
gcs_minizinc_test(minizinc-countaliasedsurvivor aliased_survivor.mzn true true
    OPTIONS --fzn-pattern glasgow_count_eq)

gcs_minizinc_test(minizinc-countops ops.mzn true true)
