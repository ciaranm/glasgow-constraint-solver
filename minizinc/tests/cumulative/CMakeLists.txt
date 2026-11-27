gcs_minizinc_test(minizinc-cumulative basic.mzn false true)

gcs_minizinc_test(minizinc-cumulative-mode mode.mzn true true)

gcs_minizinc_test(minizinc-cumulative-var var.mzn true true)

# Optional tasks. --fzn-pattern is the reachability guard: MiniZinc's cumulative
# wrapper is free to rewrite the constraint into a decomposition, and if it did,
# these tests would agree with the default solver and verify their proofs
# without glasgow_cumulative_opt ever running.
gcs_minizinc_test(minizinc-cumulative-opt opt.mzn true true
    OPTIONS --fzn-pattern glasgow_cumulative_opt --reference-solver chuffed)

gcs_minizinc_test(minizinc-cumulative-opt-obj opt_obj.mzn false true
    OPTIONS --fzn-pattern glasgow_cumulative_opt --reference-solver chuffed)

# Pins the glasgow_cumulative_opt signature against the solver directly, so a
# MiniZinc version that re-routes around the builtin cannot take this coverage
# with it. The expected solutions are the hand-countable set: 9 with both tasks
# absent, 9 with each alone, and the 2 non-overlapping placements with both.
gcs_fzn_json_test(minizinc-cumulativeopt-fzn opt_fzn.fzn)
