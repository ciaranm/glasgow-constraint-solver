# --fzn-pattern is load-bearing on every lane here: without it they would pass
# against the stdlib decomposition, which agrees with the reference solver and
# verifies its proof just as happily, and nothing else the harness checks would
# notice that the builtin never ran.
gcs_minizinc_test(minizinc-circuit basic.mzn true true OPTIONS --fzn-pattern glasgow_circuit)

gcs_minizinc_test(minizinc-subcircuit subcircuit_basic.mzn true true OPTIONS --fzn-pattern glasgow_subcircuit)

gcs_minizinc_test(minizinc-subcircuit-evidence subcircuit_evidence.mzn true true
    OPTIONS --fzn-pattern glasgow_subcircuit)

# Two entries of one array equated, which MiniZinc flattens into the same
# variable twice. Each is unsatisfiable and used to be an error (#1047); the
# pattern checks that the array really did reach the builtin with a repeat.
gcs_minizinc_test(minizinc-circuit-aliased aliased.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern glasgow_circuit --fzn-pattern "\\[\"(X_INTRODUCED_[0-9]+_)\", \"\\1\"")

gcs_minizinc_test(minizinc-subcircuit-aliased subcircuit_aliased.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern glasgow_subcircuit --fzn-pattern "\\[\"(X_INTRODUCED_[0-9]+_)\", \"\\1\"")
