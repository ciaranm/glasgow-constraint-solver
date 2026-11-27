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
    OPTIONS --unsatisfiable --fzn-pattern glasgow_circuit --fzn-pattern "\"(X_INTRODUCED_[0-9]+_)\", \"\\1\"")

gcs_minizinc_test(minizinc-subcircuit-aliased subcircuit_aliased.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern glasgow_subcircuit --fzn-pattern "\"(X_INTRODUCED_[0-9]+_)\", \"\\1\"")

# More of the shapes a front end can misread (#1006): circuit and subcircuit
# values are indices into their own array, so fzn_circuit.mzn and
# fzn_subcircuit.mzn pass min(index_set(x)) as an offset. Several shapes to a
# model, so --fzn-count guards each; --reference-std adds the standard
# library's decomposition, which agrees with Gecode on every size from two up.
gcs_minizinc_test(minizinc-circuit-shapes shapes.mzn true true
    OPTIONS --fzn-count 6 glasgow_circuit --reference-std)

gcs_minizinc_test(minizinc-circuit-subcircuit-shapes subcircuit_shapes.mzn true true
    OPTIONS --fzn-count 6 glasgow_subcircuit --reference-std)

# circuit over var opt successors, which the standard library hands to
# subcircuit, so the guard names glasgow_subcircuit.
gcs_minizinc_test(minizinc-circuit-opt opt_shapes.mzn true true
    OPTIONS --fzn-count 2 glasgow_subcircuit --reference-std)

# A one-node circuit. Glasgow and Gecode take the self loop as the tour
# (#254); the standard library's decomposition forbids it, so this compares
# against Gecode alone and pins the documented choice. Which reading is right
# is still open (#1319); if that changes it, this lane changes with it.
gcs_minizinc_test(minizinc-circuit-single single.mzn true true
    OPTIONS --fzn-count 1 glasgow_circuit)

# An empty circuit, which is true. Gecode's own fzn_circuit takes min of the
# empty index set unguarded and calls it unsatisfiable, so this compares
# against the standard library's decomposition alone. Nothing reaches a
# builtin; what it checks is the redefinition's length guard.
gcs_minizinc_test(minizinc-circuit-empty empty.mzn true true
    OPTIONS --reference-std --skip-default-reference)
