gcs_minizinc_test(minizinc-regex regex.mzn true true)

# Start states other than 1 (#1328), which fzn-glasgow has to renumber to
# Regular's state 0 consistently across the table's rows, its targets and the
# final states. The shapes model packs four automata, and --fzn-count checks all
# four reached the builtin. The other two are empty sequences whose start state
# is final and state 1 is not, and the other way round.
gcs_minizinc_test(minizinc-regularstart start.mzn true true
    OPTIONS --fzn-count 4 glasgow_regular --reference-std)

gcs_minizinc_test(minizinc-regularstartempty start_empty.mzn true true
    OPTIONS --fzn-pattern glasgow_regular --reference-std)

gcs_minizinc_test(minizinc-regularstartemptynot start_empty_not.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern glasgow_regular --reference-std)

# A reified regular with a start state other than 1, as MiniZinc 2.10's
# fzn_regular_reif flattens it: a plain glasgow_regular over two extra states,
# with q0 passed through. 2.9 refuses a reified regular for every solver, so
# this is hand-written JSON (taken from 2.10.1's output) rather than a model
# whose flattening would depend on the version.
gcs_fzn_json_test(minizinc-regularreifstart-fzn reif_start.fzn)

# More shapes (#1006): variables whose domains reach past the alphabet on both
# sides, the fail state in the table, an unreachable final state, a sequence
# indexed from 0, one of length 1, and a one-state automaton over a sequence
# with a repeated variable and a constant. --fzn-count insists all three
# reached the builtin.
gcs_minizinc_test(minizinc-regular-shapes shapes.mzn true true
    OPTIONS --fzn-count 3 glasgow_regular --reference-std)

# No final states, so nothing is accepted.
gcs_minizinc_test(minizinc-regular-nofinal no_final.mzn true true
    OPTIONS --unsatisfiable --fzn-pattern glasgow_regular --reference-std)
