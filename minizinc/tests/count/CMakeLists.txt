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

# The shapes a front end hands count (#1006), several to a model, each guarded
# by --fzn-count so that one rewritten away cannot hide behind the others.
# --reference-std adds the standard library's decompositions, since MiniZinc's
# default solver has its own count. shapes.mzn has empty and single-element
# arrays, literals and a repeated variable, a negative-indexed 2-D array, enums
# and coerced bools; compare.mzn and compare_par.mzn have every comparison form,
# with variable and with constant arguments; deprecated.mzn has at_least,
# at_most and exactly, which have redefinitions of their own; reif.mzn has every
# form in reified, half-reified and negated contexts, which must flatten through
# the stdlib's _reif decompositions; and too_many.mzn is a count larger than its
# array, which must be refused with a proof.
gcs_minizinc_test(minizinc-count-shapes shapes.mzn true true
    OPTIONS --fzn-count 7 glasgow_count_eq --reference-std)

gcs_minizinc_test(minizinc-count-compare compare.mzn true true
    OPTIONS --fzn-count 6 glasgow_count_eq --reference-std)

gcs_minizinc_test(minizinc-count-compare-par compare_par.mzn true true
    OPTIONS --fzn-count 5 glasgow_count_eq --reference-std)

gcs_minizinc_test(minizinc-count-deprecated deprecated.mzn true true
    OPTIONS --fzn-count 7 glasgow_count_eq --reference-std)

gcs_minizinc_test(minizinc-count-reif reif.mzn true true
    OPTIONS --fzn-count 3 glasgow_count_eq --reference-std)

gcs_minizinc_test(minizinc-count-too-many too_many.mzn true true
    OPTIONS --unsatisfiable --fzn-count 1 glasgow_count_eq --reference-std)
