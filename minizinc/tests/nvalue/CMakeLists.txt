gcs_minizinc_test(minizinc-nvalue basic.mzn true true)

# The shapes a front end hands nvalue (#1006), guarded by --fzn-count so that
# one rewritten away cannot hide behind the others: empty and single-element
# arrays, literals and repeated variables, coerced bools, the count inside its
# own array, and the function form over a negative-indexed 2-D array. reif.mzn
# has the reified, half-reified and negated contexts, which go through the
# stdlib's fzn_nvalue_reif, and zero.mzn a count of 0 for an array that is not
# empty, which must be refused with a proof. --reference-std adds the standard
# library's decompositions, since MiniZinc's default solver has its own nvalue.
gcs_minizinc_test(minizinc-nvalue-shapes shapes.mzn true true
    OPTIONS --fzn-count 5 glasgow_nvalue --reference-std)

gcs_minizinc_test(minizinc-nvalue-reif reif.mzn true true
    OPTIONS --fzn-count 1 glasgow_nvalue --reference-std)

gcs_minizinc_test(minizinc-nvalue-zero zero.mzn true true
    OPTIONS --unsatisfiable --fzn-count 1 glasgow_nvalue --reference-std)
