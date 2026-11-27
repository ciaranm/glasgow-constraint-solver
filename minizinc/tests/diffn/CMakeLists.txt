gcs_minizinc_test(minizinc-diffn basic.mzn true true)

gcs_minizinc_test(minizinc-diffn-rotate rotate.mzn true true)

gcs_minizinc_test(minizinc-diffn-nonstrict nonstrict.mzn true true)

# The shapes a front end hands diffn and diffn_nonstrict (#1006), several to a
# model, with a count for each builtin (the closing quote keeps
# glasgow_diffn_nonstrict out of the first). Most have a rectangle of zero
# width or height, the one place the two forms differ. --reference-std adds
# the standard library's decompositions, since native Gecode has its own diffn.
gcs_minizinc_test(minizinc-diffn-shapes shapes.mzn true true
    OPTIONS --fzn-count 2 "glasgow_diffn\"" --fzn-count 2 glasgow_diffn_nonstrict --reference-std)

# No rectangles, for both forms. Native Gecode's diffn reports =====ERROR=====
# on empty arrays, so this compares against the standard library's
# decompositions alone.
gcs_minizinc_test(minizinc-diffn-empty empty.mzn true true
    OPTIONS --fzn-count 1 "glasgow_diffn\"" --fzn-count 1 glasgow_diffn_nonstrict
    --reference-std --skip-default-reference)
