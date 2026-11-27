gcs_minizinc_test(minizinc-alldifferentexcept except.mzn true true)

gcs_minizinc_test(minizinc-alldifferentexceptzero except_zero.mzn true true)

# The shapes a front end hands these globals (#1006): empty and single-element
# arrays, integer literals among the variables, arrays indexed from negative
# values, enum-typed arrays, and for the exception set, an empty set and one with
# a hole. Each model packs several shapes, so --fzn-count insists that every one
# of them reached the builtin rather than one being rewritten away behind the
# others. --reference-std adds the standard library's decompositions, since
# MiniZinc's default solver has its own all_different and alldifferent_except_0,
# and agreeing with a propagator and with a decomposition are different evidence.
# The except lane's count takes either builtin because MiniZinc 2.10's wrapper
# turns an empty exception set into a plain all_different before our
# redefinition is consulted, where 2.9 hands it over; the Linux lanes pin 2.9.7
# and the macOS ones take Homebrew's current release, so the count has to hold
# for both.
gcs_minizinc_test(minizinc-alldifferent-shapes shapes.mzn true true
    OPTIONS --fzn-count 5 glasgow_alldifferent --reference-std)

gcs_minizinc_test(minizinc-alldifferentexcept-shapes except_shapes.mzn true true
    OPTIONS --fzn-count 6 "glasgow_all_different_except_int|glasgow_alldifferent" --reference-std)
