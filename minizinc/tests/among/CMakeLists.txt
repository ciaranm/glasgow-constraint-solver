gcs_minizinc_test(minizinc-among basic.mzn true true)

# Among with how_many among the positions over a wide holey domain: the lower
# bound's justification used to read the state after its own push, and VeriPB
# rejected the proof (issue #1308).
gcs_minizinc_test(minizinc-amongaliased aliased.mzn true true OPTIONS --fzn-pattern glasgow_among)

# The shapes a front end hands among (#1006), guarded by --fzn-count so that
# one rewritten away cannot hide behind the others: empty and single-element
# arrays, literals in and out of the value set, an empty value set, a value set
# with holes (three ranges in the JSON, so reading only the first, or the hull,
# gives different answers), enums and coerced bools. reif.mzn has the reified,
# half-reified and negated contexts, which go through the stdlib's
# fzn_among_reif, and the function form, which reaches the builtin.
# --reference-std adds the standard library's decompositions, since MiniZinc's
# default solver has its own among.
gcs_minizinc_test(minizinc-among-shapes shapes.mzn true true
    OPTIONS --fzn-count 6 glasgow_among --reference-std)

gcs_minizinc_test(minizinc-among-reif reif.mzn true true
    OPTIONS --fzn-count 3 glasgow_among --reference-std)
