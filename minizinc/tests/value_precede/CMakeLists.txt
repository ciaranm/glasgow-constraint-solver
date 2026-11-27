gcs_minizinc_test(minizinc-valueprecede basic.mzn true true)

gcs_minizinc_test(minizinc-valueprecedechain chain.mzn true true)

# The shapes a front end can misread for value_precede (#1006): s = t, values
# outside every domain, an empty x, negative values, integer literals and a
# repeated variable, index sets not from 1, and enums. The count insists that
# every shape reached the builtin; --reference-std adds the standard library's
# decomposition, since MiniZinc's default solver has its own value_precede. The
# reified forms are not tested: the stdlib's reified decomposition aborts for
# every solver.
gcs_minizinc_test(minizinc-valueprecede-shapes shapes.mzn true true
    OPTIONS --fzn-count 6 glasgow_value_precede_int --reference-std)

# As minizinc-valueprecede-shapes, for value_precede_chain: a chain indexed from
# 0 with negative values and one outside every domain, an empty chain, a chain
# that repeats a value, literals and a repeated variable in an x indexed from
# -1, and enums. MiniZinc's default solver already runs the stdlib
# decomposition, so there is no --reference-std. An empty x is left out because
# that decomposition cannot run it (it takes ub_array(x)).
gcs_minizinc_test(minizinc-valueprecedechain-shapes chain_shapes.mzn true true
    OPTIONS --fzn-count 5 glasgow_value_precede_chain_int)
