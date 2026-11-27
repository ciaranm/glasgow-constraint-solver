gcs_minizinc_test(minizinc-seqprecedechain basic.mzn true true)

# The shapes a front end can misread for seq_precede_chain (#1006): negative and
# zero values, which it leaves free, an empty x, a single element, index sets
# not from 1, integer literals and a repeated variable, and a domain with a hole
# at 1. The count insists that every shape reached the builtin. MiniZinc's
# default solver already runs the stdlib decomposition, so there is no
# --reference-std.
gcs_minizinc_test(minizinc-seqprecedechain-shapes shapes.mzn true true
    OPTIONS --fzn-count 5 glasgow_seq_precede_chain_int)
