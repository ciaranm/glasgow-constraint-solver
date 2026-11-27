gcs_minizinc_test(minizinc-among basic.mzn true true)

# Among with how_many among the positions over a wide holey domain: the lower
# bound's justification used to read the state after its own push, and VeriPB
# rejected the proof (issue #1308).
gcs_minizinc_test(minizinc-amongaliased aliased.mzn true true OPTIONS --fzn-pattern glasgow_among)
