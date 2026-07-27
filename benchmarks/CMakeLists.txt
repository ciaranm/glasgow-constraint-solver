# Propagator and mechanism micro-benchmarks: programs whose purpose is to
# measure something, not to demonstrate the API. None of them is registered as
# a ctest -- they take a size or a repeat count and print timings, so there is
# no fixed instance to check an answer against.
#
# Kept apart from examples/, which is user-facing material and doubles as the
# proof-logging regression suite (every program there is a ctest that runs with
# --prove and is checked by VeriPB), and from minicp_benchmarks/, which is the
# specific curated set used for cross-solver comparison against MiniCP.
#
# See dev_docs/benchmarking.md for the benchmark set used when evaluating a
# performance-sensitive change.
add_subdirectory(bin_packing_bench)
add_subdirectory(knapsack_bench)
add_subdirectory(linear_prop_cost)
add_subdirectory(linear_slack_bench)
add_subdirectory(negative_table_random)
add_subdirectory(positive_table_random)
add_subdirectory(slack_watch)
add_subdirectory(wake_cost)
