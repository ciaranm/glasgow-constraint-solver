# glasgow_scp_solver: a standalone client that solves a problem given as a
# `.scp` (s-expression CP) file (workflow 3). Reads the model with read_scp from
# the core library; the .scp is the input rather than a --prove by-product.
add_executable(glasgow_scp_solver glasgow_scp_solver.cc)
target_link_libraries(glasgow_scp_solver PRIVATE glasgow_constraint_solver)
target_link_libraries(glasgow_scp_solver PRIVATE cxxopts)
target_link_libraries(glasgow_scp_solver PRIVATE gcs_fmt)

# Arithmetic over in-range values that does not fit in an Integer, during
# search: B*X + B*Y + B*Z = 0 with every variable over the whole bounded range.
# An arithmetic constraint may refuse that with IntegerOverflow
# (dev_docs/integer-ranges.md), and the solver must report it rather than abort,
# which it used to. An uncaught exception's message could otherwise match.
add_test(NAME glasgow_scp_solver_range_sum_overflow
    COMMAND $<TARGET_FILE:glasgow_scp_solver> --all ${CMAKE_CURRENT_SOURCE_DIR}/tests/range_sum_overflow.scp)
set_tests_properties(glasgow_scp_solver_range_sum_overflow PROPERTIES
    PASS_REGULAR_EXPRESSION "Error: [^\n]*Integer overflow"
    FAIL_REGULAR_EXPRESSION "terminate called")
