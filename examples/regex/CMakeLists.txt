add_executable(regex regex.cc)
target_link_libraries(regex PRIVATE glasgow_constraint_solver)


target_link_libraries(regex PRIVATE cxxopts)

add_test(NAME regex COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename regex $<TARGET_FILE:regex>)
add_test(NAME regex-regex COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename regex-regex $<TARGET_FILE:regex> --regex)
# The one lane whose .scp read_scp cannot rebuild (a non-deterministic automaton),
# so the only one through run_test_and_verify.bash's exit-3 branch. The pass
# expression is the line that branch prints, which replaces the exit status as
# the test's verdict: the script prints it only after the run and VeriPB have
# both succeeded, and nothing after it can fail, so the test fails if the .scp
# stops reaching that branch and passes only through it.
add_test(NAME regex-nondeterministic COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename regex-nondeterministic $<TARGET_FILE:regex> --nondeterministic)
set_tests_properties(regex-nondeterministic PROPERTIES
    PASS_REGULAR_EXPRESSION "is a shape gcs::read_scp cannot rebuild; passing")
