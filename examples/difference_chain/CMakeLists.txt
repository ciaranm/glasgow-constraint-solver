add_executable(difference_chain difference_chain.cc)
target_link_libraries(difference_chain PRIVATE glasgow_constraint_solver)
target_link_libraries(difference_chain PRIVATE cxxopts)

# One entry per mode, each with its own proof basename: without that, a parallel
# ctest run has both entries writing the same .opb / .pbp pair (issue #562).
add_test(NAME difference_chain-fixpoint COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename difference_chain-fixpoint $<TARGET_FILE:difference_chain> --mode fixpoint)
add_test(NAME difference_chain-refute COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename difference_chain-refute $<TARGET_FILE:difference_chain> --mode refute)
