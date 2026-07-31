add_executable(difference_chain difference_chain.cc)
target_link_libraries(difference_chain PRIVATE glasgow_constraint_solver)
target_link_libraries(difference_chain PRIVATE cxxopts)

# One entry per mode and variant, each with its own proof basename: without
# that, a parallel ctest run has several entries writing the same .opb / .pbp
# pair (issue #562).
add_test(NAME difference_chain-fixpoint COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename difference_chain-fixpoint $<TARGET_FILE:difference_chain> --mode fixpoint)
add_test(NAME difference_chain-refute COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename difference_chain-refute $<TARGET_FILE:difference_chain> --mode refute)
add_test(NAME difference_chain-global-fixpoint COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename difference_chain-global-fixpoint $<TARGET_FILE:difference_chain> --mode fixpoint --variant global)
add_test(NAME difference_chain-global-refute COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename difference_chain-global-refute $<TARGET_FILE:difference_chain> --mode refute --variant global)

# The presolved variant reaches the same two conclusions by a third route: the
# donors are posted as ordinary linears and the presolver lifts them, so the
# proof cites the donors' own OPB rows rather than rows this example's model
# emitted. Worth its own entries --- the presolver's unit tests drive it through
# a Problem built in-process, not through a posted model.
add_test(NAME difference_chain-presolved-fixpoint COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename difference_chain-presolved-fixpoint $<TARGET_FILE:difference_chain> --mode fixpoint --variant presolved)
add_test(NAME difference_chain-presolved-refute COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename difference_chain-presolved-refute $<TARGET_FILE:difference_chain> --mode refute --variant presolved)

# And with the root simplification stage off, which is the configuration the
# difference_chain measurements say to prefer on a dense system.
add_test(NAME difference_chain-global-refute-nosimplify COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename difference_chain-global-refute-nosimplify $<TARGET_FILE:difference_chain> --mode refute --variant global --simplify off)
