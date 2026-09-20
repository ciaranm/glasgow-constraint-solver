add_executable(squares squares.cc)
target_link_libraries(squares PRIVATE glasgow_constraint_solver)

target_link_libraries(squares PRIVATE cxxopts)

# The default instance is unsatisfiable by one unit, so both lanes are quick and
# both write a refutation to check. The --relaxation lane is the one that
# exercises the derived capacity row; without it the same refutation is found by
# searching, over the pairwise rule alone.
add_test(NAME squares COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash
    --basename squares_pairwise $<TARGET_FILE:squares>)
add_test(NAME squares_relaxation COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash
    --basename squares_relaxation $<TARGET_FILE:squares> --relaxation)
