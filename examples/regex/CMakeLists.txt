add_executable(regex regex.cc)
target_link_libraries(regex PRIVATE glasgow_constraint_solver)


target_link_libraries(regex PRIVATE cxxopts)

add_test(NAME regex COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename regex $<TARGET_FILE:regex>)
add_test(NAME regex-regex COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename regex-regex $<TARGET_FILE:regex> --regex)
# A non-deterministic automaton. Its .scp used to be the one shape read_scp
# could not rebuild, and this lane passed only through run_test_and_verify.bash's
# exit-3 branch; the reader rebuilds it since #1335, so the lane now reads it
# back like any other.
add_test(NAME regex-nondeterministic COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename regex-nondeterministic $<TARGET_FILE:regex> --nondeterministic)
