add_executable(cumulative cumulative.cc)
target_link_libraries(cumulative PRIVATE glasgow_constraint_solver)


target_link_libraries(cumulative PRIVATE cxxopts)

add_test(NAME cumulative COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:cumulative>)
