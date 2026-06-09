add_executable(sort_count_probe sort_count_probe.cc)
target_link_libraries(sort_count_probe PRIVATE glasgow_constraint_solver)

add_test(NAME sort_count_probe COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:sort_count_probe>)
