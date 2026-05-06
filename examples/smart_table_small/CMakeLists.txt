add_executable(smart_table_small smart_table_small.cc)
target_link_libraries(smart_table_small PRIVATE glasgow_constraint_solver)


target_link_libraries(smart_table_small PRIVATE cxxopts)

add_test(NAME smart_table_small COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:smart_table_small>)
