add_executable(smart_table_am1 smart_table_am1.cc)
target_link_libraries(smart_table_am1 PRIVATE glasgow_constraint_solver)


target_link_libraries(smart_table_am1 PRIVATE cxxopts)

add_test(NAME smart_table_am1 COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:smart_table_am1>)
