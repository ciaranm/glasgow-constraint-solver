add_executable(smart_table_random smart_table_random.cc)
target_link_libraries(smart_table_random PUBLIC glasgow_constraint_solver)

target_link_libraries(smart_table_random LINK_PUBLIC cxxopts)

add_test(NAME smart_table_random COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:smart_table_random>)