add_executable(smart_table_lex smart_table_lex.cc)
target_link_libraries(smart_table_lex PRIVATE glasgow_constraint_solver)


target_link_libraries(smart_table_lex PRIVATE cxxopts)

add_test(NAME smart_table_lex COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:smart_table_lex>)