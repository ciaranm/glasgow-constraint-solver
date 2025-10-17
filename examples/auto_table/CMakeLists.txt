add_executable(auto_table auto_table.cc)
target_link_libraries(auto_table PUBLIC glasgow_constraint_solver)

target_link_libraries(auto_table LINK_PUBLIC cxxopts)

add_test(NAME auto_table COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:auto_table>)

