add_executable(table_layout table_layout.cc)
target_link_libraries(table_layout PRIVATE glasgow_constraint_solver)


target_link_libraries(table_layout PRIVATE cxxopts)

add_test(NAME table_layout-table COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename table_layout-table $<TARGET_FILE:table_layout> --variant table)
add_test(NAME table_layout-auto-table COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename table_layout-auto-table $<TARGET_FILE:table_layout> --variant auto-table)
add_test(NAME table_layout-element COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename table_layout-element $<TARGET_FILE:table_layout> --variant element)
