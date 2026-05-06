add_executable(sudoku sudoku.cc)
target_link_libraries(sudoku PRIVATE glasgow_constraint_solver)


target_link_libraries(sudoku PRIVATE cxxopts)

add_test(NAME sudoku COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:sudoku>)
add_test(NAME sudoku-xv COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:sudoku> --xv)
set_tests_properties(sudoku sudoku-xv PROPERTIES RESOURCE_LOCK sudoku)
