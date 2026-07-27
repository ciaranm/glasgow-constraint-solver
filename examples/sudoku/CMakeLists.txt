add_executable(sudoku sudoku.cc)
target_link_libraries(sudoku PRIVATE glasgow_constraint_solver)


target_link_libraries(sudoku PRIVATE cxxopts)

add_test(NAME sudoku COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename sudoku $<TARGET_FILE:sudoku>)
add_test(NAME sudoku-xv COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename sudoku-xv $<TARGET_FILE:sudoku> --xv)
