add_executable(sudoku sudoku.cc)
target_link_libraries(sudoku PRIVATE glasgow_constraint_solver)


target_link_libraries(sudoku PRIVATE cxxopts)
