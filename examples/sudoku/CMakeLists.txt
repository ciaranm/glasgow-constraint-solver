add_executable(sudoku sudoku.cc)
target_link_libraries(sudoku PUBLIC glasgow_constraint_solver)


target_link_libraries(sudoku LINK_PUBLIC cxxopts)
