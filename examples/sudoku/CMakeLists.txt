add_executable(sudoku sudoku.cc)
target_link_libraries(sudoku PRIVATE glasgow_constraint_solver)


target_link_libraries(sudoku PRIVATE cxxopts)

add_test(NAME sudoku COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename sudoku $<TARGET_FILE:sudoku>)
add_test(NAME sudoku-xv COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename sudoku-xv $<TARGET_FILE:sudoku> --xv)

# A 16x16 puzzle read with --puzzle: naked and hidden singles alone solve it,
# and blanking any one of its clues would stop them (it was made by blanking the
# clues of a random solution one at a time, keeping each blank that singles
# could still fill). GAC solves it at the root, while every weaker
# all-different has to search.
add_test(NAME sudoku-sixteen COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename sudoku-sixteen $<TARGET_FILE:sudoku>
    --puzzle ${CMAKE_CURRENT_SOURCE_DIR}/sixteen.txt --all)
