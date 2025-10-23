add_executable(n_queens n_queens.cc)
target_link_libraries(n_queens PUBLIC glasgow_constraint_solver)

target_link_libraries(n_queens LINK_PUBLIC cxxopts)

add_test(NAME n_queens-all-10 COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:n_queens> --all 10)
