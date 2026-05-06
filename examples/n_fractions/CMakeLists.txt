add_executable(n_fractions n_fractions.cc)
target_link_libraries(n_fractions PRIVATE glasgow_constraint_solver)


target_link_libraries(n_fractions PRIVATE cxxopts)

add_test(NAME n_fractions COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:n_fractions> --unsat)
