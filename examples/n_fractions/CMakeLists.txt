add_executable(n_fractions n_fractions.cc)
target_link_libraries(n_fractions PRIVATE glasgow_constraint_solver)


target_link_libraries(n_fractions PRIVATE cxxopts)
