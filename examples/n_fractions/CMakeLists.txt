add_executable(n_fractions n_fractions.cc)
target_link_libraries(n_fractions PUBLIC glasgow_constraint_solver)


target_link_libraries(n_fractions LINK_PUBLIC cxxopts)
