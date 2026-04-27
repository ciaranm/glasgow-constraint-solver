add_executable(talent talent.cc)
target_link_libraries(talent PRIVATE glasgow_constraint_solver)


target_link_libraries(talent PRIVATE cxxopts)