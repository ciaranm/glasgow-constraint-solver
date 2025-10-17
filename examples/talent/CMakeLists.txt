add_executable(talent talent.cc)
target_link_libraries(talent PUBLIC glasgow_constraint_solver)


target_link_libraries(talent LINK_PUBLIC cxxopts)