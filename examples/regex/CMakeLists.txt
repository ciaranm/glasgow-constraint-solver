add_executable(regex regex.cc)
target_link_libraries(regex PUBLIC glasgow_constraint_solver)


target_link_libraries(regex LINK_PUBLIC cxxopts)