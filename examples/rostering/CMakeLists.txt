add_executable(rostering rostering.cc)
target_link_libraries(rostering PRIVATE glasgow_constraint_solver)


target_link_libraries(rostering PRIVATE cxxopts)