add_executable(tsp tsp.cc)
target_link_libraries(tsp PRIVATE glasgow_constraint_solver)

target_link_libraries(tsp PRIVATE cxxopts)

