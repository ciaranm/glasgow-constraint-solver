add_executable(tsp tsp.cc)
target_link_libraries(tsp PUBLIC glasgow_constraint_solver)

target_link_libraries(tsp LINK_PUBLIC cxxopts)

