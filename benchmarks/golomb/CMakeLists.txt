add_executable(golomb golomb.cc)
target_link_libraries(golomb PRIVATE glasgow_constraint_solver cxxopts)
