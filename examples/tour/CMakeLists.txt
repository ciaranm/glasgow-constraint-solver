add_executable(tour tour.cc)
target_link_libraries(tour PRIVATE glasgow_constraint_solver)


target_link_libraries(tour PRIVATE cxxopts)

add_test(NAME tour COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:tour>)
