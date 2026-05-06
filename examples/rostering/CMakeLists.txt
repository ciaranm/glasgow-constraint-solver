add_executable(rostering rostering.cc)
target_link_libraries(rostering PRIVATE glasgow_constraint_solver)


target_link_libraries(rostering PRIVATE cxxopts)

add_test(NAME rostering COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:rostering>)