add_executable(tour tour.cc)
target_link_libraries(tour PUBLIC glasgow_constraint_solver)


target_link_libraries(tour LINK_PUBLIC cxxopts)

add_test(NAME tour COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:tour>)
