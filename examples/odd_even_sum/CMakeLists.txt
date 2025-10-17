add_executable(odd_even_sum odd_even_sum.cc)
target_link_libraries(odd_even_sum PUBLIC glasgow_constraint_solver)


target_link_libraries(odd_even_sum LINK_PUBLIC cxxopts)

add_test(NAME odd_even_sum COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:odd_even_sum>)
