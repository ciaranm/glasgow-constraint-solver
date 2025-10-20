add_executable(random_regular random_regular.cc)
target_link_libraries(random_regular PUBLIC glasgow_constraint_solver)
target_link_libraries(random_regular LINK_PUBLIC cxxopts)

add_test(NAME random_regular COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:random_regular>)