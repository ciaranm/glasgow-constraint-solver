add_executable(money money.cc)
target_link_libraries(money PRIVATE glasgow_constraint_solver)


target_link_libraries(money PRIVATE cxxopts)

add_test(NAME money COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:money>)
