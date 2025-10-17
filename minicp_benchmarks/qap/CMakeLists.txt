add_executable(qap qap.cc)
target_link_libraries(qap PUBLIC glasgow_constraint_solver)

target_link_libraries(qap LINK_PUBLIC cxxopts)

add_test(NAME qap-5 COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:qap> 5)
