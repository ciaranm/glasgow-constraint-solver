add_executable(qap qap.cc)
target_link_libraries(qap PRIVATE glasgow_constraint_solver)

target_link_libraries(qap PRIVATE cxxopts)

add_test(NAME qap-5 COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:qap> 5)
