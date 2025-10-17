add_executable(langford langford.cc)
target_link_libraries(langford PUBLIC glasgow_constraint_solver)


target_link_libraries(langford LINK_PUBLIC cxxopts)

add_test(NAME langford COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:langford>)
