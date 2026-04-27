add_executable(ortho_latin ortho_latin.cc)
target_link_libraries(ortho_latin PRIVATE glasgow_constraint_solver)


target_link_libraries(ortho_latin PRIVATE cxxopts)

add_test(NAME ortho_latin-5 COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:ortho_latin> 5)
