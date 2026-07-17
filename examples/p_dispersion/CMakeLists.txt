add_executable(p_dispersion p_dispersion.cc)
target_link_libraries(p_dispersion PRIVATE glasgow_constraint_solver)
target_link_libraries(p_dispersion PRIVATE cxxopts)

add_test(NAME p_dispersion COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:p_dispersion>)
