add_executable(hitori hitori.cc)
target_link_libraries(hitori PRIVATE glasgow_constraint_solver)
target_link_libraries(hitori PRIVATE cxxopts)

add_test(NAME hitori COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename hitori $<TARGET_FILE:hitori>)
add_test(NAME hitori-no-connectivity COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash --basename hitori-no-connectivity $<TARGET_FILE:hitori> --connectivity none)
