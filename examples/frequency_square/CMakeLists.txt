add_executable(frequency_square frequency_square.cc)
target_link_libraries(frequency_square PRIVATE glasgow_constraint_solver)


target_link_libraries(frequency_square PRIVATE cxxopts)

add_test(NAME frequency_square COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:frequency_square> --size 8 --lambda 2 --holes 3)
