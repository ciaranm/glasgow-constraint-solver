add_executable(regex regex.cc)
target_link_libraries(regex PRIVATE glasgow_constraint_solver)


target_link_libraries(regex PRIVATE cxxopts)

add_test(NAME regex COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:regex>)
add_test(NAME regex-regex COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:regex> --regex)

# Both runs write the same regex.{opb,pbp} (the proof basename defaults to the
# binary name), so serialise them rather than racing in a parallel ctest.
set_tests_properties(regex regex-regex PROPERTIES RESOURCE_LOCK regex)
