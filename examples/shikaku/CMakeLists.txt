add_executable(shikaku shikaku.cc)
target_link_libraries(shikaku PRIVATE glasgow_constraint_solver)


target_link_libraries(shikaku PRIVATE cxxopts)

add_test(NAME shikaku COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:shikaku>)
