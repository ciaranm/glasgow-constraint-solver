add_executable(tutorial_proof tutorial_proof.cc)
target_link_libraries(tutorial_proof PRIVATE glasgow_constraint_solver)


target_link_libraries(tutorial_proof PRIVATE cxxopts)

add_test(NAME tutorial_proof COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:tutorial_proof>)
