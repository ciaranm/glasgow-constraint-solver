add_executable(skyscrapers skyscrapers.cc)
target_link_libraries(skyscrapers PRIVATE glasgow_constraint_solver)


target_link_libraries(skyscrapers PRIVATE cxxopts)

add_test(NAME skyscrapers-5 COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:skyscrapers> 5)
add_test(NAME skyscrapers-5-autotable COMMAND ${GCS_BASH} ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:skyscrapers> 5 --autotable)
set_tests_properties(skyscrapers-5 skyscrapers-5-autotable PROPERTIES RESOURCE_LOCK skyscrapers)
