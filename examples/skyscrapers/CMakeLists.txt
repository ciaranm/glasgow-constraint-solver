add_executable(skyscrapers skyscrapers.cc)
target_link_libraries(skyscrapers PUBLIC glasgow_constraint_solver)


target_link_libraries(skyscrapers LINK_PUBLIC cxxopts)

add_test(NAME skyscrapers-5 COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:skyscrapers> 5)

# currently failing due to a bug in VeriPB
# add_test(NAME skyscrapers-5-autotable COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:skyscrapers> 5 --autotable)
# set_tests_properties(skyscrapers-5 skyscrapers-5-autotable PROPERTIES RESOURCE_LOCK skyscrapers)
