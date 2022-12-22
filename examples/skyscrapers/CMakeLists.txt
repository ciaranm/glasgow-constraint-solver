add_executable(skyscrapers skyscrapers.cc)
target_link_libraries(skyscrapers PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(skyscrapers LINK_PUBLIC ${Boost_LIBRARIES})

add_test(NAME skyscrapers-5 COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:skyscrapers> 5)

# currently failing due to a bug in VeriPB
# add_test(NAME skyscrapers-5-autotable COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:skyscrapers> 5 --autotable)
# set_tests_properties(skyscrapers-5 skyscrapers-5-autotable PROPERTIES RESOURCE_LOCK skyscrapers)
