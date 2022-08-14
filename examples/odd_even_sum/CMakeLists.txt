add_executable(odd_even_sum odd_even_sum.cc)
target_link_libraries(odd_even_sum PUBLIC glasgow_constraint_solver)

find_package(Boost 1.74 COMPONENTS program_options REQUIRED)
include_directories(${Boost_INCLUDE_DIR})
target_link_libraries(odd_even_sum LINK_PUBLIC ${Boost_LIBRARIES})

add_test(NAME odd_even_sum COMMAND ${CMAKE_SOURCE_DIR}/run_test_and_verify.bash $<TARGET_FILE:odd_even_sum>)
